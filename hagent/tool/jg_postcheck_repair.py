#!/usr/bin/env python3
# -*- coding: utf-8 -*-

from __future__ import annotations

import os
import sys
import csv
import shutil
import subprocess
from pathlib import Path
from typing import Dict, List, Optional, Tuple

try:
    from hagent.core.llm_wrap import LLM_wrap
except Exception:
    LLM_wrap = None


def _tail_text(p: Path, n_lines: int = 250) -> str:
    if not p.exists():
        return f"<missing: {p}>"
    try:
        lines = p.read_text(errors="ignore").splitlines()
        return "\n".join(lines[-n_lines:])
    except Exception as e:
        return f"<failed to read {p}: {e}>"


def _read_text(p: Path, max_bytes: int = 250_000) -> str:
    if not p.exists():
        return f"<missing: {p}>"
    try:
        b = p.read_bytes()
        if len(b) > max_bytes:
            b = b[-max_bytes:]
        return b.decode("utf-8", errors="ignore")
    except Exception as e:
        return f"<failed to read {p}: {e}>"


def _read_results_summary(p: Path) -> Dict[str, int]:
    out: Dict[str, int] = {}
    if not p.exists():
        return out
    with p.open("r", encoding="utf-8", errors="ignore") as f:
        r = csv.DictReader(f)
        for row in r:
            k = (row.get("status") or "").strip()
            v = (row.get("count") or "0").strip()
            try:
                out[k] = int(v)
            except Exception:
                out[k] = 0
    return out


def _needs_repair(counts: Dict[str, int]) -> Tuple[bool, str]:
    fail = counts.get("FAIL", 0)
    unk = counts.get("UNKNOWN", 0)
    cov = counts.get("COVER", 0)
    unr = counts.get("UNREACHABLE", 0)

    if fail > 0:
        return True, f"FAIL={fail}"
    if unk > 0:
        return True, f"UNKNOWN={unk}"
    # Common “environment too weak / no stimulus” symptom
    if cov == 0 and unr > 0:
        return True, f"COVER={cov},UNREACHABLE={unr}"
    return False, "no fail/unknown/unreachable-stimulus condition"


def _collect_files(fpv_dir: Path, sva_top: str) -> List[Path]:
    cands = [
        fpv_dir / "FPV.tcl",
        fpv_dir / "files.vc",
        fpv_dir / "jg.stderr.log",
        fpv_dir / "jg.stdout.log",
        fpv_dir / "jgproject" / "jg.log",
        fpv_dir / "results_summary.csv",
        fpv_dir / "formal_coverage_summary.txt",
        fpv_dir / "sva" / "properties.sv",
        fpv_dir / "sva" / f"{sva_top}_prop.sv",
        fpv_dir / "sva" / f"{sva_top}_bind.sv",
    ]
    out: List[Path] = []
    seen = set()
    for p in cands:
        if p in seen:
            continue
        seen.add(p)
        if p.exists():
            out.append(p)
    return out


def _files_blob(paths: List[Path]) -> str:
    parts: List[str] = []
    for p in paths:
        parts.append(f"=== FILE: {p} ===")
        parts.append(_read_text(p))
        parts.append("")
    return "\n".join(parts)


def _backup_tree(fpv_dir: Path) -> Path:
    bdir = fpv_dir / "backup_before_post_repair"
    if bdir.exists():
        shutil.rmtree(bdir)
    bdir.mkdir(parents=True, exist_ok=True)

    for rel in ["FPV.tcl", "files.vc", "results_summary.csv", "jg.stderr.log", "jg.stdout.log", "jgproject", "sva"]:
        src = fpv_dir / rel
        if src.exists():
            dst = bdir / rel
            if src.is_dir():
                shutil.copytree(src, dst)
            else:
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copy2(src, dst)
    return bdir


def _apply_patch(patch_text: str, patch_path: Path) -> bool:
    patch_path.write_text(patch_text, encoding="utf-8")
    try:
        subprocess.run(
            ["patch", "-p0", "-i", str(patch_path)],
            cwd=Path("/"),
            check=True,
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
        return True
    except Exception:
        return False


def _run_jasper(fpv_dir: Path, jasper_bin: str) -> bool:
    cmd = [jasper_bin, "-allow_unsupported_OS", "-tcl", "FPV.tcl", "-batch"]
    jg_stdout = fpv_dir / "jg.stdout.log"
    jg_stderr = fpv_dir / "jg.stderr.log"
    try:
        with open(jg_stdout, "w") as fo, open(jg_stderr, "w") as fe:
            subprocess.run(cmd, cwd=fpv_dir, stdout=fo, stderr=fe, check=True)
        return True
    except subprocess.CalledProcessError:
        return False


def run_postcheck_repair(
    fpv_dir: Path,
    sva_top: str,
    scope_path: str,
    llm_conf: Path,
    apply: bool = False,
    rerun_jg: bool = False,
    jasper_bin: str = "jg",
    max_iters: int = 1,
    tail_lines: int = 250,
    also_read_csv_spec: bool = True,
) -> int:
    fpv_dir = fpv_dir.resolve()
    counts = _read_results_summary(fpv_dir / "results_summary.csv")
    need, reason = _needs_repair(counts)

    if not need:
        print(f"[POSTCHECK] No repair needed ({reason}).")
        return 0

    if LLM_wrap is None:
        print("[POSTCHECK] LLM_wrap not available. Cannot repair.")
        return 2
    if not llm_conf.exists():
        print(f"[POSTCHECK] Missing llm conf: {llm_conf}")
        return 2

    # Optional: include spec CSV if present (helps environment assumptions)
    spec_csv = fpv_dir / f"{sva_top}_spec.csv"
    extra_paths: List[Path] = []
    if also_read_csv_spec and spec_csv.exists():
        extra_paths.append(spec_csv)

    for it in range(max_iters):
        print(f"[POSTCHECK] Repair iteration {it+1}/{max_iters} due to {reason}")

        files = _collect_files(fpv_dir, sva_top) + extra_paths
        blob = _files_blob(files)

        payload = {
            "sva_top": sva_top,
            "scope_path": scope_path or "-",
            "results_summary": _read_text(fpv_dir / "results_summary.csv"),
            "jg_stderr_tail": _tail_text(fpv_dir / "jg.stderr.log", tail_lines),
            "jg_stdout_tail": _tail_text(fpv_dir / "jg.stdout.log", tail_lines),
            "jg_log_tail": _tail_text(fpv_dir / "jgproject" / "jg.log", tail_lines),
            "coverage_summary": _read_text(fpv_dir / "formal_coverage_summary.txt"),
            "files_blob": blob,
        }

        llm = LLM_wrap(
            name="default",
            conf_file=str(llm_conf),
            log_file=str(fpv_dir / "jg_post_repair_llm.log"),
        )

        try:
            res = llm.inference(payload, prompt_index="jg_post_repair_patch", n=1)
        except Exception as e:
            print(f"[POSTCHECK] LLM inference failed: {e}")
            return 2

        patch_text = ""
        if isinstance(res, list) and res:
            patch_text = res[0]
        elif isinstance(res, str):
            patch_text = res

        patch_text = (patch_text or "").strip()
        patch_path = fpv_dir / "jg_post_repair.patch"
        patch_path.write_text(patch_text + "\n", encoding="utf-8")

        if not patch_text.startswith("--- "):
            print("[POSTCHECK] LLM did not output a unified diff. Wrote jg_post_repair.patch; not applying.")
            return 2

        if not apply:
            print("[POSTCHECK] Patch produced (not applied). See:", patch_path)
            return 0

        bdir = _backup_tree(fpv_dir)
        ok = _apply_patch(patch_text, patch_path)
        if not ok:
            print("[POSTCHECK] Patch apply failed. Backup at:", bdir)
            return 2

        print("[POSTCHECK] Patch applied. Backup at:", bdir)

        if rerun_jg:
            ok2 = _run_jasper(fpv_dir, jasper_bin)
            if ok2:
                print("[POSTCHECK] Jasper rerun succeeded after patch.")
                return 0
            else:
                print("[POSTCHECK] Jasper rerun still failing; continuing loop if iterations remain.")

        # re-check summary if it exists/was updated externally
        counts = _read_results_summary(fpv_dir / "results_summary.csv")
        need, reason = _needs_repair(counts)
        if not need:
            print("[POSTCHECK] Repair condition cleared.")
            return 0

    print("[POSTCHECK] Reached max_iters and still needs repair.")
    return 2


def main(argv: Optional[List[str]] = None) -> int:
    import argparse

    ap = argparse.ArgumentParser(description="Post-Jasper triage + optional LLM repair (environment-focused).")
    ap.add_argument("--fpv-dir", required=True, help="Path like .../out/fpv_<top>")
    ap.add_argument("--sva-top", required=True)
    ap.add_argument("--scope-path", default="")
    ap.add_argument("--llm-conf", required=True, help="jg_post_repair_prompt.yaml")
    ap.add_argument("--apply", action="store_true", help="Apply patch (otherwise just generate patch file).")
    ap.add_argument("--rerun-jg", action="store_true", help="Rerun Jasper after applying patch.")
    ap.add_argument("--jasper-bin", default="jg")
    ap.add_argument("--max-iters", type=int, default=1)
    ap.add_argument("--tail-lines", type=int, default=250)
    ap.add_argument("--no-csv", action="store_true", help="Do not include *_spec.csv in LLM context.")
    args = ap.parse_args(argv)

    return run_postcheck_repair(
        fpv_dir=Path(args.fpv_dir),
        sva_top=args.sva_top,
        scope_path=args.scope_path,
        llm_conf=Path(args.llm_conf),
        apply=args.apply,
        rerun_jg=args.rerun_jg,
        jasper_bin=args.jasper_bin,
        max_iters=args.max_iters,
        tail_lines=args.tail_lines,
        also_read_csv_spec=(not args.no_csv),
    )


if __name__ == "__main__":
    raise SystemExit(main())

