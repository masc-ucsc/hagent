#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cli_spec_builder.py
-------------------
Command-line wrapper around hagent.tool.spec_builder.SpecBuilder.

Features:
  - Uses Slang to extract AST.
  - Generates Markdown + CSV specs via LLM (mandatory).
  - Supports single or multi-top execution.
  - Optional YAML config to preload arguments.
"""

from __future__ import annotations
import os
import glob
import yaml
import argparse
from pathlib import Path
from typing import Any, Dict, List

from hagent.tool.spec_builder import SpecBuilder

SV_EXTS = (".sv", ".v", ".svh", ".vh")


# ──────────────────────────────────────────────────────────────────────────────
# Utilities
# ──────────────────────────────────────────────────────────────────────────────
def is_valid_rtl(path: str) -> bool:
    """Accept .sv/.v files except *_pkg.sv or *_tb.sv."""
    return path.endswith(SV_EXTS) and not any(
        path.endswith(s) for s in ["_pkg.sv", "_tb.sv"]
    )


def list_candidate_tops(rtl_root: str) -> List[str]:
    """Return unique module-name candidates based on filenames."""
    files = [
        f
        for f in glob.glob(os.path.join(rtl_root, "**"), recursive=True)
        if is_valid_rtl(f)
    ]
    return sorted(set(Path(f).stem for f in files))


def merge_config(args: argparse.Namespace, config_file: str | None) -> argparse.Namespace:
    """Merge defaults from YAML config into CLI args (non-destructively)."""
    if not config_file:
        return args
    path = Path(config_file).expanduser()
    if not path.exists():
        print(f"[WARN] Config file not found: {path}")
        return args

    with path.open() as fh:
        cfg = yaml.safe_load(fh) or {}

    for k, v in cfg.items():
        if hasattr(args, k) and getattr(args, k) in (None, "", [], False):
            setattr(args, k, v)
    return args


def _sanitize_incdirs(dirs: List[str]) -> List[str]:
    """Expand and verify include directories."""
    out: List[str] = []
    for d in dirs or []:
        dd = os.path.expanduser(d)
        if os.path.isdir(dd):
            out.append(dd)
        else:
            print(f"[WARN] Include directory does not exist: {d}")
    return out


# ──────────────────────────────────────────────────────────────────────────────
# Core runner
# ──────────────────────────────────────────────────────────────────────────────
def _run_one_top(args: argparse.Namespace, top: str) -> Dict[str, Any]:
    """Run SpecBuilder for a single top."""
    out_dir = Path(args.out).expanduser()
    out_dir.mkdir(parents=True, exist_ok=True)

    builder = SpecBuilder(
        slang_bin=Path(args.slang).resolve(),
        rtl_dir=Path(args.rtl).resolve(),
        top=top,
        out_dir=out_dir,
        llm_conf=Path(args.llm_conf).resolve(),
        include_dirs=[Path(i).resolve() for i in (args.include or [])],
        defines=args.defines or [],
        disable_analysis=not args.no_disable_analysis,
    )

    print(f"\n[⚙️] Building spec for top module: {top}")
    try:
        builder.run()
        return {"ok": True, "top": top}
    except SystemExit as se:
        return {"ok": False, "top": top, "error": str(se)}
    except Exception as e:
        return {"ok": False, "top": top, "error": str(e)}


def run_single(args: argparse.Namespace) -> int:
    """Run spec build for a single top module."""
    if not args.top:
        print("[❌] --top is required in single mode")
        return 2
    res = _run_one_top(args, args.top)
    print(res)
    return 0 if res.get("ok") else 2


def run_multi(args: argparse.Namespace) -> int:
    """Run spec build for all discovered top modules."""
    tops = list_candidate_tops(args.rtl)
    if not tops:
        print(f"[❌] No RTL tops found in: {args.rtl}")
        return 2

    print(f"[INFO] Found {len(tops)} candidate tops.")
    failures = 0
    for top in tops:
        res = _run_one_top(args, top)
        print(res)
        if not res.get("ok"):
            failures += 1

    if failures:
        print(f"[❌] {failures} top(s) failed.")
        return 2

    print("[✅] All tops completed successfully.")
    return 0


# ──────────────────────────────────────────────────────────────────────────────
# CLI Entrypoint
# ──────────────────────────────────────────────────────────────────────────────
def main() -> int:
    parser = argparse.ArgumentParser(
        description="CLI wrapper around SpecBuilder (LLM-driven RTL spec generator)"
    )
    parser.add_argument(
        "--mode",
        choices=["single", "multi"],
        default="single",
        help="Single top or multi-top mode",
    )
    parser.add_argument("--slang", required=True, help="Path to slang binary")
    parser.add_argument("--rtl", required=True, help="Path to RTL directory")
    parser.add_argument("--top", help="Top module name (required for single mode)")
    parser.add_argument(
        "--include", "-I", nargs="*", default=[], help="Include directories"
    )
    parser.add_argument(
        "--defines",
        "-D",
        nargs="*",
        default=[],
        help="Defines to pass to Slang (e.g., FOO=1)",
    )
    parser.add_argument(
        "--out", default="out_spec", help="Output directory for spec artifacts"
    )
    parser.add_argument(
        "--llm-conf",
        required=True,
        help="YAML config for LLM (spec_prompt.yaml)",
    )
    parser.add_argument(
        "--no-disable-analysis",
        action="store_true",
        help="Enable full analysis in Slang",
    )
    parser.add_argument(
        "-f",
        "--config-file",
        dest="config_file",
        help="YAML config file with default arguments",
    )

    args = parser.parse_args()
    args = merge_config(args, args.config_file)

    # Path sanity
    args.rtl = os.path.expanduser(args.rtl)
    args.include = _sanitize_incdirs(args.include)
    args.llm_conf = os.path.expanduser(args.llm_conf)

    if not os.path.isfile(args.slang):
        print(f"[❌] slang not found: {args.slang}")
        return 2
    if not os.path.isdir(args.rtl):
        print(f"[❌] RTL directory not found: {args.rtl}")
        return 2

    if args.mode == "single":
        return run_single(args)
    else:
        return run_multi(args)


if __name__ == "__main__":
    raise SystemExit(main())

