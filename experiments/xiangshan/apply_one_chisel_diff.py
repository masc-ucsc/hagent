#!/usr/bin/env python3
"""
Apply one chisel_diff mutation in a fresh Docker-based workspace.

Steps:
  1. Create a temp directory and run setup_mcp.sh xiangshan to copy the Docker image into it
  2. Compile clean Chisel (debug build) to produce the correct baseline RTL
  3. Snapshot the clean RTL baseline (build_dbg/rtl)
  4. Apply the mutation to the Scala source
  5. Compile again with the mutation
  6. Find changed .sv files vs baseline and generate verilog_diffs
  7. Revert the Scala source
  8. Save results back into the mutation YAML
  9. Delete the temp directory completely

Usage:
    cd ~/hagent
    uv run python experiments/xiangshan/apply_one_chisel_diff.py \
        experiments/xiangshan/chisel_diffs_B/mutation_f0_m0_diffs.yaml
"""

import argparse
import difflib
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

import yaml
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString


# ── YAML helpers ─────────────────────────────────────────────────────────────
def _make_literal(obj):
    """Recursively convert multiline strings to LiteralScalarString so ruamel.yaml uses block style."""
    if isinstance(obj, dict):
        return {k: _make_literal(v) for k, v in obj.items()}
    if isinstance(obj, list):
        return [_make_literal(v) for v in obj]
    if isinstance(obj, str) and "\n" in obj:
        return LiteralScalarString(obj)
    return obj


def yaml_dump(obj) -> str:
    ry = YAML()
    ry.default_flow_style = False
    ry.width = 120
    ry.allow_unicode = True
    import io
    buf = io.StringIO()
    ry.dump(_make_literal(obj), buf)
    return buf.getvalue()


def yaml_load(text: str):
    return yaml.safe_load(text)


# ── RTL helpers ───────────────────────────────────────────────────────────────
def snapshot_rtl(rtl_dir: Path) -> dict:
    """Read all .sv files in rtl_dir into a dict {filename: content}."""
    return {f.name: f.read_text(errors="replace") for f in sorted(rtl_dir.glob("*.sv"))}


def find_changed_sv(rtl_dir: Path, baseline: dict) -> list:
    """Return list of (Path, old_content, new_content) for changed .sv files."""
    changed = []
    for f in sorted(rtl_dir.glob("*.sv")):
        old = baseline.get(f.name, "")
        new = f.read_text(errors="replace")
        if old != new:
            changed.append((f, old, new))
    return changed


def make_unified_diff(old: str, new: str, filename: str, n: int = 3) -> str:
    diff = "".join(
        difflib.unified_diff(
            old.splitlines(keepends=True),
            new.splitlines(keepends=True),
            fromfile=f"a/{filename}",
            tofile=f"b/{filename}",
            n=n,
        )
    )
    return "\n".join(line.rstrip() for line in diff.splitlines()).rstrip() + "\n"


# ── Compile ───────────────────────────────────────────────────────────────────
def compile_xiangshan(hagent_root: Path, env: dict) -> bool:
    """Run the debug compile via mcp_build.py with the given environment."""
    cmd = [
        "uv", "run", "--python", "3.13",
        "python", str(hagent_root / "hagent/mcp/mcp_build.py"),
        "--name", "xiangshan_rtl_dbg",
        "--api", "compile",
    ]
    print(f"  Running: {' '.join(cmd)}")
    result = subprocess.run(cmd, cwd=str(hagent_root), env=env)
    return result.returncode == 0


# ── Main ──────────────────────────────────────────────────────────────────────
def main():
    parser = argparse.ArgumentParser(description="Apply one chisel diff and collect verilog_diffs")
    parser.add_argument("mutation_yaml", help="Path to mutation_f*_m*_diffs.yaml")
    parser.add_argument("--output-dir", default=None, help="Directory to save result YAML (default: verilog_diffs_B/ next to input)")
    args = parser.parse_args()

    mutation_path = Path(args.mutation_yaml).resolve()
    if not mutation_path.exists():
        print(f"ERROR: file not found: {mutation_path}", file=sys.stderr)
        sys.exit(1)

    hagent_root = Path(os.environ.get("HAGENT_ROOT", Path.home() / "hagent"))
    setup_script = hagent_root / "scripts" / "setup_mcp.sh"

    # ── Load mutation YAML ────────────────────────────────────────────────────
    mutation = yaml_load(mutation_path.read_text())
    scala_rel = mutation["scala_file"]   # e.g. "src/main/scala/.../Alu.scala"
    orig_code = mutation["original_code"]
    mut_code  = mutation["mutated_code"]

    print(f"Mutation YAML : {mutation_path.name}")
    print(f"Scala file    : {scala_rel}")
    print(f"Mutation type : {mutation['mutation_type']}")
    print()

    # ── Step 1: create temp dir and run setup_mcp.sh ─────────────────────────
    tmp_dir = Path(tempfile.mkdtemp(prefix="xiangshan_mut_"))
    print(f"Step 1: Setting up fresh workspace in {tmp_dir} ...")
    try:
        result = subprocess.run(
            ["bash", str(setup_script), "xiangshan", str(tmp_dir)],
            cwd=str(hagent_root),
        )
        if result.returncode != 0:
            print("ERROR: setup_mcp.sh failed", file=sys.stderr)
            sys.exit(1)
        print("  Workspace ready")
        print()

        # Paths inside the temp workspace
        repo_dir = tmp_dir / "repo"
        build_dir = tmp_dir / "build"
        cache_dir = tmp_dir / "cache"
        rtl_dir   = build_dir / "build_dbg" / "rtl"

        # Build environment for compile calls
        env = os.environ.copy()
        env["HAGENT_ROOT"]      = str(hagent_root)
        env["HAGENT_DOCKER"]    = "mascucsc/hagent-xiangshan:2025.12"
        env["HAGENT_REPO_DIR"]  = str(repo_dir)
        env["HAGENT_BUILD_DIR"] = str(build_dir)
        env["HAGENT_CACHE_DIR"] = str(cache_dir)
        env["UV_PROJECT"]       = str(hagent_root)

        scala_path = repo_dir / scala_rel
        if not scala_path.exists():
            print(f"ERROR: Scala file not found: {scala_path}", file=sys.stderr)
            sys.exit(1)

        # ── Step 2: baseline compile ──────────────────────────────────────────
        print("Step 2: Compiling clean Chisel (baseline)...")
        if not compile_xiangshan(hagent_root, env):
            print("ERROR: Baseline compile failed.", file=sys.stderr)
            sys.exit(1)
        print("  Baseline compile OK")
        print()

        if not rtl_dir.exists():
            print(f"ERROR: RTL dir not found after baseline compile: {rtl_dir}", file=sys.stderr)
            sys.exit(1)

        # ── Step 3: snapshot baseline RTL ────────────────────────────────────
        print("Step 3: Snapshotting baseline RTL...")
        baseline = snapshot_rtl(rtl_dir)
        print(f"  {len(baseline)} .sv files snapshotted")
        print()

        # ── Step 4: apply mutation ────────────────────────────────────────────
        original_chisel = scala_path.read_text()
        if orig_code not in original_chisel:
            print(f"ERROR: original_code not found in {scala_path.name}", file=sys.stderr)
            sys.exit(1)

        scala_path.write_text(original_chisel.replace(orig_code, mut_code, 1))
        print(f"Step 4: Applied mutation to {scala_path.name}")
        print()

        # ── Step 5: compile with mutation ────────────────────────────────────
        verilog_diffs = []
        sv_changed    = []
        status        = "compile_failed"

        try:
            print("Step 5: Compiling with mutation (debug build)...")
            if not compile_xiangshan(hagent_root, env):
                print("  COMPILE FAILED")
            else:
                print("  Compile OK")
                print()

                # ── Step 6: collect verilog_diffs ────────────────────────────
                changed   = find_changed_sv(rtl_dir, baseline)
                sv_changed = [f.name for f, _, _ in changed]
                print(f"Step 6: Changed .sv files ({len(changed)}): {sv_changed}")

                if len(changed) == 0:
                    status = "no_rtl_change"
                    print("  No RTL change detected.")
                else:
                    status = "success"
                    for f, old, new in changed:
                        diff = make_unified_diff(old, new, f.name)
                        verilog_diffs.append({"file": f.name, "verilog_diff": diff})
                        print(f"  Generated verilog_diff for {f.name}")

        finally:
            # ── Step 7: revert Scala source ──────────────────────────────────
            scala_path.write_text(original_chisel)
            print()
            print(f"Step 7: Reverted {scala_path.name}")

    finally:
        # ── Step 9: delete temp directory ────────────────────────────────────
        print()
        print(f"Step 9: Deleting temp workspace {tmp_dir} ...")
        shutil.rmtree(tmp_dir, ignore_errors=True)
        print("  Done")

    # ── Step 8: save results to verilog_diffs_B/ ─────────────────────────────
    mutation["status"]        = status
    mutation["sv_changed"]    = sv_changed
    mutation["verilog_diffs"] = verilog_diffs

    out_dir = Path(args.output_dir) if args.output_dir else mutation_path.parent / "verilog_diffs_B"
    os.makedirs(out_dir, exist_ok=True)
    out_path = out_dir / mutation_path.name

    content = yaml_dump(mutation)
    out_path.write_text(content)

    if out_path.stat().st_size == 0:
        print(f"WARNING: output file is empty: {out_path}", file=sys.stderr)
    else:
        print()
        print(f"Results saved to {out_path}")
        print(f"  status       : {status}")
        print(f"  sv_changed   : {sv_changed}")
        print(f"  verilog_diffs: {len(verilog_diffs)} file(s)")
        print(f"  file size    : {out_path.stat().st_size} bytes")


if __name__ == "__main__":
    main()
