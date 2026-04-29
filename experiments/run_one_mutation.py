#!/usr/bin/env python3
"""
Apply one mutation, compile, collect verilog_diffs, save to YAML.
Usage: python3 run_one_mutation.py <file_idx> <mutation_idx>
  file_idx:     0 = wrapper/Alu.scala, 1 = fu/Alu.scala, 2 = Multiplier.scala
  mutation_idx: index within that file's mutation list
"""

import sys
import json
import difflib
import subprocess
import os
import yaml
from pathlib import Path


def str_presenter(dumper, data):
    if "\n" in data:
        return dumper.represent_scalar("tag:yaml.org,2002:str", data, style="|")
    return dumper.represent_scalar("tag:yaml.org,2002:str", data)


yaml.add_representer(str, str_presenter)

# ── Config ────────────────────────────────────────────────────────────────────
MUTATIONS_JSON = Path("/soe/frabieik/firefly/mutations.json")
RTL_DIR        = Path("/soe/frabieik/hagent/xiangShan/build/build_opt/rtl")
RTL_BASELINE   = Path("/soe/frabieik/hagent/xiangShan/build/rtl_baseline_backup")
HAGENT_ROOT    = Path("/soe/frabieik/hagent")
MCP_BUILD      = HAGENT_ROOT / "hagent/mcp/mcp_build.py"


# ── Helpers ───────────────────────────────────────────────────────────────────
def make_diff(old, new, filename, n=3):
    diff = "".join(difflib.unified_diff(
        old.splitlines(keepends=True),
        new.splitlines(keepends=True),
        fromfile=f"a/{filename}",
        tofile=f"b/{filename}",
        n=n
    ))
    return "\n".join(line.rstrip() for line in diff.splitlines()).rstrip() + "\n"


def compile_xiangshan():
    env = os.environ.copy()
    env["HAGENT_DOCKER"]    = "mascucsc/hagent-xiangshan:2025.12"
    env["HAGENT_REPO_DIR"]  = "/soe/frabieik/hagent/xiangShan/repo"
    env["HAGENT_BUILD_DIR"] = "/soe/frabieik/hagent/xiangShan/build"
    env["UV_PROJECT"]       = str(HAGENT_ROOT)

    result = subprocess.run(
        ["uv", "run", "--python", "3.13", "python", str(MCP_BUILD),
         "--name", "xiangshan_rtl_opt", "--api", "compile"],
        env=env, cwd=str(HAGENT_ROOT),
        capture_output=True, text=True, timeout=900
    )
    return result.returncode == 0


def find_changed_sv():
    changed = []
    for f in RTL_DIR.glob("*.sv"):
        old_f = RTL_BASELINE / f.name
        if not old_f.exists():
            continue
        old = old_f.read_text(errors="replace")
        new = f.read_text(errors="replace")
        if old != new:
            changed.append((f, old, new))
    return changed


# ── Main ──────────────────────────────────────────────────────────────────────
def main():
    if len(sys.argv) != 3:
        print("Usage: python3 run_one_mutation.py <file_idx> <mutation_idx>")
        print("  file_idx:     0=wrapper/Alu.scala  1=fu/Alu.scala  2=Multiplier.scala")
        sys.exit(1)

    file_idx     = int(sys.argv[1])
    mutation_idx = int(sys.argv[2])

    mutations  = json.loads(MUTATIONS_JSON.read_text())
    file_keys  = list(mutations.keys())
    scala_path = Path(file_keys[file_idx].replace(
        "/home/farzaneh/hagent/xiangShan",
        "/soe/frabieik/hagent/xiangShan"
    ))
    mutation = mutations[file_keys[file_idx]][mutation_idx]

    print(f"\n{'='*60}")
    print(f"File:         {scala_path.relative_to('/soe/frabieik/hagent/xiangShan/repo')}")
    print(f"Mutation:     [{mutation_idx}] {mutation['mutation_type']}")
    print(f"Original:     {mutation['original_code']!r}")
    print(f"Mutated:      {mutation['mutated_code']!r}")
    print(f"{'='*60}\n")

    # Read original
    original_chisel = scala_path.read_text()
    if mutation["original_code"] not in original_chisel:
        print("❌ original_code not found in Chisel file — aborting")
        sys.exit(1)

    # Generate chisel_diff
    mutated_chisel = original_chisel.replace(mutation["original_code"], mutation["mutated_code"], 1)
    rel_path       = scala_path.relative_to("/soe/frabieik/hagent/xiangShan/repo")
    chisel_diff    = make_diff(original_chisel, mutated_chisel, str(rel_path))

    # Apply mutation
    scala_path.write_text(mutated_chisel)

    # Confirm application
    content = scala_path.read_text()
    if mutation["mutated_code"] in content:
        print(f"✅ Mutation applied: {mutation['mutated_code']!r}")
    else:
        print("❌ Mutation apply failed — aborting")
        scala_path.write_text(original_chisel)
        sys.exit(1)

    try:
        # Compile
        print("\n🔨 Compiling XiangShan (~5-6 min)...")
        ok = compile_xiangshan()
        if not ok:
            print("❌ Compile FAILED")
            sys.exit(1)
        print("✅ Compile succeeded")

        # Find diffs
        changed = find_changed_sv()
        print(f"\n🔍 Changed .sv files ({len(changed)}):")
        for f, _, _ in changed:
            print(f"   {f.name}")

        if len(changed) == 0:
            print("⚠️  No RTL change — mutation had no effect")
            sys.exit(0)

        # Build verilog_diffs
        verilog_diffs = []
        for f, old, new in changed:
            diff = make_diff(old, new, f.name)
            verilog_diffs.append({"filename": f.name, "verilog_diff": diff})

    finally:
        # Always revert
        scala_path.write_text(original_chisel)
        print("\n⏪ Chisel file reverted")

    # Save YAML
    output = HAGENT_ROOT / f"mutation_f{file_idx}_m{mutation_idx}_diffs.yaml"
    result = {
        "file_idx":       file_idx,
        "mutation_idx":   mutation_idx,
        "scala_file":     str(rel_path),
        "mutation_type":  mutation["mutation_type"],
        "original_code":  mutation["original_code"],
        "mutated_code":   mutation["mutated_code"],
        "chisel_diff":    chisel_diff,
        "sv_changed":     [f.name for f, _, _ in changed],
        "verilog_diffs":  verilog_diffs,
    }
    output.write_text(yaml.dump(result, allow_unicode=True, sort_keys=False, width=120))
    print(f"\n✅ Saved to {output}")


if __name__ == "__main__":
    main()
