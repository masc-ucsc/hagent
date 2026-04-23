#!/usr/bin/env python3
"""
Convert a mutation result YAML (from apply_one_chisel_diff.py) into
a v2chisel_batch input YAML.

Usage:
    uv run python experiments/xiangshan/make_v2chisel_input.py \
        experiments/xiangshan/xiangshan/chisel_diffs_B/verilog_diffs_B/mutation_f0_m0_diffs.yaml \
        -o experiments/xiangshan/test_input_B.yaml
"""

import argparse
import sys
from pathlib import Path

from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("mutation_yaml", help="Path to mutation result YAML with verilog_diffs")
    parser.add_argument("-o", "--output", default=None, help="Output YAML path")
    args = parser.parse_args()

    ry = YAML()
    mutation_path = Path(args.mutation_yaml).resolve()
    mutation = ry.load(mutation_path.read_text())

    verilog_diffs = mutation.get("verilog_diffs", [])
    if not verilog_diffs:
        print(f"ERROR: no verilog_diffs in {mutation_path.name}", file=sys.stderr)
        sys.exit(1)

    chisel_diff = mutation.get("chisel_diff", "")

    # All verilog_diffs come from one chisel_diff — combine into a single bug entry
    combined_diff = "\n".join(
        str(entry.get("verilog_diff", entry.get("unified_diff", "")))
        for entry in verilog_diffs
    )
    files = [entry["file"] for entry in verilog_diffs]
    bugs = [{"file": files[0], "unified_diff": LiteralScalarString(combined_diff)}]

    out = {
        "v2chisel_batch": {
            "llm": {
                "model": "openai/gpt-5-codex",
            }
        },
        "docker_container": "hagent",
        "docker_patterns": ["/code/XiangShan/src/main/scala"],
        "chisel_patterns": ["/home/farzaneh/hagent/xiangShan/repo/src/main/scala/**/*.scala"],
        "bugs": bugs,
    }
    if chisel_diff:
        out["chisel_diff"] = LiteralScalarString(str(chisel_diff))

    out_path = Path(args.output) if args.output else mutation_path.parent / f"test_input_{mutation_path.stem}.yaml"

    ry2 = YAML()
    ry2.default_flow_style = False
    ry2.width = 120
    with open(out_path, "w") as f:
        ry2.dump(out, f)

    print(f"Written : {out_path}")
    print(f"  bugs  : 1 combined entry covering {len(verilog_diffs)} files ({', '.join(files)})")
    print()
    print(f"Run with:")
    print(f"  uv run python hagent/step/v2chisel_batch/v2chisel_batch.py {out_path} -o out.yaml")


if __name__ == "__main__":
    main()
