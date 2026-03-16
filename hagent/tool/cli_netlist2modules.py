#!/usr/bin/env python3

import argparse
import os
import sys

from hagent.tool.netlist2modules import Netlist2Modules


def build_parser():
    parser = argparse.ArgumentParser(
        description='Partition a flat netlist into pipeline-stage submodules.',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""\
examples:
  # Partition an elaborated netlist, one file per module
  uv run python ./hagent/tool/cli_netlist2modules.py ./tmp/elab.v --output-dir out

  # Partition with hierarchy + flatten, specifying the top module
  uv run python ./hagent/tool/cli_netlist2modules.py design.sv --output-dir out --top MyCore

  # Write all modules to a single Verilog file
  uv run python ./hagent/tool/cli_netlist2modules.py ./tmp/elab.v --output-file combined.v

  # Show yosys internal log output for debugging
  uv run python ./hagent/tool/cli_netlist2modules.py design.v --output-dir partitions -v
""",
    )
    parser.add_argument('input', help='Input Verilog/SystemVerilog netlist file')
    output_group = parser.add_mutually_exclusive_group(required=True)
    output_group.add_argument('--output-dir', help='Output directory (one file per module)')
    output_group.add_argument('--output-file', help='Output file (all modules in one file)')
    parser.add_argument(
        '--top',
        default=None,
        help='Top module name. If set, runs hierarchy -top and flatten before processing',
    )
    parser.add_argument('-v', '--verbose', action='store_true', help='Show yosys log output')
    return parser


def main():
    parser = build_parser()
    args = parser.parse_args()

    if not os.path.isfile(args.input):
        print(f'Error: input file not found: {args.input}', file=sys.stderr)
        sys.exit(1)

    tool = Netlist2Modules(
        input_path=args.input,
        top=args.top,
        verbose=args.verbose,
    )
    result = tool.run(output_dir=args.output_dir, output_file=args.output_file)
    print(result.format_summary())


if __name__ == '__main__':
    main()
