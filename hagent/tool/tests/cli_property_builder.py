#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cli_property_builder.py
-----------------------
Command-line interface to run PropertyBuilder with LLM configuration.

Supports:
  - Spec Markdown + CSV (per module)
  - Optional design_top override for clock/reset detection
"""

import os
import argparse

from hagent.tool.property_builder import PropertyBuilder


def main():
    parser = argparse.ArgumentParser(description='CLI for SVA property generation using LLM.')
    parser.add_argument('--spec-md', required=True, help='Path to Markdown spec (e.g. load_unit_spec.md)')
    parser.add_argument('--csv', required=True, help='Path to CSV spec (e.g. load_unit_spec.csv)')
    parser.add_argument('--rtl', required=True, help='RTL directory')
    parser.add_argument('--out', required=True, help='Output directory')
    parser.add_argument('--llm-conf', required=True, help='YAML LLM configuration file')
    parser.add_argument(
        '--design-top',
        help='Optional design top module name used to detect clock/reset. '
             'If omitted, clk/rst are detected from the module inferred '
             'from --spec-md (<name>_spec.* -> <name>).',
    )
    args = parser.parse_args()

    # Basic path checks
    for path in [args.spec_md, args.csv, args.llm_conf]:
        if not os.path.exists(path):
            raise FileNotFoundError(f'Required file not found: {path}')

    if not os.path.isdir(args.rtl):
        raise NotADirectoryError(f'RTL directory not found: {args.rtl}')

    builder = PropertyBuilder(
        spec_md=args.spec_md,
        csv_path=args.csv,
        rtl_dir=args.rtl,
        out_dir=args.out,
        llm_conf=args.llm_conf,
        design_top=args.design_top,
    )

    out = builder.generate_properties()
    if out:
        print(f'[✅] Property generation complete: {out}')
    else:
        print('[❌] Property generation failed.')


if __name__ == '__main__':
    main()

