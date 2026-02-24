#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import argparse
from hagent.tool.property_builder import PropertyBuilder


def main():
    parser = argparse.ArgumentParser(description='CLI for SVA property generation using LLM.')
    parser.add_argument('--spec-md', required=True, help='Path to Markdown spec (e.g. load_unit_spec.md)')
    parser.add_argument('--csv', required=True, help='Path to CSV spec (e.g. load_unit_spec.csv)')
    parser.add_argument('--rtl', required=True, help='RTL directory')
    parser.add_argument('--dir', required=True, help='Output directory')
    parser.add_argument('--llm-config', required=True, help='YAML LLM configuration file')
    parser.add_argument(
        '--design-top',
        help='Optional design top module name used to detect clock/reset. '
        'If omitted, clk/rst are detected from the module inferred '
        'from --spec-md (<name>_spec.* -> <name>).',
    )
    parser.add_argument('--debug', action='store_true', help='Enable debug output')
    parser.add_argument('--whitebox', action='store_true', help='Whitebox mode: allow internal signals in properties.')
    parser.add_argument('--internal-signals-json', default=None, help='Path to internal_signals.json.')
    args = parser.parse_args()

    # Basic path checks
    for path in [args.spec_md, args.csv, args.llm_config]:
        if not os.path.exists(path):
            raise FileNotFoundError(f'Required file not found: {path}')

    if not os.path.isdir(args.rtl):
        raise NotADirectoryError(f'RTL directory not found: {args.rtl}')

    builder = PropertyBuilder(
        spec_md=args.spec_md,
        csv_path=args.csv,
        rtl_dir=args.rtl,
        out_dir=args.dir,
        llm_conf=args.llm_config,
        design_top=args.design_top,
        whitebox=getattr(args, 'whitebox', False),
        internal_signals_json=getattr(args, 'internal_signals_json', None),
    )

    out = builder.generate_properties()
    if out:
        print(f'[✅] Property generation complete: {out}')
    else:
        print('[❌] Property generation failed.')


if __name__ == '__main__':
    main()
