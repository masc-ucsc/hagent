#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import argparse
from hagent.tool.property_builder import PropertyBuilder


def main():
    parser = argparse.ArgumentParser(description='CLI for SVA property generation.')
    parser.add_argument('--spec-md', required=True)
    parser.add_argument('--csv', required=True)
    parser.add_argument('--rtl', required=True)
    parser.add_argument('--out', required=True)
    parser.add_argument('--llm-conf', required=False, default=None)
    parser.add_argument('--design-top', required=False, default=None)
    args = parser.parse_args()

    for path in [args.spec_md, args.csv]:
        if not os.path.exists(path):
            raise FileNotFoundError(f'Required file not found: {path}')

    if args.llm_conf and not os.path.exists(args.llm_conf):
        raise FileNotFoundError(f'LLM config not found: {args.llm_conf}')

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
