#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cli_spec_builder.py
-------------------
Command-line wrapper around hagent.tool.spec_builder.SpecBuilder.

Adds:
  - --scope-path (Slang --ast-json-scope)
  - --discover-scope-module (find instance hierarchy paths for a module name)
  - --discover-only (print paths and exit)
"""

from __future__ import annotations

import os
import glob
import yaml
import argparse
from pathlib import Path
from typing import Any, Dict, List, Optional

from hagent.tool.spec_builder import SpecBuilder

SV_EXTS = ('.sv', '.v', '.svh', '.vh')


def is_valid_rtl(path: str) -> bool:
    return path.endswith(SV_EXTS) and not any(path.endswith(s) for s in ['_pkg.sv', '_tb.sv'])


def list_candidate_tops(rtl_root: str) -> List[str]:
    files = [f for f in glob.glob(os.path.join(rtl_root, '**'), recursive=True) if is_valid_rtl(f)]
    return sorted(set(Path(f).stem for f in files))


def merge_config(args: argparse.Namespace, config_file: str | None) -> argparse.Namespace:
    if not config_file:
        return args
    path = Path(config_file).expanduser()
    if not path.exists():
        print(f'[WARN] Config file not found: {path}')
        return args

    with path.open() as fh:
        cfg = yaml.safe_load(fh) or {}

    for k, v in cfg.items():
        if hasattr(args, k) and getattr(args, k) in (None, '', [], False):
            setattr(args, k, v)
    return args


def _sanitize_incdirs(dirs: List[str]) -> List[str]:
    out: List[str] = []
    for d in dirs or []:
        dd = os.path.expanduser(d)
        if os.path.isdir(dd):
            out.append(dd)
        else:
            print(f'[WARN] Include directory does not exist: {d}')
    return out


def _flatten_str_lists(v: Any) -> List[str]:
    """Flatten argparse values that may be a list[str] or list[list[str]]."""
    if not v:
        return []
    if isinstance(v, list) and v and isinstance(v[0], list):
        out: List[str] = []
        for it in v:
            out.extend([x for x in (it or []) if x is not None])
        return out
    if isinstance(v, list):
        return [x for x in v if x is not None]
    return [str(v)]


def _resolve_filelist(path: Optional[str]) -> Optional[Path]:
    if not path:
        return None
    return Path(os.path.expanduser(path))


def _run_one_top(args: argparse.Namespace, top: str) -> Dict[str, Any]:
    """Run SpecBuilder for a single spec top."""
    out_dir = Path(args.dir).expanduser()
    out_dir.mkdir(parents=True, exist_ok=True)

    design_top = args.design_top or top
    filelist_path = _resolve_filelist(args.filelist)

    builder = SpecBuilder(
        slang_bin=Path(args.slang).resolve(),
        rtl_dir=Path(args.rtl).resolve(),
        top=top,
        design_top=design_top,
        out_dir=out_dir,
        llm_conf=Path(args.llm_config).resolve(),
        include_dirs=[Path(i).resolve() for i in _flatten_str_lists(args.include)],
        defines=_flatten_str_lists(args.defines),
        disable_analysis=not args.no_disable_analysis,
        filelist=filelist_path,
        scope_path=args.scope_path,
        discover_scope_module=args.discover_scope_module,
        discover_only=args.discover_only,
        whitebox=getattr(args, 'whitebox', False),
    )

    print(f'\n[⚙️] Building spec for top module: {top} (design_top={design_top})')
    if args.scope_path:
        print(f'[INFO] Using scope path: {args.scope_path}')
    if args.discover_scope_module:
        print(f'[INFO] Discovering scope paths for module: {args.discover_scope_module}')

    try:
        builder.run()
        return {'ok': True, 'top': top}
    except SystemExit as se:
        return {'ok': False, 'top': top, 'error': str(se)}
    except Exception as e:
        return {'ok': False, 'top': top, 'error': str(e)}


def run_single(args: argparse.Namespace) -> int:
    if not args.top:
        print('[❌] --top is required in single mode')
        return 2
    res = _run_one_top(args, args.top)
    print(res)
    return 0 if res.get('ok') else 2


def run_multi(args: argparse.Namespace) -> int:
    tops = list_candidate_tops(args.rtl)
    if not tops:
        print(f'[❌] No RTL tops found in: {args.rtl}')
        return 2

    print(f'[INFO] Found {len(tops)} candidate tops.')
    failures = 0
    for top in tops:
        res = _run_one_top(args, top)
        print(res)
        if not res.get('ok'):
            failures += 1

    if failures:
        print(f'[❌] {failures} top(s) failed.')
        return 2

    print('[✅] All tops completed successfully.')
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description='CLI wrapper around SpecBuilder (LLM-driven RTL spec generator)')
    parser.add_argument('--mode', choices=['single', 'multi'], default='single', help='Single top or multi-top mode')
    parser.add_argument('--slang', required=True, help='Path to slang binary')
    parser.add_argument('--rtl', required=True, help='Path to RTL directory')
    parser.add_argument('--top', help='Spec top module name (required for single mode). For multi mode, tops are inferred.')
    parser.add_argument('--design-top', help='Design top module used for clock/reset detection and Slang top (recommended).')
    parser.add_argument(
        '--scope-path', help='Instance hierarchy path for Slang --ast-json-scope (e.g., cva6.ex_stage_i.lsu_i.i_load_unit)'
    )
    parser.add_argument('--discover-scope-module', help='Find instance scope paths for this module name (e.g., load_unit)')
    parser.add_argument('--discover-only', action='store_true', help='Only print discovered scope paths and exit')
    parser.add_argument(
        '--include',
        '-I',
        action='append',
        nargs='+',
        default=[],
        help='Include directories (repeatable; e.g. -I dir1 -I dir2)',
    )
    parser.add_argument(
        '--defines',
        '-D',
        action='append',
        nargs='+',
        default=[],
        help='Defines to pass to Slang (repeatable; e.g. -D FOO=1 -D BAR)',
    )
    parser.add_argument('--dir', default='out_spec', help='Output directory for spec artifacts')
    parser.add_argument(
        '--llm-config',
        required=True,
        help='YAML config for LLM (spec_prompt.yaml)',
    )
    parser.add_argument(
        '--no-disable-analysis',
        action='store_true',
        help='Enable full analysis in Slang',
    )
    parser.add_argument(
        '--filelist',
        help='Optional HDL filelist (one path per line). If provided, SpecBuilder '
        'uses only these files and does not run dependency discovery.',
    )
    parser.add_argument(
        '-f',
        '--config-file',
        dest='config_file',
        help='YAML config file with default arguments',
    )
    parser.add_argument('--debug', action='store_true', help='Enable debug output')
    parser.add_argument('--whitebox', action='store_true', help='Whitebox mode: include internal signals in spec.')

    args = parser.parse_args()
    args = merge_config(args, args.config_file)

    args.rtl = os.path.expanduser(args.rtl)
    args.include = _sanitize_incdirs(_flatten_str_lists(args.include))
    args.llm_config = os.path.expanduser(args.llm_config)

    if not os.path.isfile(args.slang):
        print(f'[❌] slang not found: {args.slang}')
        return 2
    if not os.path.isdir(args.rtl):
        print(f'[❌] RTL directory not found: {args.rtl}')
        return 2

    if args.mode == 'single':
        if not args.top:
            print('[❌] --top is required in single mode')
            return 2
        return run_single(args)
    else:
        return run_multi(args)


if __name__ == '__main__':
    raise SystemExit(main())
