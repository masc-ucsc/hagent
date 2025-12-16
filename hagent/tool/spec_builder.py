#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
spec_builder.py
---------------
End-to-end RTL → Spec (Markdown + CSV) generator.

Pipeline:
  1) Collect RTL:
       - Either from a user-supplied filelist (one file per line), OR
       - Using hdl_utils-style discovery + dependency closure from design top.
  2) Run Slang to dump AST JSON for the *spec top* module
  3) Parse AST to extract:
       - Ports (I/O only) of the spec top
       - Parameters (of the spec top)
       - FSM case blocks (source spans + RTL excerpts)
       - Logic blocks (always/if/assign snapshots for context)
  4) Detect clock/reset for the *design top* via clk_rst_utils
  5) Build context JSON and invoke LLM_wrap (MANDATORY) with spec_prompt.yaml:
       - doc_sections           -> prose sections for .md
       - interface_table        -> ports table for .md
       - parameter_table        -> params table for .md
       - fsm_specification      -> per-FSM state writeups for .md
       - sva_row_list_csv       -> I/O-only CSV for property generation
  6) Write outputs to: <out_dir>/{top}_ast.json, {top}_logic_blocks.json,
                       {top}_spec.md, {top}_spec.csv

Terminology:

  top        : "spec top" — the module we are documenting (and later generating CSV for).
  design_top : optional, the real design top used for clk/rst detection and
               dependency closure. Defaults to `top` if not provided.

Typical usage for submodules:

  Design top: cva6
  Spec top  : load_unit

  - Use design_top='cva6' for clock/reset and file dependencies
  - Use top='load_unit' so Markdown/CSV focus on load_unit interface + behavior
"""

from __future__ import annotations
import os
import re
import json
import argparse
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional

# ──────────────────────────────────────────────────────────────────────────────
# Optional rich console for nice logs (safe if missing)
# ──────────────────────────────────────────────────────────────────────────────
try:
    from rich.console import Console

    console = Console()
except Exception:  # pragma: no cover

    class _Dummy:
        def print(self, *a, **k):
            print(*a)

    console = _Dummy()

# ──────────────────────────────────────────────────────────────────────────────
# Mandatory LLM + templates
# ──────────────────────────────────────────────────────────────────────────────
from hagent.core.llm_wrap import LLM_wrap
from hagent.core.llm_template import LLM_template

# ──────────────────────────────────────────────────────────────────────────────
# Utilities: clk/rst (required)
# ──────────────────────────────────────────────────────────────────────────────
from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

try:
    _HAS_HDL_UTILS = True
except Exception:  # pragma: no cover
    _HAS_HDL_UTILS = False


# ──────────────────────────────────────────────────────────────────────────────
# Helpers
# ──────────────────────────────────────────────────────────────────────────────
CSV_HEADER = ['sid', 'prop_type', 'module', 'name', 'scenario', 'pre', 'post', 'signals', 'param_ok', 'notes']

ALWAYS_KINDS = {'always', 'alwayscomb', 'alwaysff', 'always_latch', 'proceduralblock'}
ASSIGN_KINDS = {'continuousassign'}
IF_KINDS = {'if'}
CASE_KINDS = {'case'}


def _ensure_dir(p: Path) -> None:
    p.mkdir(parents=True, exist_ok=True)


def _write_text(path: Path, text: str) -> None:
    path.write_text(text if text.endswith('\n') else (text + '\n'), encoding='utf-8')


def _write_json(path: Path, obj: Any) -> None:
    path.write_text(json.dumps(obj, indent=2), encoding='utf-8')


# ──────────────────────────────────────────────────────────────────────────────
# AST Parsers
# ──────────────────────────────────────────────────────────────────────────────
def _packed_range_from_node(n: Dict[str, Any]) -> Optional[str]:
    rng = n.get('packed_range') or n.get('range') or n.get('dimensions')
    if isinstance(rng, str):
        return rng
    if isinstance(rng, dict):
        left = rng.get('left')
        r = rng.get('right')
        if left is not None and r is not None:
            return f'[{left}:{r}]'
    return None


def _data_type_from_decl(n: Dict[str, Any]) -> Optional[str]:
    base = n.get('data_type') or n.get('type') or n.get('decl_type')
    if isinstance(base, dict):
        bt = base.get('name') or base.get('type') or base.get('kind')
        rng = _packed_range_from_node(base) or _packed_range_from_node(n) or ''
        return f'{rng + " " if rng else ""}{bt or "logic"}'.strip()
    if isinstance(base, str):
        rng = _packed_range_from_node(n) or ''
        return f'{rng + " " if rng else ""}{base}'.strip()
    rng = _packed_range_from_node(n) or ''
    if rng:
        return f'{rng} logic'
    return None


def extract_ports_from_ast(module_ast: Dict[str, Any]) -> List[Dict[str, str]]:
    """
    Extract *declared* top-level ports from AST (I/O only) of the spec top.
    """
    ports: List[Dict[str, str]] = []

    def norm_dir(d):
        if not d:
            return '-'
        d = str(d).lower()
        if 'inout' in d:
            return 'Inout'
        if 'input' in d or d == 'in':
            return 'In'
        if 'output' in d or d == 'out':
            return 'Out'
        return '-'

    def add_port(name, direction, dtype):
        if not name:
            return
        ports.append({'name': name, 'dir': norm_dir(direction), 'type': dtype or '-', 'desc': '-'})

    def walk(n):
        if isinstance(n, dict):
            k = n.get('kind', '')
            if k.lower().startswith('port'):
                name = n.get('name') or n.get('symbol')
                direction = n.get('direction') or n.get('dir')
                dtype = _data_type_from_decl(n)

                decl = n.get('decl') or n.get('declared') or n.get('declaration') or {}
                if (not name) and isinstance(decl, dict):
                    name = decl.get('name') or decl.get('symbol')
                    dtype = dtype or _data_type_from_decl(decl)
                    direction = direction or decl.get('direction')

                if name:
                    add_port(name, direction, dtype)

            for v in n.values():
                walk(v)
        elif isinstance(n, list):
            for it in n:
                walk(it)

    walk(module_ast)

    uniq: List[Dict[str, str]] = []
    seen = set()
    for p in ports:
        if p['name'] not in seen:
            uniq.append(p)
            seen.add(p['name'])
    return uniq


def extract_parameters_from_ast(module_ast: Dict[str, Any]) -> List[Dict[str, str]]:
    params: List[Dict[str, str]] = []

    def render_expr(e):
        if isinstance(e, dict):
            return e.get('text') or e.get('value') or e.get('literal') or e.get('name')
        return str(e) if e is not None else None

    def add_param(name, ptype, default):
        if not name:
            return
        params.append(
            {
                'name': name,
                'type': ptype or '-',
                'default': default if default not in (None, '') else '-',
                'desc': '-',
            }
        )

    def walk(n):
        if isinstance(n, dict):
            k = n.get('kind', '').lower()
            if 'parameter' in k:
                name = n.get('name') or n.get('symbol')
                dt = n.get('data_type') or n.get('type')
                ptype = dt.get('name') if isinstance(dt, dict) else (dt if isinstance(dt, str) else None)
                default = render_expr(n.get('initializer') or n.get('value') or n.get('init'))
                if name:
                    add_param(name, ptype, default)
            for v in n.values():
                walk(v)
        elif isinstance(n, list):
            for it in n:
                walk(it)

    walk(module_ast)

    uniq: List[Dict[str, str]] = []
    seen = set()
    for p in params:
        if p['name'] not in seen:
            uniq.append(p)
            seen.add(p['name'])
    return uniq


def _src_info(n: Dict[str, Any]) -> Dict[str, Any]:
    return {
        'file': n.get('source_file_start') or n.get('source_file'),
        'ls': n.get('source_line_start') or n.get('source_line'),
        'le': n.get('source_line_end') or n.get('source_line'),
    }


def extract_logic_blocks(module_ast: Dict[str, Any], extract_rtl_fn) -> List[Dict[str, Any]]:
    """
    Collect compact logic blocks (always/if/assign/case) with short code excerpts for LLM context.
    """
    blocks: List[Dict[str, Any]] = []

    def add_block(kind: str, n: dict):
        info = _src_info(n)
        if info['file'] and info['ls'] and info['le']:
            code = extract_rtl_fn(info['file'], int(info['ls']), int(info['le']))
        else:
            code = ''
        blocks.append(
            {
                'kind': kind,
                'where': info,
                'code': code[:8000],
            }
        )

    def walk(n):
        if isinstance(n, dict):
            k = (n.get('kind') or '').lower()
            if k in ALWAYS_KINDS:
                add_block('always', n)
            elif k in IF_KINDS:
                add_block('if', n)
            elif k in ASSIGN_KINDS:
                add_block('assign', n)
            elif k in CASE_KINDS:
                add_block('case', n)

            for v in n.values():
                walk(v)
        elif isinstance(n, list):
            for it in n:
                walk(it)

    walk(module_ast)
    return blocks


def parse_case_blocks(module_ast: Dict[str, Any], extract_rtl_fn) -> List[Dict[str, Any]]:
    """
    Extract case statements with file/line spans and an RTL excerpt.
    """
    case_blocks: List[Dict[str, Any]] = []

    def _collect_span(node):
        src_file = None
        min_ln = None
        max_ln = None

        def _visit(n):
            nonlocal src_file, min_ln, max_ln
            if isinstance(n, dict):
                sf = n.get('source_file_start') or n.get('source_file')
                ls = n.get('source_line_start') or n.get('source_line')
                le = n.get('source_line_end') or n.get('source_line')
                if sf and ls and le:
                    if src_file is None:
                        src_file = sf
                    if src_file == sf:
                        min_ln = ls if min_ln is None else min(min_ln, ls)
                        max_ln = le if max_ln is None else max(max_ln, le)
                for v in n.values():
                    _visit(v)
            elif isinstance(n, list):
                for it in n:
                    _visit(it)

        _visit(node)
        return src_file, min_ln, max_ln

    def _find_expr_name(expr) -> Optional[str]:
        def _walk(n):
            if isinstance(n, dict):
                if n.get('kind') in ('NamedValue', 'ArbitrarySymbol'):
                    return n.get('symbol') or n.get('name')
                for v in n.values():
                    r = _walk(v)
                    if r:
                        return r
            elif isinstance(n, list):
                for it in n:
                    r = _walk(it)
                    if r:
                        return r
            return None

        sym = expr.get('symbol')
        return sym or _walk(expr) or expr.get('kind') or 'state'

    def walk(n):
        if isinstance(n, dict):
            if n.get('kind') == 'Case':
                expr = n.get('expr', {})
                expr_sym = _find_expr_name(expr)

                src = _src_info(n)
                if not (src['file'] and src['ls'] and src['le']):
                    sf, ls, le = _collect_span(n)
                    src = {'file': sf, 'ls': ls, 'le': le}

                block = {
                    'expr_symbol': expr_sym,
                    'source_file': src['file'],
                    'line_start': src['ls'],
                    'line_end': src['le'],
                }

                if block['source_file'] and block['line_start'] and block['line_end']:
                    block['rtl_code'] = extract_rtl_fn(block['source_file'], int(block['line_start']), int(block['line_end']))
                else:
                    block['rtl_code'] = ''

                case_blocks.append(block)

            for v in n.values():
                walk(v)
        elif isinstance(n, list):
            for it in n:
                walk(it)

    walk(module_ast)

    seen = set()
    uniq: List[Dict[str, Any]] = []
    for b in case_blocks:
        uid = (
            os.path.basename(b.get('source_file') or 'n/a'),
            int(b.get('line_start') or 0),
            int(b.get('line_end') or 0),
        )
        if uid in seen:
            continue
        seen.add(uid)
        uniq.append(b)

    uniq.sort(
        key=lambda x: (
            os.path.basename(x.get('source_file') or ''),
            int(x.get('line_start') or 0),
        )
    )
    return uniq


# ──────────────────────────────────────────────────────────────────────────────
# Builder
# ──────────────────────────────────────────────────────────────────────────────
class SpecBuilder:
    def __init__(
        self,
        slang_bin: Path,
        rtl_dir: Path,
        top: str,
        out_dir: Path,
        llm_conf: Path,
        include_dirs: Optional[List[Path]] = None,
        defines: Optional[List[str]] = None,
        disable_analysis: bool = True,
        design_top: Optional[str] = None,
        filelist: Optional[Path] = None,
    ):
        """
        Parameters
        ----------
        slang_bin : Path
            Slang binary.
        rtl_dir : Path
            RTL root directory.
        top : str
            Spec top (module we are documenting & generating CSV for).
        out_dir : Path
            Output directory for spec artifacts.
        llm_conf : Path
            spec_prompt.yaml
        include_dirs : list[Path]
            Extra include dirs for Slang.
        defines : list[str]
            Slang defines.
        disable_analysis : bool
            If True, pass --disable-analysis to Slang.
        design_top : str | None
            Design top used for clk/rst detection and dependency closure.
            Defaults to `top` if not provided.
        filelist : Path | None
            Optional HDL filelist (one file path per line). If provided,
            dependency discovery is skipped and only these files are given to Slang.
        """
        self.slang_bin = slang_bin
        self.rtl_dir = rtl_dir
        self.top = top  # spec top
        self.design_top = design_top or top
        self.out_dir = out_dir
        self.llm_conf = llm_conf
        self.include_dirs = include_dirs or []
        self.defines = defines or []
        self.disable_analysis = disable_analysis
        self.filelist = filelist

        _ensure_dir(self.out_dir)

        # Outputs base on *spec top*
        self.out_json = self.out_dir / f'{self.top}_ast.json'
        self.out_md = self.out_dir / f'{self.top}_spec.md'
        self.out_csv = self.out_dir / f'{self.top}_spec.csv'
        self.logic_snap = self.out_dir / f'{self.top}_logic_blocks.json'

        # LLM is mandatory
        if not self.llm_conf.exists():
            console.print(f'[red]❌ LLM config not found: {self.llm_conf}[/red]')
            raise SystemExit(2)

        console.print(f'[cyan][LLM] Using config:[/cyan] {self.llm_conf}')
        self.llm = LLM_wrap(name='default', conf_file=str(self.llm_conf), log_file='spec_llm.log')
        self.tmpl = LLM_template(str(self.llm_conf))
        self.template_dict = getattr(self.tmpl, 'template_dict', {}) or {}

        # Minimal template guard
        for req in ('doc_sections', 'fsm_specification', 'sva_row_list_csv'):
            if not (self.template_dict.get('default', {}).get(req)):
                console.print(f"[red]❌ Required prompt '{req}' missing in: {self.llm_conf}[/red]")
                raise SystemExit(2)

        # clock/reset (from design top)
        self.clk, self.rst, self.rst_expr = detect_clk_rst_for_top(self.rtl_dir, self.design_top)

    # ──────────────────────────────────────────────────────────────────────
    # RTL collection & Slang
    # ──────────────────────────────────────────────────────────────────────
    def _collect_rtl_files(self) -> List[Path]:
        """
        Fallback RTL discovery when no explicit filelist is provided.
        """
        try:
            from hagent.tool.utils.hdl_utils import find_sv_files  # type: ignore[attr-defined]

            files = find_sv_files(self.rtl_dir, skip_dirs=set())
            return sorted([Path(f) for f in files])
        except Exception as e:  # pragma: no cover
            console.print(f'[yellow]⚠ find_sv_files failed; falling back. ({e})[/yellow]')
            return [p for p in self.rtl_dir.rglob('*') if p.suffix in {'.sv', '.svh', '.v', '.vh'}]

    def _files_from_filelist(self) -> List[Path]:
        """
        Read files from a user-provided filelist (one path per line).
        Relative paths are resolved relative to rtl_dir.
        """
        if self.filelist is None:
            return []
        fl = self.filelist
        if not fl.exists():
            console.print(f'[red]❌ Filelist not found: {fl}[/red]')
            raise SystemExit(2)

        console.print(f'[cyan]• Using HDL filelist:[/cyan] {fl}')
        out: List[Path] = []
        for raw in fl.read_text().splitlines():
            line = raw.strip()
            if not line or line.startswith('#'):
                continue
            p = Path(line)
            if not p.is_absolute():
                p = (self.rtl_dir / p).resolve()
            else:
                p = p.resolve()
            if not p.exists():
                console.print(f'[yellow]⚠ File from filelist does not exist:[/yellow] {p}')
                continue
            out.append(p)
        if not out:
            console.print(f'[red]❌ No valid RTL files after reading filelist: {fl}[/red]')
            raise SystemExit(2)
        return out

    def _resolve_required(self, all_rtl: List[Path]) -> List[Path]:
        """
        If hdl_utils has richer dependency analysis, use it;
        otherwise just return all_rtl.
        """
        try:
            from hagent.tool.utils.hdl_utils import (  # type: ignore[attr-defined]
                index_modules_packages,
                compute_transitive_closure,
            )

            modules, packages = index_modules_packages(all_rtl)
            root_top = self.design_top or self.top
            if root_top not in modules:
                console.print(f"[red]❌ Design top '{root_top}' not found in RTL files (spec top = '{self.top}').[/red]")
                raise SystemExit(2)

            files_out, incdirs, _reachable = compute_transitive_closure(
                root_top, modules, packages, self.rtl_dir, self.include_dirs
            )
            self._incdirs_resolved = incdirs
            return files_out
        except Exception as e:  # pragma: no cover
            console.print(f'[yellow]⚠ compute_transitive_closure failed; falling back. ({e})[/yellow]')
            return all_rtl

    def _run_slang(self, req_files: List[Path]) -> None:
        cmd = [
            str(self.slang_bin),
            '--top',
            self.top,  # spec top
            '--ast-json',
            str(self.out_json),
            '--ast-json-source-info',
            '--ignore-unknown-modules',
            '--allow-use-before-declare',
            '--diag-abs-paths',
        ]
        if self.disable_analysis:
            cmd.append('--disable-analysis')
        for inc in self.include_dirs:
            cmd += ['-I', str(inc)]
        for d in self.defines:
            cmd.append(f'--define={d}')
        cmd += [str(f) for f in req_files]

        console.print('[cyan]• Running Slang to emit AST JSON[/cyan]')
        console.print('  ' + ' '.join(cmd))
        res = subprocess.run(cmd)
        if res.returncode != 0 or not self.out_json.exists():
            console.print(f'[red]❌ Slang failed (code={res.returncode}); AST not produced: {self.out_json}[/red]')
        else:
            console.print(f'[green]✔ AST written:[/green] {self.out_json}')

    # ──────────────────────────────────────────────────────────────────────
    # AST reading and top node search
    # ──────────────────────────────────────────────────────────────────────
    def _read_ast(self) -> Dict[str, Any]:
        return json.loads(self.out_json.read_text(encoding='utf-8'))

    def _find_top_module(self, ast: Dict[str, Any]) -> Optional[Dict[str, Any]]:
        """
        Locate the AST node for the *spec top* (self.top) inside the design.
        """

        def rec(node):
            if isinstance(node, dict):
                if node.get('kind') == 'Module' and node.get('name') == self.top:
                    return node
                if node.get('kind') == 'Instance' and node.get('name') == self.top:
                    return node.get('body')
                for v in node.values():
                    r = rec(v)
                    if r:
                        return r
            elif isinstance(node, list):
                for it in node:
                    r = rec(it)
                    if r:
                        return r
            return None

        return rec(ast.get('design', {}).get('members', []))

    # ──────────────────────────────────────────────────────────────────────
    # File code extraction
    # ──────────────────────────────────────────────────────────────────────
    @staticmethod
    def _extract_rtl(path: str, ls: int, le: int) -> str:
        try:
            lines = Path(path).read_text(encoding='utf-8', errors='ignore').splitlines()
            return '\n'.join(lines[max(0, ls - 1) : max(0, le)])
        except Exception as e:  # pragma: no cover
            return f'// Error extracting RTL: {e}'

    # ──────────────────────────────────────────────────────────────────────
    # LLM call (guarded)
    # ──────────────────────────────────────────────────────────────────────
    def _llm(self, prompt_index: str, payload: dict) -> str:
        try:
            out = self.llm.inference(payload, prompt_index=prompt_index, n=1)
            if isinstance(out, list) and out:
                return out[0] or ''
            if isinstance(out, str):
                return out
            if isinstance(out, dict) and 'choices' in out:
                try:
                    return out['choices'][0]['message']['content'] or ''
                except Exception:
                    return ''
            return ''
        except Exception as e:  # pragma: no cover
            console.print(f"[red]❌ LLM '{prompt_index}' failed: {e}[/red]")
            return ''

    # ──────────────────────────────────────────────────────────────────────
    # Build context and generate artifacts
    # ──────────────────────────────────────────────────────────────────────
    def run(self) -> None:
        # 1) Collect / resolve RTL
        if self.filelist is not None:
            req_files = self._files_from_filelist()
        else:
            console.print('[cyan]• Collecting RTL files[/cyan]')
            all_rtl = self._collect_rtl_files()
            if not all_rtl:
                console.print(f'[red]❌ No RTL files found under: {self.rtl_dir}[/red]')
                raise SystemExit(2)
            req_files = self._resolve_required(all_rtl)

        console.print(f'[green]✔ Required files for Slang:[/green] {len(req_files)}')

        # 2) Slang → AST
        self._run_slang(req_files)

        # 3) Parse AST for the spec top
        ast = self._read_ast()
        top_ast = self._find_top_module(ast)
        if not top_ast:
            console.print(f"[red]❌ Spec top module '{self.top}' not found in AST.[/red]")
            raise SystemExit(2)

        ports = extract_ports_from_ast(top_ast)
        params = extract_parameters_from_ast(top_ast)
        fsms = parse_case_blocks(top_ast, self._extract_rtl)
        logic = extract_logic_blocks(top_ast, self._extract_rtl)

        _write_json(self.logic_snap, logic)
        console.print(f'[green]✔ Logic snapshot:[/green] {self.logic_snap}')

        # 4) High-level context for LLM
        def fsm_summary(b):
            return {
                'expr_symbol': b.get('expr_symbol') or 'state',
                'source': os.path.basename(b.get('source_file') or ''),
                'line_start': b.get('line_start'),
                'line_end': b.get('line_end'),
                'rtl_excerpt': (b.get('rtl_code') or '')[:4000],
            }

        allowed_signals = [p['name'] for p in ports]

        ctx = {
            'top_module': self.top,
            'design_top': self.design_top,
            'clock': self.clk,
            'reset': self.rst,
            'reset_expr': self.rst_expr,
            'ports': ports,
            'params': params,
            'fsms': [fsm_summary(b) for b in fsms],
            # IMPORTANT: give some logic to LLM so spec/CSV reflect RTL behavior
            'logic_blocks': logic[:200],
            'csv_head': CSV_HEADER,
            'allowed_signals': allowed_signals,
            'notes': [
                "CSV must use only input/output signals from 'ports' (interface of the spec top).",
                'Avoid internal regs/wires.',
                'Expressions must be valid SystemVerilog.',
            ],
        }

        # 5) Generate Markdown
        md_parts: List[str] = []

        console.print('[cyan]• LLM: doc_sections[/cyan]')
        md_doc = self._llm('doc_sections', {'context_json': json.dumps(ctx, ensure_ascii=False)})
        if md_doc.strip():
            md_parts.append(md_doc.strip())

        if self.template_dict.get('default', {}).get('interface_table'):
            console.print('[cyan]• LLM: interface_table[/cyan]')
            md_if = self._llm('interface_table', {'ports_json': json.dumps(ports, ensure_ascii=False)})
            if md_if.strip():
                md_parts.append('### Interface\n\n' + md_if.strip())

        if params and self.template_dict.get('default', {}).get('parameter_table'):
            console.print('[cyan]• LLM: parameter_table[/cyan]')
            md_pa = self._llm('parameter_table', {'params_json': json.dumps(params, ensure_ascii=False)})
            if md_pa.strip():
                md_parts.append('### Parameters\n\n' + md_pa.strip())

        if fsms:
            md_parts.append(f'## FSM Specification for Module: {self.top}\n')
            for blk in fsms:
                console.print(f'[cyan]• LLM: fsm_specification ({blk.get("expr_symbol")})[/cyan]')
                fsm_json = {
                    'module': self.top,
                    'expr_symbol': blk.get('expr_symbol') or 'state',
                    'source_file': os.path.basename(blk.get('source_file') or ''),
                    'line_start': blk.get('line_start'),
                    'line_end': blk.get('line_end'),
                    'states': [],
                    'signals_seen': [],
                }
                md_fsm = self._llm(
                    'fsm_specification',
                    {
                        'module_name': self.top,
                        'fsm_json': json.dumps(fsm_json, ensure_ascii=False),
                        'rtl_code': blk.get('rtl_code') or '',
                    },
                )
                if md_fsm.strip():
                    md_parts.append(md_fsm.strip())

        md_text = '\n\n'.join([p for p in md_parts if p.strip()]) or f'## FSM Specification for Module: {self.top}\n'
        _write_text(self.out_md, md_text)
        console.print(f'[green]✔ Spec Markdown:[/green] {self.out_md}')

        # 7) Generate CSV (I/O only) via LLM
        console.print('[cyan]• LLM: sva_row_list_csv[/cyan]')
        csv_raw = self._llm(
            'sva_row_list_csv',
            {'context_json': json.dumps(ctx, ensure_ascii=False)},
        ).strip()

        if not csv_raw:
            console.print('[red]❌ LLM produced empty CSV text.[/red]')
            raise SystemExit(2)

        m = re.search(r'```(?:csv)?\s*([\s\S]*?)```', csv_raw, re.I)
        if m:
            csv_raw = m.group(1).strip()

        first_line = (csv_raw.splitlines() or [''])[0].strip().lower().replace(' ', '')
        expected = ','.join(CSV_HEADER).lower().replace(' ', '')
        if first_line != expected:
            csv_raw = ','.join(CSV_HEADER) + '\n' + csv_raw

        _write_text(self.out_csv, csv_raw)
        console.print(f'[green]✔ CSV spec:[/green] {self.out_csv}')
        console.print('[bold green]✅ SPEC BUILDER COMPLETED[/bold green]')


# ──────────────────────────────────────────────────────────────────────────────
# CLI
# ──────────────────────────────────────────────────────────────────────────────
def _parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description='LLM-driven RTL Spec Builder (Markdown + CSV)')
    p.add_argument('--slang', required=True, help='Path to slang binary')
    p.add_argument('--rtl', required=True, help='RTL directory')
    p.add_argument('--top', required=True, help='Spec top module name')
    p.add_argument(
        '--design-top',
        help='Design top module name for clk/rst + dependency closure (defaults to --top)',
    )
    p.add_argument('--out', required=True, help='Output directory')
    p.add_argument('--llm-conf', required=True, help='YAML prompt config (spec_prompt.yaml)')
    p.add_argument('--include', action='append', default=[], help='Additional include dirs (-I)')
    p.add_argument('--define', action='append', default=[], help='Slang defines (e.g., FOO=1)')
    p.add_argument(
        '--filelist',
        help='Optional HDL filelist (one path per line). If provided, dependency discovery is skipped.',
    )
    p.add_argument(
        '--no-disable-analysis',
        action='store_true',
        help='Enable Slang analysis (default: disabled)',
    )
    return p.parse_args()


def main() -> int:
    args = _parse_args()
    try:
        builder = SpecBuilder(
            slang_bin=Path(args.slang).resolve(),
            rtl_dir=Path(args.rtl).resolve(),
            top=args.top,
            design_top=args.design_top,
            out_dir=Path(args.out).resolve(),
            llm_conf=Path(args.llm_conf).resolve(),
            include_dirs=[Path(d).resolve() for d in (args.include or [])],
            defines=args.define or [],
            disable_analysis=not args.no_disable_analysis,
            filelist=Path(args.filelist).resolve() if args.filelist else None,
        )
        builder.run()
        return 0
    except SystemExit as se:
        return int(se.code) if isinstance(se.code, int) else 2
    except Exception as e:
        console.print(f'[red]❌ Unhandled error: {e}[/red]')
        return 2


if __name__ == '__main__':
    raise SystemExit(main())
