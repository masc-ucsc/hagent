#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
hagent/tool/spec_builder.py
---------------------------

Scoped-AST + IO-relations spec builder that matches hagent/step/sva_gen/spec_prompt.yaml.

Key additions:
- --scope-path: run Slang with --top <design_top> and --ast-json-scope <hier_path>
  => fixes typedef/member access issues and restricts AST to the chosen instance.
- --discover-scope-module: run a full AST once and discover instance paths matching a module name.
- Builds io_relations expected by your sva_row_list_csv prompt:
    io_relations:
      hints:
      relationships:
        control_signals_ranked:
        per_output_influences:
- Intermediate IR artifacts:
    <top>_ports.json
    <top>_assignments.jsonl
    <top>_io_relations.json
    <top>_io_influence.csv
    <top>_logic_blocks.json
- CSV validation + repair using the existing 'csv_repair' prompt.
"""

from __future__ import annotations

import os
import re
import csv
import json
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Set, Iterable
from io import StringIO

# ──────────────────────────────────────────────────────────────────────────────
# Optional rich console
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
# Mandatory LLM + templates (your existing infra)
# ──────────────────────────────────────────────────────────────────────────────
from hagent.core.llm_wrap import LLM_wrap
from hagent.core.llm_template import LLM_template
from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

CSV_HEADER = ['sid', 'prop_type', 'module', 'name', 'scenario', 'pre', 'post', 'signals', 'param_ok', 'notes']
SV_SUFFIXES = {'.sv', '.svh', '.v', '.vh'}

_SV_KEYWORDS = {
    'and',
    'or',
    'not',
    'iff',
    'if',
    'else',
    'case',
    'endcase',
    'begin',
    'end',
    'posedge',
    'negedge',
    'disable',
    'property',
    'endproperty',
    'assert',
    'assume',
    'cover',
    'sequence',
    'endsequence',
    'module',
    'endmodule',
    'always',
    'always_ff',
    'always_comb',
    'always_latch',
    'logic',
    'wire',
    'reg',
    'input',
    'output',
    'inout',
    'localparam',
    'parameter',
    'typedef',
    'struct',
    'union',
    'enum',
    'packed',
    'signed',
    'unsigned',
    'int',
    'integer',
    'bit',
    'byte',
    'shortint',
    'longint',
    'true',
    'false',
    'default',
}
_ALLOWED_SVA_FUNCS = {'$rose', '$fell', '$stable', '$changed', '$past'}


# ──────────────────────────────────────────────────────────────────────────────
# File utils
# ──────────────────────────────────────────────────────────────────────────────
def _ensure_dir(p: Path) -> None:
    p.mkdir(parents=True, exist_ok=True)


def _write_text(path: Path, text: str) -> None:
    path.write_text(text if text.endswith('\n') else (text + '\n'), encoding='utf-8')


def _write_json(path: Path, obj: Any) -> None:
    path.write_text(json.dumps(obj, indent=2), encoding='utf-8')


def _write_jsonl(path: Path, rows: Iterable[Dict[str, Any]]) -> None:
    with path.open('w', encoding='utf-8') as f:
        for r in rows:
            f.write(json.dumps(r, ensure_ascii=False) + '\n')


def _basename(p: Optional[str]) -> str:
    return os.path.basename(p) if p else ''


# ──────────────────────────────────────────────────────────────────────────────
# AST helpers (robust)
# ──────────────────────────────────────────────────────────────────────────────
def _is_invalid_node(n: Any) -> bool:
    return isinstance(n, dict) and (n.get('kind') == 'Invalid' or n.get('type') == '<error>')


def _src_info(n: Dict[str, Any]) -> Dict[str, Any]:
    return {
        'file': n.get('source_file_start') or n.get('source_file'),
        'ls': n.get('source_line_start') or n.get('source_line'),
        'le': n.get('source_line_end') or n.get('source_line'),
        'cs': n.get('source_column_start') or n.get('source_column'),
        'ce': n.get('source_column_end') or n.get('source_column'),
    }


def _extract_rtl_excerpt(path: str, ls: int, le: int, max_chars: int = 8000) -> str:
    try:
        lines = Path(path).read_text(encoding='utf-8', errors='ignore').splitlines()
        text = '\n'.join(lines[max(0, ls - 1) : max(0, le)])
        return text[:max_chars]
    except Exception as e:  # pragma: no cover
        return f'// Error extracting RTL excerpt: {e}'


def _member_name_field(member_field: Any) -> Optional[str]:
    if member_field is None:
        return None
    if isinstance(member_field, str):
        parts = member_field.strip().split()
        return parts[-1] if parts else None
    return str(member_field)


def _expr_text(n: Any) -> str:
    if n is None:
        return ''
    if _is_invalid_node(n):
        return '/*INVALID*/'
    if isinstance(n, str):
        return n
    if isinstance(n, (int, float, bool)):
        return str(n)
    if isinstance(n, list):
        return ', '.join(_expr_text(x) for x in n)
    if not isinstance(n, dict):
        return str(n)

    if isinstance(n.get('text'), str) and n['text'].strip():
        return n['text'].strip()
    if isinstance(n.get('value'), str) and n['value'].strip():
        return n['value'].strip()
    if isinstance(n.get('constant'), str) and n['constant'].strip():
        return n['constant'].strip()

    k = n.get('kind')

    if k == 'NamedValue':
        sym = n.get('symbol') or n.get('name')
        if isinstance(sym, str):
            return sym.strip().split()[-1]
        return str(sym) if sym is not None else '<?>'

    if k == 'MemberAccess':
        base = _expr_text(n.get('value'))
        mem = _member_name_field(n.get('member')) or '<?>'
        return f'{base}.{mem}'

    if k == 'ElementSelect':
        base = _expr_text(n.get('value'))
        sel = _expr_text(n.get('selector'))
        return f'{base}[{sel}]'

    if k == 'RangeSelect':
        base = _expr_text(n.get('value'))
        left = _expr_text(n.get('left'))
        right = _expr_text(n.get('right'))
        return f'{base}[{left}:{right}]'

    if k == 'Concatenation':
        ops = n.get('operands') or []
        return '{' + ', '.join(_expr_text(x) for x in ops) + '}'

    if k == 'UnaryOp':
        op = n.get('op') or ''
        operand = _expr_text(n.get('operand'))
        opmap = {'LogicalNot': '!', 'BitwiseNot': '~', 'UnaryPlus': '+', 'UnaryMinus': '-'}
        return f'{opmap.get(op, op)}{operand}'

    if k == 'BinaryOp':
        op = n.get('op') or ''
        left = _expr_text(n.get('left'))
        right = _expr_text(n.get('right'))
        opmap = {
            'LogicalAnd': '&&',
            'LogicalOr': '||',
            'BitwiseAnd': '&',
            'BitwiseOr': '|',
            'BitwiseXor': '^',
            'Equality': '==',
            'Inequality': '!=',
            'GreaterThan': '>',
            'GreaterThanEqual': '>=',
            'LessThan': '<',
            'LessThanEqual': '<=',
            'Add': '+',
            'Subtract': '-',
            'Multiply': '*',
            'Divide': '/',
            'Modulo': '%',
            'LogicalShiftLeft': '<<',
            'LogicalShiftRight': '>>',
            'ArithmeticShiftRight': '>>>',
        }
        svop = opmap.get(op, op)
        return f'({left} {svop} {right})'

    if k == 'ConditionalOp':
        conds = n.get('conditions') or []
        if conds and isinstance(conds, list) and isinstance(conds[0], dict) and 'expr' in conds[0]:
            c = _expr_text(conds[0]['expr'])
            t = _expr_text(n.get('left'))
            f = _expr_text(n.get('right'))
            return f'({c} ? {t} : {f})'
        return '/*COND_OP*/'

    if k == 'Call':
        sub = n.get('subroutine') or n.get('name') or 'call'
        args = n.get('arguments') or []
        return f'{sub}(' + ', '.join(_expr_text(a) for a in args) + ')'

    return f'/*{k or "node"}*/'


# ──────────────────────────────────────────────────────────────────────────────
# Ports / params from SCOPED bodies
# ──────────────────────────────────────────────────────────────────────────────
def extract_ports_from_body(body: Dict[str, Any]) -> List[Dict[str, str]]:
    ports: List[Dict[str, str]] = []

    def norm_dir(d: Any) -> str:
        if not d:
            return '-'
        s = str(d).lower()
        if 'inout' in s:
            return 'Inout'
        if s in ('in', 'input'):
            return 'In'
        if s in ('out', 'output'):
            return 'Out'
        return '-'

    members = body.get('members') or []
    for m in members:
        if not isinstance(m, dict):
            continue
        if m.get('kind') != 'Port':
            continue
        name = m.get('name')
        direction = norm_dir(m.get('direction'))
        dtype = m.get('type') or '-'
        if name:
            ports.append({'name': name, 'dir': direction, 'type': str(dtype), 'desc': '-'})

    # Fallback walker if needed (older dumps)
    if not ports:

        def walk(n: Any) -> None:
            if n is None or _is_invalid_node(n):
                return
            if isinstance(n, list):
                for it in n:
                    walk(it)
                return
            if not isinstance(n, dict):
                return
            k = (n.get('kind') or '').lower()
            if 'port' in k and n.get('name') and n.get('direction'):
                ports.append(
                    {'name': n.get('name'), 'dir': norm_dir(n.get('direction')), 'type': str(n.get('type') or '-'), 'desc': '-'}
                )
            for v in n.values():
                walk(v)

        walk(body)

    # de-dupe by name
    out: List[Dict[str, str]] = []
    seen: Set[str] = set()
    for p in ports:
        if p['name'] in seen:
            continue
        seen.add(p['name'])
        out.append(p)
    return out


def extract_parameters_from_body(body: Dict[str, Any]) -> List[Dict[str, str]]:
    params: List[Dict[str, str]] = []
    for m in body.get('members') or []:
        if not isinstance(m, dict):
            continue
        if m.get('kind') != 'Parameter':
            continue
        name = m.get('name')
        ptype = m.get('type') or '-'
        default = m.get('value') or (m.get('initializer', {}) or {}).get('constant') or '-'
        if name:
            params.append({'name': name, 'type': str(ptype), 'default': str(default), 'desc': '-'})
    # de-dupe
    out: List[Dict[str, str]] = []
    seen: Set[str] = set()
    for p in params:
        if p['name'] in seen:
            continue
        seen.add(p['name'])
        out.append(p)
    return out


# ──────────────────────────────────────────────────────────────────────────────
# Assignment extraction with guards (IO slicing base)
# ──────────────────────────────────────────────────────────────────────────────
@dataclass
class AssignRecord:
    assign_id: str
    kind: str  # ContinuousAssign | AlwaysComb | AlwaysFF | Unknown
    proc_kind: str
    lhs_text: str
    rhs_text: str
    defs: List[str]
    uses: List[str]
    guards: List[str]
    block_path: str
    src_file: str
    src_ls: int
    src_le: int


def _canonical_signal_ref(expr_node: Dict[str, Any]) -> Optional[str]:
    if _is_invalid_node(expr_node):
        return None
    k = expr_node.get('kind')
    if k == 'NamedValue':
        s = expr_node.get('symbol') or expr_node.get('name')
        if isinstance(s, str):
            return s.strip().split()[-1]
        return None
    if k == 'MemberAccess':
        base = _canonical_signal_ref(expr_node.get('value') or {})
        mem = _member_name_field(expr_node.get('member')) or None
        if base and mem:
            return f'{base}.{mem}'
        return base
    if k == 'ElementSelect':
        base = _canonical_signal_ref(expr_node.get('value') or {})
        sel = _expr_text(expr_node.get('selector'))
        if base and sel:
            return f'{base}[{sel}]'
        return base
    if k == 'RangeSelect':
        base = _canonical_signal_ref(expr_node.get('value') or {})
        left = _expr_text(expr_node.get('left'))
        right = _expr_text(expr_node.get('right'))
        if base and left and right:
            return f'{base}[{left}:{right}]'
        return base
    return None


def _collect_signal_refs(expr: Any, out: Set[str]) -> None:
    if expr is None or _is_invalid_node(expr):
        return
    if isinstance(expr, list):
        for it in expr:
            _collect_signal_refs(it, out)
        return
    if not isinstance(expr, dict):
        return
    k = expr.get('kind')
    if k in ('NamedValue', 'MemberAccess', 'ElementSelect', 'RangeSelect'):
        ref = _canonical_signal_ref(expr)
        if ref:
            out.add(ref)
    for v in expr.values():
        _collect_signal_refs(v, out)


def _collect_lhs_defs(lhs_expr: Any, out: Set[str]) -> None:
    if lhs_expr is None or _is_invalid_node(lhs_expr):
        return
    if isinstance(lhs_expr, list):
        for it in lhs_expr:
            _collect_lhs_defs(it, out)
        return
    if not isinstance(lhs_expr, dict):
        return
    k = lhs_expr.get('kind')
    if k in ('NamedValue', 'MemberAccess', 'ElementSelect', 'RangeSelect'):
        ref = _canonical_signal_ref(lhs_expr)
        if ref:
            out.add(ref)
        return
    if k == 'Concatenation':
        for op in lhs_expr.get('operands') or []:
            _collect_lhs_defs(op, out)
        return
    for v in lhs_expr.values():
        _collect_lhs_defs(v, out)


def extract_assignments_with_guards(body: Dict[str, Any]) -> List[AssignRecord]:
    records: List[AssignRecord] = []
    assign_counter = 0

    def new_id() -> str:
        nonlocal assign_counter
        assign_counter += 1
        return f'A{assign_counter:05d}'

    def visit_stmt(node: Any, guards: List[str], path: List[str], proc_kind: str, logical_kind: str) -> None:
        if node is None or _is_invalid_node(node):
            return
        if isinstance(node, list):
            for it in node:
                visit_stmt(it, guards, path, proc_kind, logical_kind)
            return
        if not isinstance(node, dict):
            return

        k = node.get('kind', '')

        if k == 'ExpressionStatement':
            visit_stmt(node.get('expr'), guards, path, proc_kind, logical_kind)
            return

        if k == 'Assignment':
            lhs = node.get('left')
            rhs = node.get('right')
            defs: Set[str] = set()
            uses: Set[str] = set()
            _collect_lhs_defs(lhs, defs)
            _collect_signal_refs(rhs, uses)
            src = _src_info(node)
            records.append(
                AssignRecord(
                    assign_id=new_id(),
                    kind=logical_kind,
                    proc_kind=proc_kind,
                    lhs_text=_expr_text(lhs),
                    rhs_text=_expr_text(rhs),
                    defs=sorted(defs),
                    uses=sorted(uses),
                    guards=list(guards),
                    block_path='/'.join(path) if path else '',
                    src_file=src.get('file') or '',
                    src_ls=int(src.get('ls') or 0),
                    src_le=int(src.get('le') or 0),
                )
            )
            return

        if k == 'Conditional':
            conds = node.get('conditions') or []
            cond_expr = None
            if isinstance(conds, list) and conds:
                c0 = conds[0]
                if isinstance(c0, dict) and 'expr' in c0:
                    cond_expr = c0['expr']
            cond_txt = _expr_text(cond_expr) if cond_expr is not None else '/*cond*/'
            visit_stmt(node.get('ifTrue'), guards + [cond_txt], path + ['if'], proc_kind, logical_kind)
            if node.get('ifFalse') is not None:
                visit_stmt(node.get('ifFalse'), guards + [f'!({cond_txt})'], path + ['else'], proc_kind, logical_kind)
            return

        if k == 'Case':
            expr_txt = _expr_text(node.get('expr'))
            case_guard = f'case({expr_txt})'
            for field in ('items', 'cases', 'body'):
                if node.get(field) is not None:
                    visit_stmt(node.get(field), guards + [case_guard], path + ['case'], proc_kind, logical_kind)
            return

        if k == 'Block':
            b = node.get('body')
            if isinstance(b, dict) and b.get('kind') == 'List':
                visit_stmt(b.get('list') or [], guards, path, proc_kind, logical_kind)
            else:
                visit_stmt(b, guards, path, proc_kind, logical_kind)
            return

        # generic recursion
        for v in node.values():
            visit_stmt(v, guards, path, proc_kind, logical_kind)

    def visit_member(m: Any) -> None:
        if m is None or _is_invalid_node(m):
            return
        if isinstance(m, list):
            for it in m:
                visit_member(it)
            return
        if not isinstance(m, dict):
            return

        k = (m.get('kind') or '').lower()

        if k == 'continuousassign':
            asn = m.get('assignment') or {}
            visit_stmt(asn, guards=[], path=['assign'], proc_kind='', logical_kind='ContinuousAssign')
            return

        if k == 'proceduralblock':
            pk = str(m.get('procedureKind') or '')
            logical_kind = 'Unknown'
            if pk.lower() == 'alwayscomb':
                logical_kind = 'AlwaysComb'
            elif pk.lower() == 'alwaysff':
                logical_kind = 'AlwaysFF'
            visit_stmt(m.get('body'), guards=[], path=[pk], proc_kind=pk, logical_kind=logical_kind)
            return

        for v in m.values():
            visit_member(v)

    visit_member(body.get('members') or [])
    return records


# ──────────────────────────────────────────────────────────────────────────────
# Logic blocks + FSM case blocks (for your existing LLM prompts)
# ──────────────────────────────────────────────────────────────────────────────
def extract_logic_blocks(body: Dict[str, Any]) -> List[Dict[str, Any]]:
    blocks: List[Dict[str, Any]] = []

    def add_block(kind: str, n: Dict[str, Any]) -> None:
        src = _src_info(n)
        f = src.get('file')
        ls = int(src.get('ls') or 0)
        le = int(src.get('le') or 0)
        code = _extract_rtl_excerpt(f, ls, le) if f and ls and le else ''
        blocks.append({'kind': kind, 'where': src, 'code': code})

    def walk(n: Any) -> None:
        if n is None or _is_invalid_node(n):
            return
        if isinstance(n, list):
            for it in n:
                walk(it)
            return
        if not isinstance(n, dict):
            return
        k = (n.get('kind') or '').lower()
        if k == 'proceduralblock':
            add_block('always', n)
        elif k == 'conditional':
            add_block('if', n)
        elif k == 'continuousassign':
            add_block('assign', n)
        elif k == 'case':
            add_block('case', n)
        for v in n.values():
            walk(v)

    walk(body.get('members') or [])
    return blocks


def parse_case_blocks(body: Dict[str, Any]) -> List[Dict[str, Any]]:
    case_blocks: List[Dict[str, Any]] = []

    def walk(n: Any) -> None:
        if n is None or _is_invalid_node(n):
            return
        if isinstance(n, list):
            for it in n:
                walk(it)
            return
        if not isinstance(n, dict):
            return
        if n.get('kind') == 'Case':
            src = _src_info(n)
            case_blocks.append(
                {
                    'expr_symbol': _expr_text(n.get('expr')) or 'state',
                    'source_file': src.get('file') or '',
                    'line_start': int(src.get('ls') or 0),
                    'line_end': int(src.get('le') or 0),
                }
            )
        for v in n.values():
            walk(v)

    walk(body.get('members') or [])
    # de-dupe
    seen = set()
    out = []
    for b in case_blocks:
        key = (b['source_file'], b['line_start'], b['line_end'], b['expr_symbol'])
        if key in seen:
            continue
        seen.add(key)
        out.append(b)
    out.sort(key=lambda x: (_basename(x['source_file']), x['line_start']))
    return out


# ──────────────────────────────────────────────────────────────────────────────
# IO relations builder (matches your prompt expectations)
# ──────────────────────────────────────────────────────────────────────────────
def _base_port(ref: str) -> str:
    # strip member selects and indices
    if not ref:
        return ref
    ref = ref.split('.', 1)[0]
    ref = ref.split('[', 1)[0]
    return ref


def build_io_relations(
    ports: List[Dict[str, str]],
    assigns: List[AssignRecord],
    max_depth: int = 6,
) -> Dict[str, Any]:
    """
    Returns io_relations dict with:
      - relationships.control_signals_ranked
      - relationships.per_output_influences
      - hints (basic suggestions; conservative)
    """
    # port_dir: Dict[str, str] = {p["name"]: p["dir"] for p in ports}
    inputs = {p['name'] for p in ports if p['dir'] in ('In', 'Inout')}
    outputs = {p['name'] for p in ports if p['dir'] in ('Out', 'Inout')}

    # def_map: base_signal -> defining assignments
    def_map: Dict[str, List[AssignRecord]] = {}
    for a in assigns:
        for d in a.defs:
            def_map.setdefault(_base_port(d), []).append(a)

    # helper: backward slice to inputs
    def slice_to_inputs(start_base: str) -> Set[str]:
        found_inputs: Set[str] = set()
        q: List[Tuple[str, int]] = [(start_base, 0)]
        visited: Set[str] = {start_base}
        while q:
            sig, depth = q.pop(0)
            if sig in inputs:
                found_inputs.add(sig)
                continue
            if depth >= max_depth:
                continue
            for da in def_map.get(sig, []):
                for u in da.uses:
                    ub = _base_port(u)
                    if ub not in visited:
                        visited.add(ub)
                        q.append((ub, depth + 1))
        return found_inputs

    per_output: List[Dict[str, Any]] = []

    # Count control signal usage in guards (rank)
    ctrl_score: Dict[str, int] = {}

    for a in assigns:
        used_bases = {_base_port(u) for u in a.uses}
        guard_bases: Set[str] = set()
        for g in a.guards:
            # heuristic: pick tokens that look like identifiers in guard text
            for tok in re.findall(r'\b[A-Za-z_]\w*\b', g or ''):
                if tok in inputs:
                    guard_bases.add(tok)
        for gb in guard_bases:
            ctrl_score[gb] = ctrl_score.get(gb, 0) + 2
        # also small weight for direct RHS usage
        for ub in used_bases:
            if ub in inputs:
                ctrl_score[ub] = ctrl_score.get(ub, 0) + 1

        out_defs = sorted({d for d in a.defs if _base_port(d) in outputs})
        if not out_defs:
            continue

        direct_inputs = sorted({b for b in used_bases if b in inputs})

        # include transitive inputs via internal signals in RHS
        trans_inputs: Set[str] = set(direct_inputs)
        internal = [b for b in used_bases if b not in inputs and b not in outputs]
        for intr in internal:
            trans_inputs |= slice_to_inputs(intr)

        guard_txt = ' && '.join([g for g in a.guards if g and '/*INVALID*/' not in g]) if a.guards else ''

        for od in out_defs:
            per_output.append(
                {
                    'output': _base_port(od),
                    'inputs': sorted(trans_inputs),
                    'direct_inputs': direct_inputs,
                    'guards': guard_txt,
                    'effect': f'{a.lhs_text} = {a.rhs_text}',
                    'src': f'{_basename(a.src_file)}:{a.src_ls}-{a.src_le}',
                    'block_kind': a.kind,
                    'block_path': a.block_path,
                }
            )

    # de-dupe per_output influences
    seen = set()
    uniq: List[Dict[str, Any]] = []
    for r in per_output:
        key = (r['output'], r['effect'], r.get('guards', ''))
        if key in seen:
            continue
        seen.add(key)
        uniq.append(r)

    # ranked controls (only inputs)
    ranked = sorted(ctrl_score.items(), key=lambda kv: (-kv[1], kv[0]))
    control_signals_ranked = [k for k, _ in ranked][:30]

    # very conservative hints (your prompt can use them, but it already has safe patterns)
    hints = {
        'assume': [],
        'cover': [],
        'assert': [],
    }
    # Example: if a signal name suggests flush or valid/ready, add a hint (still not a concrete property)
    for s in control_signals_ranked[:10]:
        low = s.lower()
        if 'flush' in low:
            hints['assume'].append({'idea': 'flush is a pulse not stuck-high', 'signal': s})
        if 'valid' in low:
            hints['cover'].append({'idea': 'observe valid toggling', 'signal': s})
        if 'ready' in low or 'gnt' in low or 'grant' in low:
            hints['cover'].append({'idea': 'observe handshake acceptance', 'signal': s})

    return {
        'hints': hints,
        'relationships': {
            'control_signals_ranked': control_signals_ranked,
            'per_output_influences': uniq,
        },
    }


# ──────────────────────────────────────────────────────────────────────────────
# CSV validation + repair (uses your csv_repair prompt)
# ──────────────────────────────────────────────────────────────────────────────
def _strip_code_fences(s: str) -> str:
    if not s:
        return ''
    s = s.strip()
    m = re.search(r'```(?:csv)?\s*([\s\S]*?)```', s, re.I)
    if m:
        return m.group(1).strip()
    return s


def _ensure_csv_header(csv_text: str) -> str:
    csv_text = csv_text.strip()
    if not csv_text:
        return csv_text
    lines = csv_text.splitlines()
    first = (lines[0] if lines else '').strip().lower().replace(' ', '')
    expected = ','.join(CSV_HEADER).lower().replace(' ', '')
    if first != expected:
        return ','.join(CSV_HEADER) + '\n' + csv_text
    return csv_text


def _split_csv_line(line: str) -> List[str]:
    # Robust CSV parsing (handles quoted commas properly)
    r = csv.reader(StringIO(line), skipinitialspace=True)
    return [c.strip() for c in next(r, [])]


def _strip_sv_numeric_literals(expr: str) -> str:
    """
    Remove SystemVerilog numeric literals so tokenization doesn't treat parts like
    b0/hFF as identifiers.

    Examples removed:
      1'b0, 8'hFF, 16'd10, 4'sb1010, 'hFF, '0, '1, 'x, 'z
    """
    if not expr:
        return expr

    s = expr

    # Sized literals: 8'hFF, 1'b0, 16'd10, 4'sb1010, etc.
    s = re.sub(
        r"\b\d+\s*'\s*[sS]?[bBoOdDhH][0-9a-fA-FxXzZ_]+\b",
        ' ',
        s,
    )

    # Unsized base literals: 'hFF, 'b0, 'd10, etc.
    s = re.sub(
        r"(?<!\w)'\s*[sS]?[bBoOdDhH][0-9a-fA-FxXzZ_]+\b",
        ' ',
        s,
    )

    # Unsized 1-bit literals: '0, '1, 'x, 'z
    s = re.sub(
        r"(?<!\w)'\s*[01xXzZ]\b",
        ' ',
        s,
    )

    return s


def _extract_dotted_and_plain_identifiers(expr: str) -> List[str]:
    if not expr:
        return []

    # Remove quoted strings first (don’t parse identifiers inside them)
    expr2 = re.sub(r'\"[^\"]*\"', ' ', expr)

    # --- KEY FIX: strip SV numeric literals so we don't see b0/hFF/etc as "signals"
    expr2 = _strip_sv_numeric_literals(expr2)

    # Remove allowed SVA funcs so we don't treat them as identifiers
    for fn in _ALLOWED_SVA_FUNCS:
        expr2 = expr2.replace(fn, ' ')

    # Dotted refs first (struct/member chains)
    dotted = re.findall(r'\b[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)+\b', expr2)

    # Plain identifiers
    plain = re.findall(r'\b[A-Za-z_]\w*\b', expr2)

    dotted_set = set(dotted)
    out: List[str] = []

    for d in dotted:
        if d.lower() not in _SV_KEYWORDS:
            out.append(d)

    for p in plain:
        if p in dotted_set:
            continue
        if p.lower() in _SV_KEYWORDS:
            continue
        out.append(p)

    # de-dupe preserve order
    seen = set()
    uniq = []
    for x in out:
        if x not in seen:
            uniq.append(x)
            seen.add(x)
    return uniq


def _detect_nested_temporal(post: str) -> bool:
    return bool(post) and post.count('##') > 1


def validate_csv_text(csv_text: str, allowed_ports: List[str]) -> Dict[str, Any]:
    allowed_set = set(allowed_ports)
    report: Dict[str, Any] = {
        'ok': True,
        'errors': [],
        'invalid_identifiers': [],
        'signals_column_mismatches': [],
        'bad_rows': [],
        'nested_temporal': [],
    }

    csv_text = _ensure_csv_header(_strip_code_fences(csv_text))
    lines = [ln for ln in csv_text.splitlines() if ln.strip()]
    if not lines:
        report['ok'] = False
        report['errors'].append('empty_csv')
        return report

    hdr = lines[0].strip().lower().replace(' ', '')
    expected = ','.join(CSV_HEADER).lower().replace(' ', '')
    if hdr != expected:
        report['ok'] = False
        report['errors'].append('bad_header')

    for idx in range(1, len(lines)):
        line_no = idx + 1
        cols = _split_csv_line(lines[idx])
        if len(cols) != len(CSV_HEADER):
            report['ok'] = False
            report['bad_rows'].append({'line': line_no, 'reason': 'wrong_column_count', 'cols': len(cols), 'text': lines[idx]})
            continue

        row = dict(zip(CSV_HEADER, cols))
        sid = row.get('sid', '').strip()
        pre = row.get('pre', '').strip()
        post = row.get('post', '').strip()
        sigs_col = row.get('signals', '').strip()

        if _detect_nested_temporal(post):
            report['ok'] = False
            report['nested_temporal'].append({'line': line_no, 'sid': sid, 'post': post})

        used = _extract_dotted_and_plain_identifiers(pre) + _extract_dotted_and_plain_identifiers(post)

        used_base = []
        invalid = []
        for u in used:
            base = _base_port(u)
            if base.lower() in _SV_KEYWORDS:
                continue
            if base not in allowed_set:
                invalid.append(u)
            else:
                used_base.append(base)

        if invalid:
            report['ok'] = False
            report['invalid_identifiers'].append(
                {'line': line_no, 'sid': sid, 'invalid': sorted(set(invalid)), 'pre': pre, 'post': post}
            )

        used_set = set(used_base)
        if used_set:
            sigs_set = set([s for s in sigs_col.split() if s])
            if sigs_set != used_set:
                report['ok'] = False
                report['signals_column_mismatches'].append(
                    {'line': line_no, 'sid': sid, 'expected': ' '.join(sorted(used_set)), 'got': sigs_col}
                )

    return report


# ──────────────────────────────────────────────────────────────────────────────
# Scope discovery (find instance paths for a module definition)
# ──────────────────────────────────────────────────────────────────────────────
def find_instance_paths(ast: Dict[str, Any], target_module: str) -> List[str]:
    paths: List[str] = []

    def match_def(defn: str) -> bool:
        if not defn:
            return False
        return defn.endswith('.' + target_module) or defn.endswith('work.' + target_module) or defn.endswith('::' + target_module)

    def walk(n: Any, stack: List[str]) -> None:
        if n is None or _is_invalid_node(n):
            return
        if isinstance(n, list):
            for it in n:
                walk(it, stack)
            return
        if not isinstance(n, dict):
            return

        if n.get('kind') == 'Instance':
            inst_name = n.get('name') or ''
            body = n.get('body') or {}
            defn = body.get('definition') if isinstance(body, dict) else ''
            new_stack = stack + [inst_name] if inst_name else stack

            if match_def(defn):
                paths.append('.'.join(new_stack))

            # descend into instance body
            if isinstance(body, dict):
                walk(body.get('members') or [], new_stack)

            # also recurse other content
            for v in n.values():
                if v is body:
                    continue
                walk(v, new_stack)
            return

        for v in n.values():
            walk(v, stack)

    # Try common roots
    if ast.get('kind') == 'Instance':
        walk(ast, [])
    else:
        design = ast.get('design') or {}
        walk(design.get('members') or [], [])

    # de-dupe keep order
    seen = set()
    uniq = []
    for p in paths:
        if p not in seen:
            seen.add(p)
            uniq.append(p)
    return uniq


# ──────────────────────────────────────────────────────────────────────────────
# SpecBuilder
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
        scope_path: Optional[str] = None,
        discover_scope_module: Optional[str] = None,
        discover_only: bool = False,
    ):
        self.slang_bin = slang_bin
        self.rtl_dir = rtl_dir
        self.top = top  # spec target module name (load_unit)
        self.design_top = design_top or top  # design top (cva6)
        self.out_dir = out_dir
        self.llm_conf = llm_conf
        self.include_dirs = include_dirs or []
        self.defines = defines or []
        self.disable_analysis = disable_analysis
        self.filelist = filelist
        self.scope_path = scope_path
        self.discover_scope_module = discover_scope_module
        self.discover_only = discover_only

        _ensure_dir(self.out_dir)

        # AST output (scoped vs full)
        self.out_json = self.out_dir / (f'{self.top}_scoped_ast.json' if self.scope_path else f'{self.top}_ast.json')
        self.full_ast_json = self.out_dir / f'{self.design_top}_full_ast.json'

        # primary outputs
        self.out_md = self.out_dir / f'{self.top}_spec.md'
        self.out_csv = self.out_dir / f'{self.top}_spec.csv'
        self.logic_snap = self.out_dir / f'{self.top}_logic_blocks.json'

        # IR outputs
        self.ports_json = self.out_dir / f'{self.top}_ports.json'
        self.assignments_jsonl = self.out_dir / f'{self.top}_assignments.jsonl'
        self.io_relations_json = self.out_dir / f'{self.top}_io_relations.json'
        self.io_influence_csv = self.out_dir / f'{self.top}_io_influence.csv'

        if not self.llm_conf.exists():
            console.print(f'[red]❌ LLM config not found: {self.llm_conf}[/red]')
            raise SystemExit(2)

        console.print(f'[cyan][LLM] Using config:[/cyan] {self.llm_conf}')
        self.llm = LLM_wrap(name='default', conf_file=str(self.llm_conf), log_file='spec_llm.log')
        self.tmpl = LLM_template(str(self.llm_conf))
        self.template_dict = getattr(self.tmpl, 'template_dict', {}) or {}

        # Required prompts in your YAML
        for req in ('doc_sections', 'fsm_specification', 'sva_row_list_csv'):
            if not (self.template_dict.get('default', {}).get(req)):
                console.print(f"[red]❌ Required prompt '{req}' missing in: {self.llm_conf}[/red]")
                raise SystemExit(2)

        # clock/reset from design top
        self.clk, self.rst, self.rst_expr = detect_clk_rst_for_top(self.rtl_dir, self.design_top)

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
        except Exception as e:
            console.print(f"[red]❌ LLM '{prompt_index}' failed: {e}[/red]")
            return ''

    def _repair_csv_with_llm(self, csv_text: str, allowed_ports: List[str], report: Dict[str, Any]) -> str:
        if not self.template_dict.get('default', {}).get('csv_repair'):
            console.print("[yellow]⚠ No 'csv_repair' prompt found in YAML; cannot repair CSV.[/yellow]")
            return csv_text
        payload = {
            'top_module': self.top,
            'allowed_ports_json': json.dumps(allowed_ports, ensure_ascii=False),
            'csv_text': csv_text,
            'validation_json': json.dumps(report, ensure_ascii=False),
        }
        fixed = self._llm('csv_repair', payload)
        return _ensure_csv_header(_strip_code_fences(fixed))

    def _read_json(self, p: Path) -> Dict[str, Any]:
        return json.loads(p.read_text(encoding='utf-8'))

    def _run_slang(self, out_json: Path, full: bool) -> None:
        """
        If full=True: build full AST for design_top (no scope)
        Else: if scope_path is set, build scoped AST for design_top + scope_path
        """
        top_for_slang = self.design_top if (full or self.scope_path) else self.top

        cmd = [
            str(self.slang_bin),
            '--top',
            str(top_for_slang),
            '--ast-json',
            str(out_json),
            '--ast-json-source-info',
            '--ignore-unknown-modules',
            '--allow-use-before-declare',
            '--diag-abs-paths',
        ]
        if self.disable_analysis:
            cmd.append('--disable-analysis')

        if (not full) and self.scope_path:
            cmd += ['--ast-json-scope', self.scope_path]

        for inc in self.include_dirs:
            cmd += ['-I', str(inc)]
        for d in self.defines:
            cmd.append(f'--define={d}')

        if self.filelist:
            cmd += ['-f', str(self.filelist)]
        else:
            # fallback: enumerate RTL files
            files = []
            for p in self.rtl_dir.rglob('*'):
                if p.suffix.lower() in SV_SUFFIXES and p.is_file():
                    files.append(p)
            if not files:
                console.print(f'[red]❌ No RTL files found under: {self.rtl_dir}[/red]')
                raise SystemExit(2)
            cmd += [str(f) for f in sorted(files)]

        console.print('[cyan]• Running Slang to emit AST JSON[/cyan]')
        console.print('  ' + ' '.join(cmd))
        res = subprocess.run(cmd)
        if res.returncode != 0 or not out_json.exists():
            console.print(f'[red]❌ Slang failed (code={res.returncode}); AST not produced: {out_json}[/red]')
            raise SystemExit(2)
        console.print(f'[green]✔ AST written:[/green] {out_json}')

    def _get_scoped_body(self, ast: Dict[str, Any]) -> Tuple[Dict[str, Any], str]:
        """
        In scoped runs, Slang often returns:
          - root.kind == "Instance"  -> body is InstanceBody of the scoped instance
        In other runs, it may wrap under design.members.
        """
        if isinstance(ast, dict) and ast.get('kind') == 'Instance':
            body = ast.get('body') or {}
            inst = ast.get('name') or self.top
            if not isinstance(body, dict):
                raise SystemExit(2)
            return body, inst

        # fallback: search for instance whose definition matches target module
        design = ast.get('design') or {}
        members = design.get('members') or []
        found_body = None
        found_name = self.top

        def rec(n: Any) -> None:
            nonlocal found_body, found_name
            if found_body is not None:
                return
            if n is None or _is_invalid_node(n):
                return
            if isinstance(n, list):
                for it in n:
                    rec(it)
                return
            if not isinstance(n, dict):
                return
            if n.get('kind') == 'Instance':
                b = n.get('body') or {}
                defn = b.get('definition') if isinstance(b, dict) else ''
                if defn and (
                    defn.endswith('.' + self.top) or defn.endswith('work.' + self.top) or defn.endswith('::' + self.top)
                ):
                    found_body = b
                    found_name = n.get('name') or self.top
                    return
                if isinstance(b, dict):
                    rec(b.get('members') or [])
            for v in n.values():
                rec(v)

        rec(members)
        if found_body is None:
            console.print(f"[red]❌ Could not locate target '{self.top}' in AST. Provide --scope-path or use discovery.[/red]")
            raise SystemExit(2)
        return found_body, found_name

    def _write_ir_outputs(self, ports: List[Dict[str, str]], assigns: List[AssignRecord], io_rel: Dict[str, Any]) -> None:
        _write_json(self.ports_json, ports)
        console.print(f'[green]✔ ports.json:[/green] {self.ports_json}')

        _write_jsonl(
            self.assignments_jsonl,
            [
                {
                    'assign_id': a.assign_id,
                    'kind': a.kind,
                    'proc_kind': a.proc_kind,
                    'lhs': a.lhs_text,
                    'rhs': a.rhs_text,
                    'defs': a.defs,
                    'uses': a.uses,
                    'guards': a.guards,
                    'block_path': a.block_path,
                    'src_file': a.src_file,
                    'src_ls': a.src_ls,
                    'src_le': a.src_le,
                }
                for a in assigns
            ],
        )
        console.print(f'[green]✔ assignments.jsonl:[/green] {self.assignments_jsonl}')

        _write_json(self.io_relations_json, io_rel)
        console.print(f'[green]✔ io_relations.json:[/green] {self.io_relations_json}')

        # io influence CSV (flatten per_output_influences)
        with self.io_influence_csv.open('w', newline='', encoding='utf-8') as f:
            w = csv.writer(f)
            w.writerow(['output', 'inputs', 'guards', 'effect', 'block_kind', 'src'])
            for r in io_rel.get('relationships', {}).get('per_output_influences') or []:
                w.writerow(
                    [
                        r.get('output', ''),
                        ' '.join(r.get('inputs') or []),
                        r.get('guards', ''),
                        r.get('effect', ''),
                        r.get('block_kind', ''),
                        r.get('src', ''),
                    ]
                )
        console.print(f'[green]✔ io_influence.csv:[/green] {self.io_influence_csv}')

    def run(self) -> None:
        # 0) optional scope discovery
        if self.discover_scope_module:
            console.print(f'[cyan]• Discovering scope paths for module:[/cyan] {self.discover_scope_module}')
            self._run_slang(self.full_ast_json, full=True)
            full_ast = self._read_json(self.full_ast_json)
            paths = find_instance_paths(full_ast, self.discover_scope_module)
            if not paths:
                console.print(f"[red]❌ No instance paths found for module '{self.discover_scope_module}'.[/red]")
                raise SystemExit(2)
            console.print('[green]✔ Found scope paths:[/green]')
            for p in paths:
                console.print('  ' + p)
            if self.discover_only:
                return
            if not self.scope_path:
                self.scope_path = paths[0]
                console.print(f'[cyan]• Auto-selected scope:[/cyan] {self.scope_path}')

            # update output filename for scoped ast
            self.out_json = self.out_dir / f'{self.top}_scoped_ast.json'

        # 1) produce scoped (or unscoped) AST
        self._run_slang(self.out_json, full=False)

        # 2) parse target body
        ast = self._read_json(self.out_json)
        body, inst_name = self._get_scoped_body(ast)

        # 3) extract ports/params/logic/fsms/assignments
        ports = extract_ports_from_body(body)
        if not ports:
            console.print('[red]❌ No ports extracted. Check --scope-path (or discovery results).[/red]')
            raise SystemExit(2)

        params = extract_parameters_from_body(body)
        assigns = extract_assignments_with_guards(body)
        logic = extract_logic_blocks(body)
        fsms = parse_case_blocks(body)

        _write_json(self.logic_snap, logic)
        console.print(f'[green]✔ logic_blocks.json:[/green] {self.logic_snap}')

        io_relations = build_io_relations(ports, assigns, max_depth=6)
        self._write_ir_outputs(ports, assigns, io_relations)

        allowed_ports = [p['name'] for p in ports]

        # 4) prepare LLM context JSON (MATCHES YOUR PROMPT KEYS)
        fsm_summaries: List[Dict[str, Any]] = []
        for b in fsms:
            rtl = ''
            if b['source_file'] and b['line_start'] and b['line_end']:
                rtl = _extract_rtl_excerpt(b['source_file'], int(b['line_start']), int(b['line_end']), max_chars=4000)
            fsm_summaries.append(
                {
                    'expr_symbol': b['expr_symbol'],
                    'source': _basename(b['source_file']),
                    'line_start': b['line_start'],
                    'line_end': b['line_end'],
                    'rtl_excerpt': rtl,
                }
            )

        context = {
            'top_module': self.top,
            'design_top': self.design_top,
            'instance_name': inst_name,
            'scope_path': self.scope_path or '',
            'clock': self.clk,
            'reset': self.rst,
            'reset_expr': self.rst_expr,
            'ports': ports,
            'allowed_signals': allowed_ports,
            'params': params,
            'io_relations': io_relations,  # <-- your sva_row_list_csv expects this
            'fsms': fsm_summaries,
            'logic_blocks': logic[:200],
        }

        # 5) Markdown generation
        md_parts: List[str] = []
        console.print('[cyan]• LLM: doc_sections[/cyan]')
        md_doc = self._llm('doc_sections', {'context_json': json.dumps(context, ensure_ascii=False)})
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
            for blk in fsm_summaries:
                console.print(f'[cyan]• LLM: fsm_specification ({blk.get("expr_symbol")})[/cyan]')
                fsm_json = {
                    'module': self.top,
                    'expr_symbol': blk.get('expr_symbol') or 'state',
                    'source_file': blk.get('source'),
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
                        'rtl_code': blk.get('rtl_excerpt') or '',
                    },
                )
                if md_fsm.strip():
                    md_parts.append(md_fsm.strip())

        md_text = '\n\n'.join([p for p in md_parts if p.strip()]) or f'## Spec for Module: {self.top}\n'
        _write_text(self.out_md, md_text)
        console.print(f'[green]✔ Spec Markdown:[/green] {self.out_md}')

        # 6) CSV generation + validate + repair
        console.print('[cyan]• LLM: sva_row_list_csv[/cyan]')
        csv_raw = self._llm('sva_row_list_csv', {'context_json': json.dumps(context, ensure_ascii=False)}).strip()
        csv_raw = _ensure_csv_header(_strip_code_fences(csv_raw))
        if not csv_raw.strip():
            console.print('[red]❌ LLM produced empty CSV text.[/red]')
            raise SystemExit(2)

        report = validate_csv_text(csv_raw, allowed_ports)
        report_path = self.out_dir / f'{self.top}_spec.csv.validation.json'
        _write_json(report_path, report)

        if not report.get('ok', False):
            console.print('[yellow]⚠ CSV validation failed. Attempting repair...[/yellow]')
            broken_path = self.out_dir / f'{self.top}_spec.csv.broken'
            _write_text(broken_path, csv_raw)

            repaired = csv_raw
            for attempt in range(1, 3):
                repaired = self._repair_csv_with_llm(repaired, allowed_ports, report)
                report = validate_csv_text(repaired, allowed_ports)
                _write_json(report_path, report)
                if report.get('ok', False):
                    console.print(f'[green]✔ CSV repaired on attempt {attempt}.[/green] Broken backup: {broken_path}')
                    csv_raw = repaired
                    break
                console.print(f'[yellow]⚠ Repair attempt {attempt} still invalid.[/yellow]')

            if not report.get('ok', False):
                _write_text(self.out_csv, repaired)
                console.print(f'[red]❌ CSV still invalid after repair attempts. Wrote latest to: {self.out_csv}[/red]')
                console.print(f'[red]Validation report: {json.dumps(report, indent=2)}[/red]')
                raise SystemExit(2)

        _write_text(self.out_csv, csv_raw)
        console.print(f'[green]✔ CSV spec:[/green] {self.out_csv}')
        console.print('[bold green]✅ SPEC BUILDER COMPLETED[/bold green]')
