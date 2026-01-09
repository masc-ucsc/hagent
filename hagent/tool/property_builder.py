#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
property_builder.py
-------------------
Generate SystemVerilog properties (assert/assume/cover) from a CSV spec.

KEY FIX (Dec 2025): top != sva_top clock/reset mismatch
  - Properties must be written in the *SVA module* clock/reset domain (the module you bind into),
    NOT the elaboration top's clock/reset.
    Example: top=i2c, sva_top=fifo
      * i2c clock is PCLK, fifo clock port is 'clock'
      * properties.sv must use @(posedge clock) ... inside fifo scope
  - Therefore, by default we detect clk/rst for 'property_top' (aka SVA module),
    which defaults to spec_top inferred from <spec_md> filename (e.g. fifo_spec.md -> fifo).

PORTS.JSON (preferred):
  - Prefer <property_top>_ports.json for:
      * allowed signal list
      * clk/rst detection for property clocking

ROBUST FORMAL RULES (Dec 2025, hardened):
  - Treat pre == '' or '1' or '1'b1' as NO-PRE (never invent/keep pre=1).
  - If NO-PRE and post exists => emit POST ONLY (no implication).
  - If ONLY-PRE (post empty) => emit PRE ONLY (no implication).
  - If BOTH pre and post empty => skip row (do not write property).
  - COVER: never generate cover(1'b1); if no pre and no post => skip.
  - CSV robustness:
      * Accept 9-column rows missing 'post' (insert post='').
      * If >10 cols, merge extras into notes.
      * If header missing/bad, still try best-effort parse.
  - Keep earlier safety fixes:
      * allow $rose/$fell/$stable/$changed/$past in identifier checks
      * avoid nested temporal wrappers
      * lift implications found inside post into pre
      * rewrite temporal boolean mixes into sequence operators 'and/or'
      * prefer <property_top>_ports.json if available

STRICT MODE:
  - Write a JSON report with:
      * CSV parse repairs/drops
      * per-row repairs (implication lifting, temporal-mix rewrite, pre-clearing)
      * per-row skip reasons (empty, invalid identifiers, tautology, etc.)
      * summary counts and ports source
"""

from __future__ import annotations

import os
import re
import csv
import json
from pathlib import Path
from typing import List, Dict, Optional, Tuple, Any

from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

try:
    from hagent.core.llm_wrap import LLM_wrap
except Exception:
    LLM_wrap = None


# -----------------------------------------------------------------------------
# Constants / Helpers
# -----------------------------------------------------------------------------
_ALLOWED_SVA_FUNCS = {'$stable', '$changed', '$past', '$rose', '$fell'}
_IMP_OPS = ('|->', '|=>')
CSV_HEADER = ['sid', 'prop_type', 'module', 'name', 'scenario', 'pre', 'post', 'signals', 'param_ok', 'notes']


def _strip_sv_comments(s: str) -> str:
    s = re.sub(r'//.*?$', '', s, flags=re.M)
    s = re.sub(r'/\*.*?\*/', '', s, flags=re.S)
    return s


def _split_csv_line(line: str) -> List[str]:
    r = csv.reader([line], skipinitialspace=True)
    return [c.strip() for c in next(r, [])]


def _is_trivial_true(expr: str) -> bool:
    e = (expr or '').strip()
    return e in {'1', "1'b1", "1'b01", "1'h1"}


def _split_first_implication(expr: str) -> Optional[Tuple[str, str, str]]:
    if not expr:
        return None
    for op in _IMP_OPS:
        idx = expr.find(op)
        if idx >= 0:
            ante = expr[:idx].strip()
            cons = expr[idx + len(op) :].strip()
            return ante, op, cons
    return None


def _rewrite_temporal_mix_to_sequence_ops(post: str) -> Tuple[str, bool]:
    """
    If post contains '##' then using boolean operators like '|', '||', '&', '&&'
    often creates illegal syntax (boolean vs sequence). Convert to sequence ops.
    Returns (rewritten_post, changed_flag).
    """
    p0 = (post or '').strip()
    if '##' not in p0:
        return p0, False
    if '|->' in p0 or '|=>' in p0:
        return p0, False

    p = p0
    p = re.sub(r'\s\|\|\s', ' or ', p)
    p = re.sub(r'\s\|\s', ' or ', p)
    p = re.sub(r'\s&&\s', ' and ', p)
    p = re.sub(r'\s&\s', ' and ', p)
    p = p.strip()
    return p, (p != p0)


def _parse_csv_best_effort(raw_text: str) -> Tuple[List[Dict[str, str]], Dict[str, Any]]:
    """
    Best-effort CSV parser that never throws and returns (rows, parse_report).
    - Accept 9-col rows missing post: insert post=''
    - Merge >10 cols into notes
    - If header missing/wrong: treat first line as data and synthesize header
    """
    parse_report: Dict[str, Any] = {
        'header_ok': False,
        'header_was_synthesized': False,
        'raw_lines': 0,
        'kept_rows': 0,
        'dropped_rows': 0,
        'repairs': [],
        'dropped': [],
    }

    lines = (raw_text or '').splitlines()
    parse_report['raw_lines'] = len(lines)

    nonblank: List[Tuple[int, str]] = [(i + 1, ln) for i, ln in enumerate(lines) if (ln or '').strip()]
    if not nonblank:
        return [], parse_report

    ln0_no, ln0 = nonblank[0]
    first = (ln0 or '').strip().lower().replace(' ', '')
    expected = ','.join(CSV_HEADER).lower().replace(' ', '')
    data_start_idx = 1

    if first == expected:
        parse_report['header_ok'] = True
        parse_report['header_was_synthesized'] = False
    else:
        parse_report['header_ok'] = False
        parse_report['header_was_synthesized'] = True
        data_start_idx = 0

    rows: List[Dict[str, str]] = []

    for lineno, line in nonblank[data_start_idx:]:
        cols = _split_csv_line(line)

        if len(cols) > 10:
            base9 = cols[:9]
            extra = ' '.join((c or '').replace(',', ' ').strip() for c in cols[9:]).strip()
            cols = base9 + [extra]
            parse_report['repairs'].append(
                {
                    'line': lineno,
                    'kind': 'merge_extra_columns_into_notes',
                    'original_cols': len(_split_csv_line(line)),
                    'final_cols': len(cols),
                }
            )

        if len(cols) == 9:
            # sid,prop_type,module,name,scenario,pre,signals,param_ok,notes
            sid, prop_type, module, name, scenario, pre, signals, param_ok, notes = cols
            post = ''
            cols = [sid, prop_type, module, name, scenario, pre, post, signals, param_ok, notes]
            parse_report['repairs'].append(
                {
                    'line': lineno,
                    'kind': 'insert_missing_post_column',
                }
            )

        if len(cols) != 10:
            parse_report['dropped_rows'] += 1
            parse_report['dropped'].append(
                {
                    'line': lineno,
                    'kind': 'unfixable_column_count',
                    'cols': len(cols),
                    'text': line,
                }
            )
            continue

        row = {CSV_HEADER[i]: (cols[i] or '').strip() for i in range(10)}
        row['_line'] = str(lineno)
        rows.append(row)

    parse_report['kept_rows'] = len(rows)
    return rows, parse_report


def _load_ports_from_ports_json(candidate_paths: List[Path]) -> Tuple[List[str], str]:
    """
    Returns (ports, source_path_or_empty)
    """
    for p in candidate_paths:
        if not p or not p.exists():
            continue
        try:
            data = json.loads(p.read_text(encoding='utf-8'))
            if isinstance(data, list):
                names: List[str] = []
                for item in data:
                    if isinstance(item, dict) and item.get('name'):
                        names.append(str(item['name']).strip())
                # de-dup preserve order
                out: List[str] = []
                seen = set()
                for n in names:
                    if n and n not in seen:
                        out.append(n)
                        seen.add(n)
                if out:
                    return out, str(p)
        except Exception:
            pass
    return [], ''


def detect_top_ports_from_rtl(rtl_dir: str, top: str) -> List[str]:
    rtl_dir_path = Path(rtl_dir)
    top_esc = re.escape(top)

    mod_re = re.compile(
        rf'\bmodule\s+{top_esc}\b[\s\S]*?\((?P<ports>[\s\S]*?)\)\s*;',
        re.MULTILINE,
    )

    for sv in rtl_dir_path.rglob('*'):
        if sv.suffix not in {'.sv', '.v', '.svh', '.vh'}:
            continue
        try:
            txt = sv.read_text(encoding='utf-8', errors='ignore')
        except Exception:
            continue

        m = mod_re.search(txt)
        if not m:
            continue

        port_block = _strip_sv_comments(m.group('ports') or '')

        parts: List[str] = []
        buf = []
        depth = 0
        for ch in port_block:
            if ch == '(':
                depth += 1
            elif ch == ')':
                depth = max(0, depth - 1)
            if ch == ',' and depth == 0:
                parts.append(''.join(buf).strip())
                buf = []
            else:
                buf.append(ch)
        if buf:
            parts.append(''.join(buf).strip())

        ports: List[str] = []
        for p in parts:
            if not p:
                continue
            p2 = re.sub(r'\[[^\]]+\]', ' ', p)
            toks = re.findall(r'\b[A-Za-z_]\w*\b', p2)
            if not toks:
                continue

            blacklist = {
                'input',
                'output',
                'inout',
                'wire',
                'logic',
                'reg',
                'signed',
                'unsigned',
                'parameter',
                'localparam',
                'typedef',
                'struct',
                'union',
                'enum',
            }
            name = None
            for t in reversed(toks):
                if t.lower() in blacklist:
                    continue
                name = t
                break
            if name and name not in ports:
                ports.append(name)

        if ports:
            return ports

    return []


def _detect_clk_rst_from_port_names(
    port_names: List[str],
    clock_override: Optional[str] = None,
    reset_override: Optional[str] = None,
    reset_expr_override: Optional[str] = None,
) -> Tuple[str, str, str, str]:
    """
    Heuristic clk/rst detection from a port-name list.
    Returns (clk, rst, rst_expr, source_tag).

    reset_expr:
      - if override provided -> use it verbatim
      - else:
          * active-low name endings ('n', '_n', 'ni', '_ni') -> '!<rst>'
          * otherwise -> '<rst>'
    """
    if reset_expr_override and reset_expr_override.strip():
        # even if rst unknown, allow user expression
        return (clock_override or '', reset_override or '', reset_expr_override.strip(), 'user_override_reset_expr')

    ports = [p for p in (port_names or []) if p and p.strip()]
    # de-dupe preserve order
    seen = set()
    puniq = []
    for p in ports:
        if p not in seen:
            puniq.append(p)
            seen.add(p)
    ports = puniq

    clk = (clock_override or '').strip()
    rst = (reset_override or '').strip()

    if not clk:
        clk_patterns = [
            r'^clk$',
            r'^clock$',
            r'^pclk$',
            r'^aclk$',
            r'.*clk.*',
            r'.*clock.*',
        ]
        clk_best = ''
        clk_best_rank = None
        for p in ports:
            pl = p.lower()
            for i, pat in enumerate(clk_patterns):
                if re.match(pat, pl):
                    if clk_best_rank is None or i < clk_best_rank:
                        clk_best = p
                        clk_best_rank = i
                    break
        clk = clk_best

    if not rst:
        rst_patterns = [
            r'^rst$',
            r'^reset$',
            r'^resetn$',
            r'^rst_n$',
            r'^reset_n$',
            r'^reset_ni$',
            r'^rst_ni$',
            r'.*reset.*',
            r'.*rst.*',
        ]
        rst_best = ''
        rst_best_rank = None
        for p in ports:
            pl = p.lower()
            for i, pat in enumerate(rst_patterns):
                if re.match(pat, pl):
                    if rst_best_rank is None or i < rst_best_rank:
                        rst_best = p
                        rst_best_rank = i
                    break
        rst = rst_best

    rst_expr = ''
    if rst:
        low = rst.lower()
        is_active_low = low.endswith('n') or low.endswith('_n') or low.endswith('ni') or low.endswith('_ni')
        rst_expr = f'!{rst}' if is_active_low else rst

    return clk, rst, rst_expr, 'ports_name_heuristic'


# -----------------------------------------------------------------------------
# Property Builder
# -----------------------------------------------------------------------------
class PropertyBuilder:
    def __init__(
        self,
        spec_md: str,
        csv_path: str,
        rtl_dir: str,
        out_dir: str,
        llm_conf: Optional[str],
        design_top: Optional[str] = None,
        property_top: Optional[str] = None,  # NEW: module where properties are clocked (SVA/bind target)
        clock_name: Optional[str] = None,  # NEW: override property clock name
        reset_name: Optional[str] = None,  # NEW: override property reset name
        reset_expr: Optional[str] = None,  # NEW: override disable iff expression
        strict: bool = False,
        report_json: Optional[str] = None,
    ):
        self.spec_md = os.path.abspath(spec_md)
        self.csv_path = os.path.abspath(csv_path)
        self.rtl_dir = os.path.abspath(rtl_dir)
        self.out_dir = os.path.abspath(out_dir)
        os.makedirs(self.out_dir, exist_ok=True)

        self.llm_conf = os.path.abspath(llm_conf) if llm_conf else None

        # 'design_top' is the ELAB top (useful for TCL scripts), but properties should be in property_top domain.
        self.design_top = design_top

        self.property_top = (property_top or '').strip() or None
        self.clock_name_override = (clock_name or '').strip() or None
        self.reset_name_override = (reset_name or '').strip() or None
        self.reset_expr_override = (reset_expr or '').strip() or None

        self.strict = bool(strict)
        self.report_json = os.path.abspath(report_json) if report_json else os.path.join(self.out_dir, 'properties.report.json')

        self.llm = None
        if LLM_wrap and self.llm_conf and os.path.exists(self.llm_conf):
            print(f'[LLM] Using config: {self.llm_conf}')
            try:
                self.llm = LLM_wrap(
                    name='default',
                    conf_file=self.llm_conf,
                    log_file='property_llm.log',
                )
            except Exception as e:
                print(f'[WARN] LLM init failed: {e}. Falling back to rule-based generation.')
                self.llm = None
        else:
            print('[WARN] LLM disabled (LLM_wrap missing or llm_conf missing). Using rule-based generation.')

    # ------------------------------------------------------------------
    @staticmethod
    def _fmt(s: Optional[str]) -> str:
        if s is None:
            return ''
        return str(s).replace('{', '{{').replace('}', '}}')

    # ------------------------------------------------------------------
    def _read_csv_rows(self) -> Tuple[List[Dict[str, str]], Dict[str, Any]]:
        try:
            raw = Path(self.csv_path).read_text(encoding='utf-8', errors='ignore')
        except Exception:
            raw = ''
        rows, parse_report = _parse_csv_best_effort(raw)

        out: List[Dict[str, str]] = []
        for r in rows:
            clean = {k: self._fmt((v or '').strip()) for k, v in r.items()}
            out.append(clean)

        print(f'[DEBUG] Loaded {len(out)} CSV rows (robust parse).')
        return out, parse_report

    # ------------------------------------------------------------------
    def _read_markdown(self) -> str:
        try:
            txt = Path(self.spec_md).read_text(encoding='utf-8', errors='ignore')
        except Exception:
            txt = ''
        return self._fmt(txt)

    # ------------------------------------------------------------------
    def _infer_spec_top(self) -> str:
        stem = Path(self.spec_md).stem
        if '_spec' in stem:
            return stem.split('_spec')[0]
        return stem

    # ------------------------------------------------------------------
    def _ports_json_candidates_for(self, mod_name: str) -> List[Path]:
        return [
            Path(self.out_dir) / f'{mod_name}_ports.json',
            Path(self.csv_path).parent / f'{mod_name}_ports.json',
            Path(self.spec_md).parent / f'{mod_name}_ports.json',
        ]

    # ------------------------------------------------------------------
    def _find_ports(self, mod_name: str, rows: List[Dict[str, str]]) -> Tuple[List[str], str]:
        ports, ports_src = _load_ports_from_ports_json(self._ports_json_candidates_for(mod_name))
        if ports:
            return ports, ports_src

        ports = detect_top_ports_from_rtl(self.rtl_dir, mod_name)
        if ports:
            return ports, 'rtl_module_header_fallback'

        # final fallback: infer from CSV signals column
        ports = []
        for r in rows:
            sigs = (r.get('signals') or '').strip()
            for tok in re.split(r'[\s,]+', sigs):
                tok = tok.strip()
                if tok and tok not in ports:
                    ports.append(tok)
        return ports, 'csv_signals_fallback'

    # ------------------------------------------------------------------
    def _find_clk_rst(self, rows: List[Dict[str, str]]) -> Tuple[str, str, str, str, str]:
        """
        Returns (clk, rst, disable_cond, spec_top, prop_top_used)
        """
        spec_top = self._infer_spec_top()
        prop_top = self.property_top or spec_top

        # Prefer ports.json for *property_top* to pick clk/rst in that module domain
        ports_for_prop, _ports_src = self._find_ports(prop_top, rows)

        clk, rst, rst_expr, cr_src = _detect_clk_rst_from_port_names(
            ports_for_prop,
            clock_override=self.clock_name_override,
            reset_override=self.reset_name_override,
            reset_expr_override=self.reset_expr_override,
        )

        # If heuristics didn't find anything and no overrides, fallback to clk_rst_utils
        if (not clk or not rst) and (
            not self.clock_name_override and not self.reset_name_override and not self.reset_expr_override
        ):
            try:
                cr = detect_clk_rst_for_top(
                    Path(self.rtl_dir), prop_top, ports_json=Path(self.out_dir) / f'{prop_top}_ports.json'
                )
                if isinstance(cr, (list, tuple)) and len(cr) >= 3:
                    clk2, rst2, rst_expr2 = cr[0], cr[1], cr[2]
                    if not clk and clk2:
                        clk = str(clk2)
                    if not rst and rst2:
                        rst = str(rst2)
                    if (not rst_expr or not rst_expr.strip()) and rst_expr2:
                        rst_expr = str(rst_expr2)
                    cr_src = 'clk_rst_utils_fallback'
            except Exception:
                pass

        disable_cond = (rst_expr or '').strip()
        if not disable_cond and rst:
            low = rst.lower()
            is_active_low = low.endswith('n') or low.endswith('_n') or low.endswith('ni') or low.endswith('_ni')
            disable_cond = f'!{rst}' if is_active_low else rst

        print(
            f'[INFO] Property clock/reset domain (property_top="{prop_top}"): clk={clk or "-"}, rst={rst or "-"}, disable iff ({disable_cond or "-"}) [{cr_src}]'
        )
        if self.design_top and self.design_top != prop_top:
            print(
                f'[INFO] Note: design_top="{self.design_top}" differs from property_top="{prop_top}" (expected when top!=sva_top).'
            )

        return clk, rst, disable_cond, spec_top, prop_top

    # ------------------------------------------------------------------
    @staticmethod
    def _extract_sv_code(text: str) -> str:
        if not text:
            return ''
        m = re.search(r'```(?:systemverilog|sv|verilog)?\s*([\s\S]*?)```', text, re.I)
        if m:
            return m.group(1).strip()
        return text.strip()

    # ------------------------------------------------------------------
    @staticmethod
    def _normalize_csv_expr(expr: str, ports: List[str]) -> str:
        e = (expr or '').strip()
        if not e:
            return ''

        if e == '1':
            return "1'b1"
        if e == '0':
            return "1'b0"

        # Simple english normalizations (keep minimal)
        m = re.match(r'^([A-Za-z_]\w*)\s+stable\s+for\s+1\s+cycle$', e, re.I)
        if m:
            return f'$stable({m.group(1)})'

        m = re.match(r'^([A-Za-z_]\w*)\s+changes$', e, re.I)
        if m:
            return f'$changed({m.group(1)})'

        if e.lower().endswith(' changes'):
            sig = e[:-8].strip()
            if sig in ports:
                return f'$changed({sig})'

        m = re.match(r'^stable\(([\s\S]+)\)$', e, re.I)
        if m:
            return f'$stable({m.group(1).strip()})'

        return e

    # ------------------------------------------------------------------
    @staticmethod
    def _expr_uses_only_ports(expr: str, ports: List[str]) -> bool:
        """
        Allow:
          - ports
          - dotted field names (anything after a '.')
          - $rose/$fell/$stable/$changed/$past
          - SV keywords/operators tokens that appear as identifiers
        """
        if not (expr or '').strip():
            return False

        allowed_ids = set(ports) | {
            'if',
            'else',
            'and',
            'or',
            'not',
            'posedge',
            'negedge',
            'disable',
            'iff',
            # $funcs are in the raw text as '$rose', but regex sees 'rose' too (handled below)
            *list(_ALLOWED_SVA_FUNCS),
        }

        for m in re.finditer(r'\b[A-Za-z_]\w*\b', expr):
            t = m.group(0)

            if t in allowed_ids:
                continue

            if re.match(r'^[A-Z0-9_]+$', t):
                continue

            idx = m.start()

            # Allow system functions: '$rose' -> regex sees 'rose' preceded by '$'
            if idx > 0 and expr[idx - 1] == '$':
                if ('$' + t) in allowed_ids:
                    continue

            # Allow field names after dot
            if idx > 0 and expr[idx - 1] == '.':
                continue

            return False

        return True

    # ------------------------------------------------------------------
    @staticmethod
    def _fix_reset_deassertion(row: Dict[str, str], rst: str) -> None:
        name = (row.get('name') or '').lower()
        scen = (row.get('scenario') or '').lower()
        post = (row.get('post') or '').strip()

        if 'deassert' in name or 'deassert' in scen:
            if (rst.endswith('_ni') or rst.endswith('ni') or rst.endswith('_n')) and post in (f'!{rst}', f'! {rst}'):
                row['post'] = rst

    # ------------------------------------------------------------------
    @staticmethod
    def _wrap_property(
        sid: str,
        name: str,
        ptype: str,
        clk: str,
        disable_cond: str,
        body_expr: str,
    ) -> str:
        # Use SID as property name to guarantee uniqueness (avoids duplicate property names)
        prop_name = sid.replace('-', '_').lower()
        # Keep human-readable name in comment
        label = f'{ptype}_{prop_name}'.replace('-', '_')

        if ptype not in {'assert', 'assume', 'cover'}:
            ptype = 'assert'

        body_expr_fixed = re.sub(r'\bor\b', '||', body_expr)
        body_expr_fixed = re.sub(r'\band\b', '&&', body_expr_fixed)

        # If clk is missing, we must still emit something deterministic -> block generation caller should have prevented.
        return (
            f'// {sid}: {name or prop_name}\n'
            f'property {prop_name};\n'
            f'  @(posedge {clk}) disable iff ({disable_cond})\n'
            f'    {body_expr_fixed};\n'
            f'endproperty\n'
            f'{label}: {ptype} property({prop_name});'
        )

    # ------------------------------------------------------------------
    @staticmethod
    def _post_has_temporal(post: str) -> bool:
        p = (post or '').strip()
        return ('##' in p) or ('[*' in p) or ('[->' in p) or ('throughout' in p)

    # ------------------------------------------------------------------
    @staticmethod
    def _pre_is_missing(pre_raw: str, pre_norm: str) -> bool:
        """
        Treat empty / 1 / 1'b1 as 'no real precondition'.
        """
        if (pre_raw or '').strip() in {'', '1', "1'b1"}:
            return True
        return _is_trivial_true(pre_norm)

    # ------------------------------------------------------------------
    def _repair_pre_post_from_csv(
        self,
        pre_raw: str,
        post_raw: str,
        ports: List[str],
        scenario: str = '',
    ) -> Tuple[str, str, Dict[str, Any]]:
        meta: Dict[str, Any] = {
            'lifted_implications': 0,
            'temporal_mix_rewritten': False,
            'cleared_trivial_pre': False,
            'dropped_implication_in_pre': False,
        }

        pre0 = (pre_raw or '').strip()
        post0 = (post_raw or '').strip()

        pre = self._normalize_csv_expr(pre_raw, ports)
        post = self._normalize_csv_expr(post_raw, ports)

        while True:
            spl = _split_first_implication(post)
            if not spl:
                break
            ante, _op, cons = spl
            if not ante or not cons:
                break
            if not pre.strip() or _is_trivial_true(pre.strip()):
                pre = ante
            else:
                pre = f'({pre}) && ({ante})'
            post = cons
            meta['lifted_implications'] += 1

        # If implication exists in pre (shouldn't), drop it (safer than generating invalid SVA)
        if '|->' in pre or '|=>' in pre:
            # keep only antecedent part
            spl = _split_first_implication(pre)
            if spl:
                pre = spl[0].strip()
                meta['dropped_implication_in_pre'] = True

        post2, changed = _rewrite_temporal_mix_to_sequence_ops(post)
        post = post2
        meta['temporal_mix_rewritten'] = bool(changed)

        if pre0 in {'1', "1'b1"} or _is_trivial_true(pre.strip()):
            if pre.strip():
                meta['cleared_trivial_pre'] = True
            pre = ''

        meta['pre_raw'] = pre0
        meta['post_raw'] = post0
        meta['pre_norm'] = pre.strip()
        meta['post_norm'] = post.strip()
        meta['scenario'] = (scenario or '').strip().lower()

        return pre.strip(), post.strip(), meta

    # ------------------------------------------------------------------
    def _rule_based_property_from_row(
        self,
        row: Dict[str, str],
        clk: str,
        rst: str,
        disable_cond: str,
        ports: List[str],
        strict_log: Dict[str, Any],
    ) -> Optional[str]:
        sid = row.get('sid', '').strip()
        name = row.get('name', '').strip() or sid
        ptype = (row.get('prop_type', 'assert') or 'assert').strip().lower()
        scenario = (row.get('scenario', '') or '').strip().lower()
        line_no = row.get('_line', '')

        pre_raw = row.get('pre', '')
        post_raw = row.get('post', '')

        pre, post, repair_meta = self._repair_pre_post_from_csv(pre_raw, post_raw, ports, scenario=scenario)

        invalidated = {'pre_invalid': False, 'post_invalid': False}
        if pre and not self._expr_uses_only_ports(pre, ports):
            invalidated['pre_invalid'] = True
            pre = ''
        if post and not self._expr_uses_only_ports(post, ports):
            invalidated['post_invalid'] = True
            post = ''

        repair_meta.update(invalidated)

        if self.strict:
            changed = (
                repair_meta.get('lifted_implications', 0) > 0
                or repair_meta.get('temporal_mix_rewritten', False)
                or repair_meta.get('cleared_trivial_pre', False)
                or repair_meta.get('dropped_implication_in_pre', False)
                or repair_meta.get('pre_invalid', False)
                or repair_meta.get('post_invalid', False)
            )
            if changed:
                strict_log['row_repairs'].append(
                    {
                        'sid': sid,
                        'name': name,
                        'line': line_no,
                        'prop_type': ptype,
                        'details': repair_meta,
                    }
                )

        pre_missing = self._pre_is_missing(pre_raw, pre)

        if not pre and not post:
            if self.strict:
                strict_log['skipped'].append(
                    {
                        'sid': sid,
                        'name': name,
                        'line': line_no,
                        'prop_type': ptype,
                        'reason': 'empty_pre_and_post_after_repairs_or_invalid_identifiers',
                        'pre_raw': (pre_raw or '').strip(),
                        'post_raw': (post_raw or '').strip(),
                        'pre_norm': pre,
                        'post_norm': post,
                    }
                )
            return None

        if 'auto_repaired_invariant' in scenario:
            if post:
                body = f'({post})'
            else:
                body = f'({pre})' if pre else ''
            if not body:
                if self.strict:
                    strict_log['skipped'].append(
                        {
                            'sid': sid,
                            'name': name,
                            'line': line_no,
                            'prop_type': ptype,
                            'reason': 'auto_repaired_invariant_but_no_expr',
                            'pre_raw': (pre_raw or '').strip(),
                            'post_raw': (post_raw or '').strip(),
                        }
                    )
                return None
            return self._wrap_property(sid, name, ptype, clk, disable_cond, body)

        # ONLY-PRE
        if not post and pre:
            if ptype in {'assume', 'assert'} and _is_trivial_true(pre):
                if self.strict:
                    strict_log['skipped'].append(
                        {
                            'sid': sid,
                            'name': name,
                            'line': line_no,
                            'prop_type': ptype,
                            'reason': 'only_pre_but_trivial_true',
                            'pre_norm': pre,
                        }
                    )
                return None
            body = f'({pre})'
            return self._wrap_property(sid, name, ptype, clk, disable_cond, body)

        # ONLY-POST (NO-PRE)
        if post and pre_missing:
            if ptype in {'assume', 'assert'} and _is_trivial_true(post):
                if self.strict:
                    strict_log['skipped'].append(
                        {
                            'sid': sid,
                            'name': name,
                            'line': line_no,
                            'prop_type': ptype,
                            'reason': 'only_post_but_trivial_true',
                            'post_norm': post,
                        }
                    )
                return None
            body = f'({post})'
            return self._wrap_property(sid, name, ptype, clk, disable_cond, body)

        # BOTH pre and post
        if pre and post:
            if (('eventually' in scenario) or ('not stuck' in scenario) or ('forever' in scenario)) and (
                not self._post_has_temporal(post)
            ):
                body = f'({pre}) |-> ##[1:$] ({post})'
            else:
                body = f'({pre}) |-> ({post})'

            flat = re.sub(r'\s+', '', body)
            if ptype in {'assume', 'assert'} and ("1'b1|->1'b1" in flat or '1|->1' in flat):
                if self.strict:
                    strict_log['skipped'].append(
                        {
                            'sid': sid,
                            'name': name,
                            'line': line_no,
                            'prop_type': ptype,
                            'reason': 'tautology_implication',
                            'body': body,
                        }
                    )
                return None

            return self._wrap_property(sid, name, ptype, clk, disable_cond, body)

        if post:
            return self._wrap_property(sid, name, ptype, clk, disable_cond, f'({post})')

        if self.strict:
            strict_log['skipped'].append(
                {
                    'sid': sid,
                    'name': name,
                    'line': line_no,
                    'prop_type': ptype,
                    'reason': 'fell_through_unhandled_case',
                }
            )
        return None

    # ------------------------------------------------------------------
    def _call_llm_for_row(
        self,
        clk: str,
        rst: str,
        disable_cond: str,
        ports: List[str],
        md: str,
        row: Dict[str, str],
    ) -> str:
        if not self.llm:
            return ''

        # IMPORTANT: Your current property_prompt.yaml ALWAYS outputs '<PRE> |-> <POST>'.
        # Since you explicitly do not want '1 |-> ...' when pre is empty, we skip LLM when pre is missing.
        pre_raw = (row.get('pre', '') or '').strip()
        post_raw = (row.get('post', '') or '').strip()

        if pre_raw in {'', '1', "1'b1"}:
            return ''
        if post_raw == '':
            return ''

        sid = row.get('sid', '')
        name = row.get('name', '')
        ptype = row.get('prop_type', 'assert')
        scenario = (row.get('scenario', '') or '').strip().lower()

        # Repair CSV mistakes BEFORE sending to LLM (prevents nested implications)
        pre_fixed, post_fixed, _meta = self._repair_pre_post_from_csv(pre_raw, post_raw, ports, scenario=scenario)
        if not pre_fixed or not post_fixed:
            return ''

        payload = {
            'clock': clk,
            'reset': rst,
            'reset_disable': disable_cond,
            'sid': sid,
            'name': name,
            'ptype': ptype,
            'pre': pre_fixed,
            'post': post_fixed,
            'spec_markdown': md,
            'allowed_signals': ', '.join(sorted(set(ports))),
        }

        try:
            res = self.llm.inference(payload, prompt_index='sva_property_block', n=1)
        except Exception as e:
            print(f'[LLM ERROR] row {sid} ({name}): {e}')
            return ''

        if isinstance(res, str):
            text = res
        elif isinstance(res, list) and res:
            text = res[0]
        elif isinstance(res, dict) and 'choices' in res:
            try:
                text = res['choices'][0]['message']['content']
            except Exception:
                text = ''
        else:
            text = ''

        return self._extract_sv_code(text or '')

    # ------------------------------------------------------------------
    def _sanitize_llm_property(
        self,
        llm_sv: str,
        row: Dict[str, str],
        clk: str,
        rst: str,
        disable_cond: str,
        ports: List[str],
    ) -> Optional[str]:
        sv = (llm_sv or '').strip()
        if not sv:
            return None

        # If LLM returned a bare expression, fall back
        if 'property' not in sv:
            return None

        # Ensure disable iff exists; if not, inject after @(posedge clk)
        if 'disable iff' not in sv:
            sv = re.sub(
                rf'(@\(\s*posedge\s+{re.escape(clk)}\s*\))',
                rf'\1 disable iff ({disable_cond})',
                sv,
                count=1,
            )

        # Reject tautologies
        flat = re.sub(r'\s+', '', sv)
        if '1|->1' in flat or "1'b1|->1'b1" in flat:
            return None

        # Also reject nested implications inside the property text (common when CSV was broken)
        # (If present, fall back to rule-based which repairs pre/post.)
        if sv.count('|->') > 1 or sv.count('|=>') > 1:
            return None

        pre_raw = (row.get('pre', '') or '').strip()
        if pre_raw in {'', '1', "1'b1"} and ('|->' in sv or '|=>' in sv):
            return None

        return sv.strip()

    # ------------------------------------------------------------------
    def _write_strict_report(self, report: Dict[str, Any]) -> None:
        try:
            Path(self.report_json).write_text(json.dumps(report, indent=2), encoding='utf-8')
            print(f'[STRICT] Report written: {self.report_json}')
        except Exception as e:
            print(f'[STRICT WARN] Failed to write report JSON {self.report_json}: {e}')

    # ------------------------------------------------------------------
    def generate_properties(self) -> str:
        rows, csv_parse_report = self._read_csv_rows()
        md = self._read_markdown()

        clk, rst, disable_cond, spec_top_module, prop_top_used = self._find_clk_rst(rows)

        strict_log: Dict[str, Any] = {
            'inputs': {
                'spec_md': self.spec_md,
                'csv': self.csv_path,
                'rtl_dir': self.rtl_dir,
                'out_dir': self.out_dir,
                'design_top': self.design_top or '',
                'property_top': prop_top_used,
                'clock_override': self.clock_name_override or '',
                'reset_override': self.reset_name_override or '',
                'reset_expr_override': self.reset_expr_override or '',
                'llm_enabled': bool(self.llm),
            },
            'clock_reset': {
                'clock': clk,
                'reset': rst,
                'disable_iff': disable_cond,
                'spec_top': spec_top_module,
                'property_top': prop_top_used,
            },
            'csv_parse': csv_parse_report,
            'ports': {
                'source': '',
                'count': 0,
                'list': [],
            },
            'summary': {
                'rows_total': len(rows),
                'generated': 0,
                'skipped': 0,
                'llm_used': 0,
                'rule_based_used': 0,
            },
            'row_repairs': [],
            'skipped': [],
        }

        # Ports are also based on property_top (SVA/bind target), not design top
        ports, ports_source = self._find_ports(prop_top_used, rows)

        # Ensure clk/rst included in allowed tokens
        if clk and clk not in ports:
            ports.append(clk)
        if rst and rst not in ports:
            ports.append(rst)

        strict_log['ports']['source'] = ports_source
        strict_log['ports']['count'] = len(ports)
        strict_log['ports']['list'] = ports[:]

        print(f'[INFO] Allowed signals for checks ({prop_top_used}): {ports}')

        # If we still don't have a clock, we cannot generate correct properties
        if not clk:
            raise SystemExit(
                f"ERROR: Could not determine property clock for property_top='{prop_top_used}'. "
                f'Provide --clock-name or ensure {prop_top_used}_ports.json exists.'
            )
        if not disable_cond:
            # Still allow, but warn; disable iff () is illegal, so we need something.
            print("[WARN] Could not determine reset/disable iff condition; defaulting to 1'b0 (no disable).")
            disable_cond = "1'b0"

        all_props: List[str] = []
        header = (
            '// ------------------------------------------------------------------\n'
            '// Auto-generated properties\n'
            f'// Spec: {Path(self.spec_md).name}\n'
            f'// CSV : {Path(self.csv_path).name}\n'
            f'// Domain: property_top={prop_top_used}, clk={clk}, disable_iff=({disable_cond})\n'
            '// ------------------------------------------------------------------\n'
        )

        for row in rows:
            self._fix_reset_deassertion(row, rst)

            sid = row.get('sid', '').strip()
            name = row.get('name', '').strip()
            print(f'[INFO] Generating property for row {sid} ({name})')

            # LLM then sanitize; fallback to deterministic rule-based
            llm_sv = self._call_llm_for_row(clk, rst, disable_cond, ports, md, row) if self.llm else ''
            sv_text = self._sanitize_llm_property(llm_sv, row, clk, rst, disable_cond, ports)

            if sv_text:
                strict_log['summary']['llm_used'] += 1
            else:
                sv_text = self._rule_based_property_from_row(row, clk, rst, disable_cond, ports, strict_log)
                if sv_text:
                    strict_log['summary']['rule_based_used'] += 1

            if not sv_text:
                strict_log['summary']['skipped'] += 1
                continue

            all_props.append(sv_text.strip())
            strict_log['summary']['generated'] += 1

        out_path = os.path.join(self.out_dir, 'properties.sv')
        final_text = header + ('\n\n'.join(all_props) if all_props else '\n// No valid properties generated\n')

        with open(out_path, 'w', encoding='utf-8') as f:
            f.write(final_text.rstrip() + '\n')

        print(f'[✅] Properties written to {out_path}')

        if self.strict:
            self._write_strict_report(strict_log)

        return out_path


if __name__ == '__main__':
    import argparse

    p = argparse.ArgumentParser()
    p.add_argument('--spec-md', required=True)
    p.add_argument('--csv', required=True)
    p.add_argument('--rtl', required=True)
    p.add_argument('--out', required=True)
    p.add_argument('--llm-conf', required=False, default=None)

    # Existing (kept): ELAB top name (useful for overall flow/debug), but NOT used for property clocking by default
    p.add_argument(
        '--design-top', default=None, help='Elaboration top (informational here; properties use --property-top domain).'
    )

    # NEW: property domain module (SVA/bind target)
    p.add_argument(
        '--property-top',
        '--sva-top',
        dest='property_top',
        default=None,
        help='Module whose clock/reset domain properties are generated in (bind target). Default: inferred from spec-md filename (e.g. fifo_spec.md -> fifo).',
    )

    # NEW overrides
    p.add_argument('--clock-name', default=None, help='Override property clock name (e.g. clock).')
    p.add_argument('--reset-name', default=None, help='Override property reset signal name (e.g. reset_n).')
    p.add_argument('--reset-expr', default=None, help="Override disable iff expression verbatim (e.g. '!reset_n' or 'reset').")

    p.add_argument('--strict', action='store_true', help='Write strict JSON report of repairs/skips.')
    p.add_argument('--report-json', default=None, help='Path for strict JSON report (default: out/properties.report.json)')
    args = p.parse_args()

    pb = PropertyBuilder(
        spec_md=args.spec_md,
        csv_path=args.csv,
        rtl_dir=args.rtl,
        out_dir=args.out,
        llm_conf=args.llm_conf,
        design_top=args.design_top,
        property_top=args.property_top,
        clock_name=args.clock_name,
        reset_name=args.reset_name,
        reset_expr=args.reset_expr,
        strict=args.strict,
        report_json=args.report_json,
    )
    pb.generate_properties()
