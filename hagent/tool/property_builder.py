#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
property_builder.py
-------------------
Generate SystemVerilog properties (assert/assume/cover) from a CSV spec,
optionally using an LLM per row.

Improvements vs older draft:
  - Complete implementation (no missing helpers).
  - Robust RTL port extraction (ANSI + non-ANSI module headers).
  - CSV phrase normalization:
      * "X stable for 1 cycle" -> $stable(X)
      * "Y changes"            -> $changed(Y)
      * "1"                    -> 1'b1
  - Adds "disable iff (reset_expr)" to every property automatically.
  - Fixes reset deassertion rows (common polarity bug).
  - Allows struct member access (e.g., lsu_ctrl_i.vaddr) in expressions.
  - Rule-based fallback if LLM is missing or returns empty/unusable text.
"""

from __future__ import annotations

import os
import re
import csv
from pathlib import Path
from typing import List, Dict, Optional, Tuple

from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

try:
    from hagent.core.llm_wrap import LLM_wrap
except Exception:
    LLM_wrap = None


# -----------------------------------------------------------------------------
# RTL Port Extraction (ANSI + non-ANSI)
# -----------------------------------------------------------------------------
def _strip_sv_comments(s: str) -> str:
    s = re.sub(r'//.*?$', '', s, flags=re.M)
    s = re.sub(r'/\*.*?\*/', '', s, flags=re.S)
    return s


def detect_top_ports_from_rtl(rtl_dir: str, top: str) -> List[str]:
    """
    Return a list of port names for module `top` found under rtl_dir.

    Supports:
      - Non-ANSI: module m(a,b,c);
      - ANSI:     module m(input logic clk, output logic [3:0] y, ...);

    NOTE: This is intentionally lightweight (not a full SV parser),
          but works well for typical RTL.
    """
    rtl_dir_path = Path(rtl_dir)
    top_esc = re.escape(top)

    # Match "module <top> ... ( <ports> ) ;"
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
        # Split on commas at top-level (ignore commas inside parentheses)
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
            # remove packed/unpacked ranges
            p2 = re.sub(r'\[[^\]]+\]', ' ', p)
            # If ANSI style, last identifier is the port name.
            # If non-ANSI style, the chunk is already a name.
            toks = re.findall(r'\b[A-Za-z_]\w*\b', p2)
            if not toks:
                continue
            name = toks[-1]
            if name not in ports:
                ports.append(name)

        if ports:
            return ports

    return []


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
    ):
        self.spec_md = os.path.abspath(spec_md)
        self.csv_path = os.path.abspath(csv_path)
        self.rtl_dir = os.path.abspath(rtl_dir)
        self.out_dir = os.path.abspath(out_dir)
        os.makedirs(self.out_dir, exist_ok=True)

        self.llm_conf = os.path.abspath(llm_conf) if llm_conf else None
        self.design_top = design_top

        self.llm = None
        if LLM_wrap and self.llm_conf and os.path.exists(self.llm_conf):
            print(f'[LLM] Using config: {self.llm_conf}')
            self.llm = LLM_wrap(
                name='default',
                conf_file=self.llm_conf,
                log_file='property_llm.log',
            )
        else:
            print('[WARN] LLM disabled (LLM_wrap missing or llm_conf missing). Using rule-based generation.')

    # ------------------------------------------------------------------
    @staticmethod
    def _fmt(s: Optional[str]) -> str:
        """Escape braces so YAML templates don't get confused."""
        if s is None:
            return ''
        return str(s).replace('{', '{{').replace('}', '}}')

    # ------------------------------------------------------------------
    def _read_csv_rows(self) -> List[Dict[str, str]]:
        rows: List[Dict[str, str]] = []
        with open(self.csv_path, 'r', encoding='utf-8', errors='ignore') as f:
            reader = csv.DictReader(f)
            for r in reader:
                clean = {(k or '').strip(): self._fmt((v or '').strip()) for k, v in r.items() if k is not None}
                rows.append(clean)
        print(f'[DEBUG] Loaded {len(rows)} CSV rows.')
        return rows

    # ------------------------------------------------------------------
    def _read_markdown(self) -> str:
        try:
            txt = Path(self.spec_md).read_text(encoding='utf-8', errors='ignore')
        except Exception:
            txt = ''
        return self._fmt(txt)

    # ------------------------------------------------------------------
    def _infer_spec_top(self) -> str:
        # <name>_spec.md -> <name>
        stem = Path(self.spec_md).stem
        if '_spec' in stem:
            return stem.split('_spec')[0]
        # fallback: use module column later if present
        return stem

    # ------------------------------------------------------------------
    def _find_clk_rst(self) -> Tuple[str, str, str, str]:
        """
        Return (clk_name, rst_name, rst_disable_expr, spec_top_module_name).

        detect_clk_rst_for_top returns clk, rst, and sometimes reset expression
        depending on your implementation; your logs show it detects expression "!rst_ni".
        We compute disable expression ourselves as:
            disable iff (<reset_asserted_expr>)
        """
        spec_top = self._infer_spec_top()
        clk_top = self.design_top or spec_top

        clk, rst, rst_expr = detect_clk_rst_for_top(Path(self.rtl_dir), clk_top)

        # rst_expr in your log is "!rst_ni" meaning "reset asserted when !rst_ni".
        # We'll use that as disable iff condition if present; else guess:
        #   *_ni means active-low, otherwise active-high.
        if rst_expr and str(rst_expr).strip():
            disable_cond = str(rst_expr).strip()
        else:
            disable_cond = f'!{rst}' if rst.endswith('_ni') else rst

        print(f'[INFO] Clock={clk}, Reset={rst}, disable iff ({disable_cond}) (detected from top="{clk_top}")')
        return clk, rst, disable_cond, spec_top

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
        """
        Convert CSV natural language fragments to SV-ish expressions.
        """
        e = (expr or '').strip()
        if not e:
            return ''

        # Canonicalize "1"
        if e == '1':
            return "1'b1"
        if e == '0':
            return "1'b0"

        # "X stable for 1 cycle" -> $stable(X)
        m = re.match(r'^([A-Za-z_]\w*)\s+stable\s+for\s+1\s+cycle$', e, re.I)
        if m:
            sig = m.group(1)
            return f'$stable({sig})'

        # "<sig> changes" -> $changed(sig)
        m = re.match(r'^([A-Za-z_]\w*)\s+changes$', e, re.I)
        if m:
            sig = m.group(1)
            return f'$changed({sig})'

        # "result_o changes" sometimes appears with spaces: keep as is if token is port
        if e.lower().endswith(' changes'):
            sig = e[:-8].strip()
            if sig in ports:
                return f'$changed({sig})'

        # "stable(X)" (if someone wrote it) -> $stable(X)
        m = re.match(r'^stable\(([\s\S]+)\)$', e, re.I)
        if m:
            return f'$stable({m.group(1).strip()})'

        return e

    # ------------------------------------------------------------------
    @staticmethod
    def _expr_uses_only_ports(expr: str, ports: List[str]) -> bool:
        """
        Lightweight sanity check:
        - allow identifiers that are ports
        - allow identifiers preceded by '.' (struct field names)
        - allow all-caps params
        - allow system funcs/keywords

        This avoids blocking expressions like "lsu_ctrl_i.vaddr[11:0]".
        """
        if not (expr or '').strip():
            return False

        allowed_ids = set(ports) | {
            # keywords / misc
            'if', 'else', 'and', 'or', 'not', 'posedge', 'negedge', 'disable', 'iff',
            # system tasks/functions
            '$stable', '$changed', '$past', '$rose', '$fell', '$isunknown',
            # temporal operators sometimes tokenized
            '##',
        }

        # Find all identifiers and their position
        for m in re.finditer(r'\b[A-Za-z_]\w*\b', expr):
            t = m.group(0)
            if t in allowed_ids:
                continue
            if re.match(r'^[A-Z0-9_]+$', t):
                continue

            # Allow field names (preceded by a dot)
            idx = m.start()
            if idx > 0 and expr[idx - 1] == '.':
                continue

            # Anything else unknown => reject
            return False

        return True

    # ------------------------------------------------------------------
    @staticmethod
    def _fix_reset_deassertion(row: Dict[str, str], rst: str) -> None:
        """
        Heuristic fix:
        - If row name/scenario implies "deassert", then post should be rst==1 for *_ni.
        - Your CSV row SVA001 had post "!rst_ni" which is wrong for deassert.
        """
        name = (row.get('name') or '').lower()
        scen = (row.get('scenario') or '').lower()
        post = (row.get('post') or '').strip()

        if 'deassert' in name or 'deassert' in scen:
            # If reset is active-low, deassert means rst=1 (i.e., rst_ni).
            # If they wrote "!rst_ni", flip it.
            if rst.endswith('_ni') and post in (f'!{rst}', f'! {rst}'):
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
        """
        Create a property + bind label snippet.
        """
        prop_name = name or sid or 'prop'
        label = f"{ptype}_{prop_name}".replace('-', '_')

        # ptype may be "assert/assume/cover"
        if ptype not in {'assert', 'assume', 'cover'}:
            ptype = 'assert'

        return (
            f"// {sid}: {prop_name}\n"
            f"property {prop_name};\n"
            f"  @(posedge {clk}) disable iff ({disable_cond})\n"
            f"    {body_expr};\n"
            f"endproperty\n"
            f"{label}: {ptype} property({prop_name});"
        )

    # ------------------------------------------------------------------
    def _rule_based_property_from_row(
        self,
        row: Dict[str, str],
        clk: str,
        rst: str,
        disable_cond: str,
        ports: List[str],
    ) -> Optional[str]:
        """
        Deterministic generation when:
          - LLM is disabled, or
          - LLM output is empty/broken.

        Uses row pre/post and prop_type plus simple scenario keyword inference.
        """
        sid = row.get('sid', '').strip()
        name = row.get('name', '').strip() or sid
        ptype = (row.get('prop_type', 'assert') or 'assert').strip().lower()
        scenario = (row.get('scenario', '') or '').strip().lower()

        pre_raw = row.get('pre', '')
        post_raw = row.get('post', '')

        pre = self._normalize_csv_expr(pre_raw, ports)
        post = self._normalize_csv_expr(post_raw, ports)

        # Safety: if pre/post look like "stable for 1 cycle" without converting,
        # normalize again.
        pre = self._normalize_csv_expr(pre, ports)
        post = self._normalize_csv_expr(post, ports)

        # If someone wrote just a signal in post, that is okay (treated as boolean)
        # Validate (lightly)
        if pre and not self._expr_uses_only_ports(pre, ports):
            pre = ''
        if post and not self._expr_uses_only_ports(post, ports):
            post = ''

        # Default pre
        if not pre:
            pre = "1'b1"

        # Decide operator form
        # - "eventually" / "not stuck" -> pre |-> ##[1:$] post
        # - otherwise -> pre |-> post
        if ('eventually' in scenario) or ('not stuck' in scenario) or ('forever' in scenario):
            if not post:
                return None
            body = f"({pre}) |-> ##[1:$] ({post})"
        else:
            if not post:
                # If post missing but pre present, treat as cover/assert of pre itself
                body = f"({pre})"
            else:
                body = f"({pre}) |-> ({post})"

        # Drop totally trivial
        if re.sub(r'\s+', '', body) in ("1'b1|->1'b1", "(1'b1)|->(1'b1)"):
            return None

        return self._wrap_property(sid=sid, name=name, ptype=ptype, clk=clk, disable_cond=disable_cond, body_expr=body)

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
        """
        Call the LLM for a single CSV row and return raw SV text (unfiltered).
        """
        if not self.llm:
            return ''

        sid = row.get('sid', '')
        name = row.get('name', '')
        ptype = row.get('prop_type', 'assert')
        pre = row.get('pre', '')
        post = row.get('post', '')

        payload = {
            'clock': clk,
            'reset': rst,
            'reset_disable': disable_cond,
            'sid': sid,
            'name': name,
            'ptype': ptype,
            'pre': pre,
            'post': post,
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
        """
        Try to make LLM output usable. If it looks too broken, return None.
        """
        sv = (llm_sv or '').strip()
        if not sv:
            return None

        # If LLM returned a bare expression, wrap it
        if 'property' not in sv:
            rb = self._rule_based_property_from_row(row, clk, rst, disable_cond, ports)
            return rb

        # Ensure disable iff exists; if not, inject after @(posedge clk)
        if 'disable iff' not in sv:
            sv = re.sub(
                rf'(@\(\s*posedge\s+{re.escape(clk)}\s*\))',
                rf'\1 disable iff ({disable_cond})',
                sv,
                count=1
            )

        # Fix 1 |-> <post> by replacing 1 with normalized pre when available
        pre = self._normalize_csv_expr(row.get('pre', ''), ports)
        post = self._normalize_csv_expr(row.get('post', ''), ports)

        if pre and self._expr_uses_only_ports(pre, ports):
            sv = re.sub(r'(\s)1(\s*\|\-\>)', rf'\1({pre})\2', sv, count=1)

        if post and self._expr_uses_only_ports(post, ports):
            sv = re.sub(r'(\|\-\>\s*)(?:##\s*\d+\s*)?1\b', rf'\1({post})', sv, count=1)

        # If still has completely trivial implication, drop it
        flat = re.sub(r'\s+', '', sv)
        if "1|->1" in flat or "1'b1|->1'b1" in flat:
            return None

        return sv.strip()

    # ------------------------------------------------------------------
    def generate_properties(self) -> str:
        """
        Main entry: read CSV + Markdown, detect clk/rst + ports, generate properties.
        """
        clk, rst, disable_cond, spec_top_module = self._find_clk_rst()
        rows = self._read_csv_rows()
        md = self._read_markdown()

        # Detect top-level ports from RTL for the *spec module*.
        ports = detect_top_ports_from_rtl(self.rtl_dir, spec_top_module)
        if not ports:
            # Fallback: infer from CSV signals column if present (weak but better than nothing)
            ports = []
            for r in rows:
                sigs = (r.get('signals') or '').strip()
                for tok in re.split(r'[\s,]+', sigs):
                    tok = tok.strip()
                    if tok and tok not in ports:
                        ports.append(tok)

        # Always include clk/rst in allowed signals
        if clk and clk not in ports:
            ports.append(clk)
        if rst and rst not in ports:
            ports.append(rst)

        print(f'[INFO] Spec-top ports detected from RTL ({spec_top_module}): {ports}')

        all_props: List[str] = []
        header = (
            "// ------------------------------------------------------------------\n"
            "// Auto-generated properties\n"
            f"// Spec: {Path(self.spec_md).name}\n"
            f"// CSV : {Path(self.csv_path).name}\n"
            "// ------------------------------------------------------------------\n"
        )

        for row in rows:
            self._fix_reset_deassertion(row, rst)

            sid = row.get('sid', '').strip()
            name = row.get('name', '').strip()
            print(f'[INFO] Generating property for row {sid} ({name})')

            # Try LLM first (per-row), then sanitize; fallback to rule-based.
            llm_sv = self._call_llm_for_row(clk, rst, disable_cond, ports, md, row) if self.llm else ''
            sv_text = self._sanitize_llm_property(llm_sv, row, clk, rst, disable_cond, ports)

            if not sv_text:
                sv_text = self._rule_based_property_from_row(row, clk, rst, disable_cond, ports)

            if not sv_text:
                print(f'[WARN] Could not generate usable property for row {sid} ({name}); skipping.')
                continue

            all_props.append(sv_text.strip())

        out_path = os.path.join(self.out_dir, 'properties.sv')
        final_text = header + ("\n\n".join(all_props) if all_props else "\n// No valid properties generated\n")

        with open(out_path, 'w', encoding='utf-8') as f:
            f.write(final_text.rstrip() + '\n')

        print(f'[✅] Properties written to {out_path}')
        return out_path


# -----------------------------------------------------------------------------
# CLI wrapper (optional; you also have cli_property_builder.py)
# -----------------------------------------------------------------------------
if __name__ == '__main__':
    import argparse

    p = argparse.ArgumentParser()
    p.add_argument('--spec-md', required=True)
    p.add_argument('--csv', required=True)
    p.add_argument('--rtl', required=True)
    p.add_argument('--out', required=True)
    p.add_argument('--llm-conf', required=False, default=None)
    p.add_argument(
        '--design-top',
        help='Optional design top module name to use for clk/rst detection. '
             'If omitted, clk/rst are detected from the spec top inferred '
             'from --spec-md.',
    )
    args = p.parse_args()

    pb = PropertyBuilder(
        spec_md=args.spec_md,
        csv_path=args.csv,
        rtl_dir=args.rtl,
        out_dir=args.out,
        llm_conf=args.llm_conf,
        design_top=args.design_top,
    )
    pb.generate_properties()
