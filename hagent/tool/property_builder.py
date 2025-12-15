#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
property_builder.py
-------------------
Generate SystemVerilog properties (assert/assume/cover) using LLM.

Key behavior:
  - One LLM call **per CSV row**.
  - Use clock/reset from clk_rst_utils:
        * If a design_top is provided, detect clk/rst from design_top.
        * Otherwise, detect clk/rst from the spec top (module name inferred
          from spec_md:  <module>_spec.md).
  - Ports / allowed signals are taken from the *spec module* (submodule),
    not from the design top. This keeps properties local to the module
    being specified (e.g. load_unit).
  - Give the LLM:
      * Markdown spec
      * CSV row
      * allowed top-level signals for the spec module
      * clock/reset names
  - Post-process the SVA to:
      * replace bad '1'b1 |-> ...' with proper CSV `pre` when possible
      * replace '... |-> 1'b1' with CSV `post` when possible
      * drop totally trivial 1'b1 |-> 1'b1 properties
"""

from __future__ import annotations
import os
import re
import csv
from pathlib import Path
from typing import List, Dict, Optional

from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

try:
    from hagent.core.llm_wrap import LLM_wrap
except Exception:
    LLM_wrap = None


# -----------------------------------------------------------------------------
# Simple RTL-based spec-top port extraction
# -----------------------------------------------------------------------------
def detect_top_ports_from_rtl(rtl_dir: str, top: str) -> List[str]:
    """
    Parse 'module <top>( ... );' headers in RTL and return a list of port names.

    E.g. for:
      module Sync_FIFO( clk, rst, buf_in, buf_out, wr_en, rd_en, buf_empty, buf_full, fifo_counter );
    returns:
      ['clk', 'rst', 'buf_in', 'buf_out', 'wr_en', 'rd_en',
       'buf_empty', 'buf_full', 'fifo_counter']
    """
    rtl_dir_path = Path(rtl_dir)

    mod_re = re.compile(
        rf'\bmodule\s+{re.escape(top)}\b[^(]*\((?P<ports>.*?)\)\s*;',
        re.DOTALL | re.MULTILINE,
    )

    port_names: List[str] = []

    for sv in rtl_dir_path.rglob('*'):
        if sv.suffix not in {'.sv', '.v'}:
            continue
        try:
            txt = sv.read_text(encoding='utf-8', errors='ignore')
        except Exception:
            continue

        m = mod_re.search(txt)
        if not m:
            continue

        port_block = m.group('ports') or ''
        # Strip comments
        port_block = re.sub(r'//.*?$', '', port_block, flags=re.M)
        port_block = re.sub(r'/\*.*?\*/', '', port_block, flags=re.S)

        # Split by comma and extract last identifier from each chunk
        for chunk in port_block.split(','):
            chunk = chunk.strip()
            if not chunk:
                continue
            # Drop ranges like [7:0]
            chunk = re.sub(r'\[[^\]]+\]', ' ', chunk)
            toks = re.findall(r'\b[A-Za-z_]\w*\b', chunk)
            if not toks:
                continue
            name = toks[-1]
            if name not in port_names:
                port_names.append(name)

        if port_names:
            break

    return port_names


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
        """
        Parameters
        ----------
        spec_md : str
            Path to Markdown spec (e.g. out/load_unit_spec.md).
            The spec-top module is inferred from the filename stem
            before '_spec', e.g. 'load_unit_spec' -> 'load_unit'.
        csv_path : str
            Path to CSV spec (same module as spec_md).
        rtl_dir : str
            RTL root directory (for clk/rst detection and port discovery).
        out_dir : str
            Output directory (properties.sv).
        llm_conf : str | None
            YAML configuration for LLM.
        design_top : str | None
            Optional design top used to detect clk/rst. If None, we
            detect clk/rst from the spec top module inferred from spec_md.
        """
        self.spec_md = os.path.abspath(spec_md)
        self.csv_path = os.path.abspath(csv_path)
        self.rtl_dir = os.path.abspath(rtl_dir)
        self.out_dir = os.path.abspath(out_dir)
        os.makedirs(self.out_dir, exist_ok=True)

        self.llm_conf = os.path.abspath(llm_conf) if llm_conf else None
        self.design_top = design_top

        if not LLM_wrap or not self.llm_conf:
            print('[❌] LLM_wrap not available or llm_conf missing.')
            self.llm = None
        else:
            print(f'[LLM] Using config: {self.llm_conf}')
            self.llm = LLM_wrap(
                name='default',
                conf_file=self.llm_conf,
                log_file='property_llm.log',
            )

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
    def _find_clk_rst(self):
        """
        Return (clk, rst, spec_top_module_name).

        - spec_top_module_name is inferred from spec_md: <name>_spec.md -> <name>.
        - clk/rst are detected via detect_clk_rst_for_top:
            * If design_top is provided, we detect clk/rst from design_top.
            * Otherwise, we detect clk/rst from spec_top_module_name.
        """
        spec_top = Path(self.spec_md).stem.split('_spec')[0]
        clk_top = self.design_top or spec_top

        clk, rst, _ = detect_clk_rst_for_top(Path(self.rtl_dir), clk_top)
        print(f'[INFO] Clock={clk}, Reset={rst} (detected from top="{clk_top}")')
        return clk, rst, spec_top

    # ------------------------------------------------------------------
    @staticmethod
    def _extract_sv_code(text: str) -> str:
        """
        If the model wraps SV in ```systemverilog``` fences, strip them.
        Otherwise just return trimmed text.
        """
        if not text:
            return ''
        m = re.search(r'```(?:systemverilog|sv|verilog)?\s*([\s\S]*?)```', text, re.I)
        if m:
            return m.group(1).strip()
        return text.strip()

    # ------------------------------------------------------------------
    @staticmethod
    def _expr_uses_only_ports(expr: str, ports: List[str]) -> bool:
        """
        Check that an expression only references known ports / SV keywords.
        Very lightweight sanity check.
        """
        if not expr.strip():
            return False
        tokens = re.findall(r'\b[A-Za-z_]\w*\b', expr)
        allowed_ids = set(ports) | {
            # SV keywords we might see as identifiers
            'if',
            'else',
            'and',
            'or',
            'not',
            # builtins/system functions (keywords, not identifiers, but safe)
            'posedge',
            'negedge',
            'disable',
            'iff',
        }
        for t in tokens:
            if t in allowed_ids:
                continue
            # allow simple numeric/token-like symbols (e.g. BUF_SIZE)
            if re.match(r'^[A-Z0-9_]+$', t):
                continue
            # any other unknown identifier is suspicious
            if t not in ports:
                return False
        return True

    # ------------------------------------------------------------------
    @staticmethod
    def _fix_trivial_pre_post(
        sv_text: str,
        pre_expr: str,
        post_expr: str,
        ports: List[str],
    ) -> str:
        """
        Try to repair common bad patterns:
          1'b1 |-> <expr>
          <expr> |-> 1'b1
          1'b1 |-> 1'b1   (drop outside this function)
        We only patch if CSV expressions look sane (only ports).
        """
        txt = sv_text

        # Fix LHS 1'b1 |-> <expr>  -->  (pre_expr) |-> <expr>
        if pre_expr and PropertyBuilder._expr_uses_only_ports(pre_expr, ports):
            lhs_pattern = r"1'b1\s*\|\-\>"
            if re.search(lhs_pattern, txt):
                txt = re.sub(lhs_pattern, f'({pre_expr}) |->', txt, count=1)

        # Fix RHS ... |-> 1'b1  or ... |-> ##N 1'b1  -->  ... |-> (post_expr)
        if post_expr and PropertyBuilder._expr_uses_only_ports(post_expr, ports):
            rhs_pattern = r"\|\-\>\s*(?:##\s*\d+\s*)?1'b1\b"
            if re.search(rhs_pattern, txt):
                txt = re.sub(rhs_pattern, f'|-> ({post_expr})', txt, count=1)

        return txt

    # ------------------------------------------------------------------
    def _is_totally_trivial(self, sv_text: str) -> bool:
        """
        Return True if the property body effectively has 1'b1 |-> 1'b1.
        """
        return bool(
            re.search(
                r"1'b1\s*\|\-\>\s*(?:##\s*\d+\s*)?1'b1\b",
                sv_text.replace(' ', ''),
            )
        )

    # ------------------------------------------------------------------
    def _call_llm_for_row(
        self,
        clk: str,
        rst: str,
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
            'sid': sid,
            'name': name,
            'ptype': ptype,
            'pre': pre,
            'post': post,
            'spec_markdown': md,
            # Give the LLM explicit list of allowed top-level signals
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
    def generate_properties(self) -> str:
        """
        Main entry: read CSV + Markdown, detect clk/rst + ports, call LLM per row,
        repair trivial pre/post, drop useless properties, and write properties.sv.
        """

        if not self.llm:
            print('[❌] LLM is not initialized; cannot generate properties.')
            return ''

        clk, rst, spec_top_module = self._find_clk_rst()
        rows = self._read_csv_rows()
        md = self._read_markdown()

        # Detect top-level ports from RTL for the *spec module*.
        ports = detect_top_ports_from_rtl(self.rtl_dir, spec_top_module)
        print(f'[INFO] Spec-top ports detected from RTL ({spec_top_module}): {ports}')

        # Fallback: if RTL detection fails, at least add clk/rst so prompt isn't empty
        if not ports:
            ports = []
        if clk and clk not in ports:
            ports.append(clk)
        if rst and rst not in ports:
            ports.append(rst)

        all_props: List[str] = []

        for row in rows:
            sid = row.get('sid', '')
            name = row.get('name', '')
            pre = row.get('pre', '')
            post = row.get('post', '')

            print(f'[INFO] Generating property for row {sid} ({name})')

            sv_text = self._call_llm_for_row(clk, rst, ports, md, row)
            if not sv_text.strip():
                print(f'[WARN] Empty property text for row {sid} ({name}); skipping.')
                continue

            # Try to fix trivial 1'b1 uses using CSV pre/post
            sv_text = self._fix_trivial_pre_post(sv_text, pre, post, ports)

            # Drop completely trivial properties 1'b1 |-> 1'b1
            if self._is_totally_trivial(sv_text):
                print(f'[WARN] Dropping totally trivial property for row {sid} ({name}).')
                continue

            all_props.append(sv_text.strip())

        out_path = os.path.join(self.out_dir, 'properties.sv')

        if all_props:
            final_text = '\n\n'.join(all_props)
        else:
            final_text = '// No valid properties generated'

        with open(out_path, 'w', encoding='utf-8') as f:
            f.write(final_text + '\n')

        print(f'[✅] Properties written to {out_path}')
        return out_path


# -----------------------------------------------------------------------------
# CLI wrapper
# -----------------------------------------------------------------------------
if __name__ == '__main__':
    import argparse

    p = argparse.ArgumentParser()
    p.add_argument('--spec-md', required=True)
    p.add_argument('--csv', required=True)
    p.add_argument('--rtl', required=True)
    p.add_argument('--out', required=True)
    p.add_argument('--llm-conf', required=True)
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

