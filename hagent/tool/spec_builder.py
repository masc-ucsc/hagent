#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
spec_builder.py
---------------
End-to-end RTL → Spec (Markdown + CSV) generator.

ADDED (2025):
  - CSV "double-check" + repair feedback loop:
      * validate identifiers in pre/post against RTL IO ports
      * allow field-selects (req_port_o.data_req) if base port is valid
      * validate 'signals' column is consistent with signals used in pre/post
      * detect illegal nested temporal operators (## inside post expression)
      * if invalid, call LLM (prompt_index='csv_repair') to rewrite CSV
      * save broken CSV backup + validation JSON report for debugging
"""

from __future__ import annotations
import os
import re
import json
import shlex
import argparse
import subprocess
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple, Set

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

# ──────────────────────────────────────────────────────────────────────────────
# Helpers
# ──────────────────────────────────────────────────────────────────────────────
CSV_HEADER = ['sid', 'prop_type', 'module', 'name', 'scenario', 'pre', 'post', 'signals', 'param_ok', 'notes']

ALWAYS_KINDS = {'always', 'alwayscomb', 'alwaysff', 'always_latch', 'proceduralblock'}
ASSIGN_KINDS = {'continuousassign'}
IF_KINDS = {'if'}
CASE_KINDS = {'case'}

SV_SUFFIXES = {'.sv', '.svh', '.v', '.vh'}

# SV keywords we don't want to treat as signal identifiers
_SV_KEYWORDS = {
    "and", "or", "not", "iff", "if", "else", "case", "endcase", "begin", "end",
    "posedge", "negedge", "disable", "property", "endproperty", "assert", "assume",
    "cover", "sequence", "endsequence", "module", "endmodule", "always", "always_ff",
    "always_comb", "always_latch", "logic", "wire", "reg", "input", "output", "inout",
    "localparam", "parameter", "typedef", "struct", "union", "enum", "packed", "signed",
    "unsigned", "int", "integer", "bit", "byte", "shortint", "longint",
    "true", "false",
}

# Allowed SVA/SystemVerilog $functions we permit in CSV expressions
_ALLOWED_SVA_FUNCS = {"$rose", "$fell", "$stable", "$changed", "$past"}

# ──────────────────────────────────────────────────────────────────────────────
# File utilities
# ──────────────────────────────────────────────────────────────────────────────
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
# Robust filelist parsing (CVA6-style manifests)
# ──────────────────────────────────────────────────────────────────────────────
_FILELIST_KNOWN_OPTIONS = {
    "-F", "-f",
    "-v",
    "-y",
    "+incdir+",
    "-I",
    "+define+",
    "-D",
}

def _looks_like_comment_or_banner(line: str) -> bool:
    s = line.strip()
    if not s:
        return True
    if s.startswith("#") or s.startswith("//"):
        return True
    if s.startswith("/*") or s.startswith("*") or s.startswith("*/"):
        return True
    if s.startswith("/ ") and not any(ext in s for ext in (".sv", ".svh", ".v", ".vh", ".f", ".Flist", ".flist")):
        return True
    if s.startswith("/") and " " in s and not any(ext in s for ext in (".sv", ".svh", ".v", ".vh", ".f", ".Flist", ".flist")):
        return True
    return False


def _expand_vars(s: str, rtl_dir: Path, filelist_path: Path) -> str:
    if "CVA6_REPO_DIR" not in os.environ:
        os.environ["CVA6_REPO_DIR"] = str(rtl_dir.parent.resolve())
    return os.path.expandvars(s)


def _is_unresolved_var_path(s: str) -> bool:
    return ("${" in s) or ("$" in s and re.search(r"\$[A-Za-z_]\w*", s) is not None)


def _norm_path_token(tok: str) -> str:
    return tok.strip().strip('"').strip("'")


def _tokenize_filelist_line(line: str) -> List[str]:
    try:
        return shlex.split(line, comments=False, posix=True)
    except Exception:
        return line.strip().split()


def _parse_filelist(
    filelist_path: Path,
    rtl_dir: Path,
    include_dirs: List[Path],
    defines: List[str],
    visited: Set[Path],
) -> Tuple[List[Path], List[Path], List[str]]:
    files: List[Path] = []
    if filelist_path in visited:
        return files, include_dirs, defines
    visited.add(filelist_path)

    if not filelist_path.exists():
        console.print(f"[yellow]⚠ Nested filelist not found:[/yellow] {filelist_path}")
        return files, include_dirs, defines

    base_dir = filelist_path.parent.resolve()

    for raw in filelist_path.read_text(errors="ignore").splitlines():
        line = raw.strip()
        if _looks_like_comment_or_banner(line):
            continue

        toks = _tokenize_filelist_line(line)
        if not toks:
            continue

        i = 0
        while i < len(toks):
            t = _norm_path_token(toks[i])

            if t.startswith("+incdir+"):
                inc = t[len("+incdir+") :].strip()
                inc = _expand_vars(inc, rtl_dir, filelist_path)
                inc = _norm_path_token(inc)
                if _is_unresolved_var_path(inc):
                    console.print(f"[yellow]⚠ Skipping unresolved incdir:[/yellow] {t}")
                else:
                    ip = Path(inc)
                    if not ip.is_absolute():
                        ip = (rtl_dir / ip).resolve()
                    else:
                        ip = ip.resolve()
                    if ip.exists() and ip.is_dir():
                        include_dirs.append(ip)
                i += 1
                continue

            if t == "-I" and (i + 1) < len(toks):
                inc = _norm_path_token(toks[i + 1])
                inc = _expand_vars(inc, rtl_dir, filelist_path)
                if _is_unresolved_var_path(inc):
                    console.print(f"[yellow]⚠ Skipping unresolved -I incdir:[/yellow] {inc}")
                else:
                    ip = Path(inc)
                    if not ip.is_absolute():
                        ip = (rtl_dir / ip).resolve()
                    else:
                        ip = ip.resolve()
                    if ip.exists() and ip.is_dir():
                        include_dirs.append(ip)
                i += 2
                continue

            if t.startswith("+define+"):
                d = t[len("+define+") :].strip()
                d = _expand_vars(d, rtl_dir, filelist_path)
                d = _norm_path_token(d)
                if d:
                    defines.append(d)
                i += 1
                continue

            if t == "-D" and (i + 1) < len(toks):
                d = _norm_path_token(toks[i + 1])
                d = _expand_vars(d, rtl_dir, filelist_path)
                d = _norm_path_token(d)
                if d:
                    defines.append(d)
                i += 2
                continue

            if t in ("-F", "-f") and (i + 1) < len(toks):
                nested = _norm_path_token(toks[i + 1])
                nested = _expand_vars(nested, rtl_dir, filelist_path)
                nested = _norm_path_token(nested)

                if _is_unresolved_var_path(nested):
                    console.print(f"[yellow]⚠ Skipping unresolved nested filelist:[/yellow] {nested}")
                    i += 2
                    continue

                np = Path(nested)
                if not np.is_absolute():
                    np = (base_dir / np).resolve()
                else:
                    np = np.resolve()

                sub_files, include_dirs, defines = _parse_filelist(np, rtl_dir, include_dirs, defines, visited)
                files.extend(sub_files)
                i += 2
                continue

            if t == "-y" and (i + 1) < len(toks):
                i += 2
                continue

            if t == "-v" and (i + 1) < len(toks):
                fp = _norm_path_token(toks[i + 1])
                fp = _expand_vars(fp, rtl_dir, filelist_path)
                fp = _norm_path_token(fp)
                if _is_unresolved_var_path(fp):
                    console.print(f"[yellow]⚠ Skipping unresolved -v file:[/yellow] {fp}")
                else:
                    p = Path(fp)
                    if not p.is_absolute():
                        p = (rtl_dir / p).resolve()
                    else:
                        p = p.resolve()
                    if p.exists() and p.suffix.lower() in SV_SUFFIXES:
                        files.append(p)
                i += 2
                continue

            candidate = _expand_vars(t, rtl_dir, filelist_path)
            candidate = _norm_path_token(candidate)

            if _is_unresolved_var_path(candidate):
                console.print(f"[yellow]⚠ Skipping unresolved token:[/yellow] {t}")
                i += 1
                continue

            if candidate.startswith("-") or candidate.startswith("+"):
                i += 1
                continue

            p = Path(candidate)
            if not p.is_absolute():
                p1 = (rtl_dir / p).resolve()
                p2 = (base_dir / p).resolve()
                p = p1 if p1.exists() else p2
            else:
                p = p.resolve()

            if p.exists() and p.is_file() and p.suffix.lower() in SV_SUFFIXES:
                files.append(p)

            i += 1

    return files, include_dirs, defines


# ──────────────────────────────────────────────────────────────────────────────
# CSV validation + repair helpers (NEW)
# ──────────────────────────────────────────────────────────────────────────────
def _strip_code_fences(s: str) -> str:
    if not s:
        return ""
    s = s.strip()
    m = re.search(r"```(?:csv)?\s*([\s\S]*?)```", s, re.I)
    if m:
        return m.group(1).strip()
    return s


def _ensure_csv_header(csv_text: str) -> str:
    csv_text = csv_text.strip()
    if not csv_text:
        return csv_text
    lines = csv_text.splitlines()
    first = (lines[0] if lines else "").strip().lower().replace(" ", "")
    expected = ",".join(CSV_HEADER).lower().replace(" ", "")
    if first != expected:
        return ",".join(CSV_HEADER) + "\n" + csv_text
    return csv_text


def _split_csv_line(line: str) -> List[str]:
    # We REQUIRE "no commas inside fields" by prompt rule, so split is safe.
    return [c.strip() for c in line.rstrip("\n").split(",")]


def _extract_dotted_and_plain_identifiers(expr: str) -> List[str]:
    """
    Extract possible identifiers from an SV expression.

    Rules:
      - capture dotted refs: foo.bar.baz
      - capture plain refs: foo
      - DO NOT capture $rose/$fell/... as identifiers
      - ignore numbers/base literals ('0, 1'b0, 4'hF), and keywords
    """
    if not expr:
        return []

    # Remove strings to avoid accidental captures
    expr2 = re.sub(r"\"[^\"]*\"", " ", expr)

    # Temporarily remove allowed $functions so we don't treat their names as identifiers
    for fn in _ALLOWED_SVA_FUNCS:
        expr2 = expr2.replace(fn, " ")

    # Capture dotted tokens first
    dotted = re.findall(r"\b[A-Za-z_]\w*(?:\.[A-Za-z_]\w*)+\b", expr2)

    # Then capture plain identifiers
    plain = re.findall(r"\b[A-Za-z_]\w*\b", expr2)

    # Filter out pieces of dotted from plain list (we want full dotted tokens)
    dotted_set = set(dotted)
    plain_filtered = []
    for p in plain:
        if p in dotted_set:
            continue
        # ignore keywords
        if p.lower() in _SV_KEYWORDS:
            continue
        plain_filtered.append(p)

    # Also filter dotted components that are actually keywords (rare)
    dotted_filtered = []
    for d in dotted:
        if d.lower() in _SV_KEYWORDS:
            continue
        dotted_filtered.append(d)

    # Remove base literal artifacts that can look like identifiers (e.g. 'b0' won't match anyway)
    out = dotted_filtered + plain_filtered

    # De-dup but preserve order
    seen = set()
    uniq = []
    for x in out:
        if x not in seen:
            uniq.append(x)
            seen.add(x)
    return uniq


def _base_port(tok: str) -> str:
    # req_port_o.data_req -> req_port_o
    return tok.split(".", 1)[0] if tok else tok


def _detect_nested_temporal(post: str) -> bool:
    """
    Jasper error you hit was from something like:
      ##[1:$] (wr_en && ##[1:$] rd_en)
    i.e., multiple '##' tokens inside a single post field.
    We flag that as invalid.
    """
    if not post:
        return False
    return post.count("##") > 1


def validate_csv_text(csv_text: str, allowed_ports: List[str]) -> Dict[str, Any]:
    """
    Validate:
      1) pre/post signal identifiers reference ONLY valid base ports
      2) signals column matches used base ports (space separated)
      3) post does not contain nested temporal operators
      4) correct column count
    """
    allowed_set = set(allowed_ports)

    report: Dict[str, Any] = {
        "ok": True,
        "errors": [],
        "invalid_identifiers": [],
        "signals_column_mismatches": [],
        "bad_rows": [],
        "nested_temporal": [],
    }

    csv_text = _ensure_csv_header(_strip_code_fences(csv_text))
    lines = [ln for ln in csv_text.splitlines() if ln.strip()]
    if not lines:
        report["ok"] = False
        report["errors"].append("empty_csv")
        return report

    # Header check
    hdr = lines[0].strip().lower().replace(" ", "")
    expected = ",".join(CSV_HEADER).lower().replace(" ", "")
    if hdr != expected:
        report["ok"] = False
        report["errors"].append("bad_header")

    # Validate rows
    for idx in range(1, len(lines)):
        line_no = idx + 1
        cols = _split_csv_line(lines[idx])
        if len(cols) != len(CSV_HEADER):
            report["ok"] = False
            report["bad_rows"].append({"line": line_no, "reason": "wrong_column_count", "cols": len(cols), "text": lines[idx]})
            continue

        row = dict(zip(CSV_HEADER, cols))
        sid = row.get("sid", "").strip()

        pre = row.get("pre", "").strip()
        post = row.get("post", "").strip()
        sigs_col = row.get("signals", "").strip()

        # nested temporal check
        if _detect_nested_temporal(post):
            report["ok"] = False
            report["nested_temporal"].append({"line": line_no, "sid": sid, "post": post})

        used = _extract_dotted_and_plain_identifiers(pre) + _extract_dotted_and_plain_identifiers(post)
        used_base_ports = []
        invalid = []

        for u in used:
            # skip if it is clearly a local macro-ish keyword (unlikely)
            if u.lower() in _SV_KEYWORDS:
                continue
            base = _base_port(u)
            # Filter out accidental captures that are actually language tokens
            if base.lower() in _SV_KEYWORDS:
                continue
            # Allow only if base is a real port
            if base not in allowed_set:
                invalid.append(u)
            else:
                used_base_ports.append(base)

        if invalid:
            report["ok"] = False
            report["invalid_identifiers"].append(
                {"line": line_no, "sid": sid, "invalid": sorted(set(invalid)), "pre": pre, "post": post}
            )

        # signals column match check (base ports)
        sigs_list = [s for s in sigs_col.split() if s]
        sigs_set = set(sigs_list)
        used_set = set(used_base_ports)

        # If expressions use no ports (e.g., "1"), we accept empty signals, but prompt expects correctness.
        # We'll be conservative: if used_set is empty, don't flag mismatch.
        if used_set:
            if sigs_set != used_set:
                report["ok"] = False
                report["signals_column_mismatches"].append(
                    {
                        "line": line_no,
                        "sid": sid,
                        "expected": " ".join(sorted(used_set)),
                        "got": sigs_col,
                        "used_in_expr": sorted(used_set),
                    }
                )

    return report


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
        self.slang_bin = slang_bin
        self.rtl_dir = rtl_dir
        self.top = top
        self.design_top = design_top or top
        self.out_dir = out_dir
        self.llm_conf = llm_conf
        self.include_dirs = include_dirs or []
        self.defines = defines or []
        self.disable_analysis = disable_analysis
        self.filelist = filelist

        _ensure_dir(self.out_dir)

        self.out_json = self.out_dir / f'{self.top}_ast.json'
        self.out_md = self.out_dir / f'{self.top}_spec.md'
        self.out_csv = self.out_dir / f'{self.top}_spec.csv'
        self.logic_snap = self.out_dir / f'{self.top}_logic_blocks.json'

        if not self.llm_conf.exists():
            console.print(f'[red]❌ LLM config not found: {self.llm_conf}[/red]')
            raise SystemExit(2)

        console.print(f'[cyan][LLM] Using config:[/cyan] {self.llm_conf}')
        self.llm = LLM_wrap(name='default', conf_file=str(self.llm_conf), log_file='spec_llm.log')
        self.tmpl = LLM_template(str(self.llm_conf))
        self.template_dict = getattr(self.tmpl, 'template_dict', {}) or {}

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
        try:
            from hagent.tool.utils.hdl_utils import find_sv_files  # type: ignore[attr-defined]
            files = find_sv_files(self.rtl_dir, skip_dirs=set())
            return sorted([Path(f) for f in files])
        except Exception as e:  # pragma: no cover
            console.print(f'[yellow]⚠ find_sv_files failed; falling back. ({e})[/yellow]')
            return [p for p in self.rtl_dir.rglob('*') if p.suffix in SV_SUFFIXES]

    def _files_from_filelist(self) -> List[Path]:
        if self.filelist is None:
            return []
        fl = self.filelist
        if not fl.exists():
            console.print(f'[red]❌ Filelist not found: {fl}[/red]')
            raise SystemExit(2)

        console.print(f'[cyan]• Using HDL filelist:[/cyan] {fl}')

        visited: Set[Path] = set()
        files, incs, defs = _parse_filelist(
            filelist_path=fl.resolve(),
            rtl_dir=self.rtl_dir.resolve(),
            include_dirs=list(self.include_dirs),
            defines=list(self.defines),
            visited=visited,
        )

        def _uniq_paths(xs: List[Path]) -> List[Path]:
            out: List[Path] = []
            seen = set()
            for p in xs:
                rp = str(p.resolve())
                if rp not in seen:
                    out.append(p)
                    seen.add(rp)
            return out

        def _uniq_strs(xs: List[str]) -> List[str]:
            out: List[str] = []
            seen = set()
            for s in xs:
                if s not in seen:
                    out.append(s)
                    seen.add(s)
            return out

        self.include_dirs = _uniq_paths(incs)
        self.defines = _uniq_strs(defs)

        if not files:
            console.print(f'[red]❌ No valid RTL files found in filelist after parsing: {fl}[/red]')
            raise SystemExit(2)

        console.print(f'[green]✔ Filelist parsed RTL files:[/green] {len(files)}')
        if self.include_dirs:
            console.print(f'[green]✔ Filelist include dirs:[/green] {len(self.include_dirs)}')
        if self.defines:
            console.print(f'[green]✔ Filelist defines:[/green] {len(self.defines)}')

        return files

    def _resolve_required(self, all_rtl: List[Path]) -> List[Path]:
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
            self.top,
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
    # NEW: CSV repair loop using LLM
    # ──────────────────────────────────────────────────────────────────────
    def _repair_csv_with_llm(self, csv_text: str, allowed_ports: List[str], report: Dict[str, Any]) -> str:
        """
        Uses prompt_index='csv_repair' if it exists in YAML.
        If not present, returns original csv_text unchanged.
        """
        if not self.template_dict.get('default', {}).get('csv_repair'):
            console.print("[yellow]⚠ No 'csv_repair' prompt found in spec_prompt.yaml; cannot LLM-repair CSV.[/yellow]")
            return csv_text

        payload = {
            "top_module": self.top,
            "allowed_ports_json": json.dumps(allowed_ports, ensure_ascii=False),
            "csv_text": csv_text,
            "validation_json": json.dumps(report, ensure_ascii=False),
            "rules_json": json.dumps(
                {
                    "header": ",".join(CSV_HEADER),
                    "allowed_sva_funcs": sorted(_ALLOWED_SVA_FUNCS),
                    "allow_field_select": True,
                    "no_nested_temporal": True,
                    "signals_column_base_ports": True,
                },
                ensure_ascii=False,
            ),
        }
        fixed = self._llm("csv_repair", payload)
        fixed = _ensure_csv_header(_strip_code_fences(fixed))
        return fixed

    # ──────────────────────────────────────────────────────────────────────
    # Build context and generate artifacts
    # ──────────────────────────────────────────────────────────────────────
    def run(self) -> None:
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

        self._run_slang(req_files)

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

        def fsm_summary(b):
            return {
                'expr_symbol': b.get('expr_symbol') or 'state',
                'source': os.path.basename(b.get('source_file') or ''),
                'line_start': b.get('line_start'),
                'line_end': b.get('line_end'),
                'rtl_excerpt': (b.get('rtl_code') or '')[:4000],
            }

        allowed_ports = [p['name'] for p in ports]  # base ports only

        ctx = {
            'top_module': self.top,
            'design_top': self.design_top,
            'clock': self.clk,
            'reset': self.rst,
            'reset_expr': self.rst_expr,
            'ports': ports,
            'params': params,
            'fsms': [fsm_summary(b) for b in fsms],
            'logic_blocks': logic[:200],
            'csv_head': CSV_HEADER,
            'allowed_signals': allowed_ports,
            'notes': [
                "CSV pre/post may ONLY reference RTL IO ports from allowed_signals.",
                "Field-selects are permitted ONLY if the base port exists (e.g., req_port_o.data_req).",
                "signals column must list BASE PORTS only, space-separated, matching ports used in pre/post.",
                "post must NOT contain nested temporal operators (no more than one '##' token).",
                f"Allowed $functions: {', '.join(sorted(_ALLOWED_SVA_FUNCS))}",
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

        # 7) Generate CSV via LLM
        console.print('[cyan]• LLM: sva_row_list_csv[/cyan]')
        csv_raw = self._llm('sva_row_list_csv', {'context_json': json.dumps(ctx, ensure_ascii=False)}).strip()
        csv_raw = _ensure_csv_header(_strip_code_fences(csv_raw))

        if not csv_raw.strip():
            console.print('[red]❌ LLM produced empty CSV text.[/red]')
            raise SystemExit(2)

        # NEW: validate + repair loop
        report = validate_csv_text(csv_raw, allowed_ports)
        report_path = self.out_dir / f"{self.top}_spec.csv.validation.json"
        _write_json(report_path, report)

        if not report.get("ok", False):
            console.print("[yellow]⚠ CSV validation failed. Attempting repair...[/yellow]")
            console.print(f"  invalid_identifiers rows: {len(report.get('invalid_identifiers', []))}")
            console.print(f"  signals_column_mismatches: {len(report.get('signals_column_mismatches', []))}")
            console.print(f"  bad_rows: {len(report.get('bad_rows', []))}")
            console.print(f"  nested_temporal: {len(report.get('nested_temporal', []))}")

            broken_path = self.out_dir / f"{self.top}_spec.csv.broken"
            _write_text(broken_path, csv_raw)

            repaired = csv_raw
            max_attempts = 2
            for attempt in range(1, max_attempts + 1):
                repaired = self._repair_csv_with_llm(repaired, allowed_ports, report)
                repaired = _ensure_csv_header(_strip_code_fences(repaired))
                report = validate_csv_text(repaired, allowed_ports)
                _write_json(report_path, report)
                if report.get("ok", False):
                    console.print(f"[green]✔ CSV repaired on attempt {attempt}.[/green] Broken backup saved to: {broken_path}")
                    csv_raw = repaired
                    break
                else:
                    console.print(f"[yellow]⚠ Repair attempt {attempt} still invalid.[/yellow]")

            if not report.get("ok", False):
                _write_text(self.out_csv, repaired)
                console.print(f"[red]❌ CSV still invalid after repair attempts. Wrote latest to: {self.out_csv}[/red]")
                console.print(f"[red]Validation report: {json.dumps(report, indent=2)}[/red]")
                raise SystemExit(2)

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
    p.add_argument('--design-top', help='Design top module name (defaults to --top)')
    p.add_argument('--out', required=True, help='Output directory')
    p.add_argument('--llm-conf', required=True, help='YAML prompt config (spec_prompt.yaml)')
    p.add_argument('--include', action='append', default=[], help='Additional include dirs (-I)')
    p.add_argument('--define', action='append', default=[], help='Slang defines (e.g., FOO=1)')
    p.add_argument('--filelist', help='Optional HDL filelist. If provided, discovery is skipped.')
    p.add_argument('--no-disable-analysis', action='store_true', help='Enable Slang analysis (default: disabled)')
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
