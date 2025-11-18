#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Clock/reset auto-detection utilities.

Heuristic strategy (inspired by the old gen_dep_tcl_and_sva.py):

1) Read the top module file and strip comments.
2) Extract just the text of `module <top> ... endmodule`.
3) **Primary heuristic**: look for always/always_ff blocks with a pair:
       @(posedge <clk> or negedge <rst>)
       @(negedge <rst> or posedge <clk>)
   If found, use that (<clk>, <rst>) pair.
4) If no pair is found, fall back to:
   - Find clk / rst candidates ONLY in declarations that start with
     input|wire|logic|reg (so we ignore parameters like NrStorePipeRegs).
   - Optionally look at posedge/negedge sensitivity lists.
5) Rank candidates with simple heuristics and build reset expression
   (handle active-low rst_n, rst_ni, rst_b).
6) If HAGENT_CLK_NAME and HAGENT_RESET_EXPR are set, those win.
"""

import os
import re
from pathlib import Path

from rich.console import Console

console = Console()

# --------------------------------------------------------------------
# Basic utilities
# --------------------------------------------------------------------


def _strip_comments(text: str) -> str:
    """Remove // and /* */ comments."""
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)
    text = re.sub(r"//.*?$", "", text, flags=re.M)
    return text


def _find_top_file(src_root: Path, top: str) -> Path | None:
    """Locate the file that defines module <top>."""
    pat = re.compile(rf"\bmodule\s+{re.escape(top)}\b")
    for f in Path(src_root).rglob("*.sv"):
        try:
            txt = f.read_text(errors="ignore")
        except OSError:
            continue
        if pat.search(txt):
            return f
    return None


def _extract_module_text(full_text: str, top: str) -> str:
    """Slice out 'module <top> ... endmodule' from the file."""
    m = re.search(rf"\bmodule\s+{re.escape(top)}\b", full_text)
    if not m:
        return ""
    start = m.start()
    rest = full_text[start:]
    end_match = re.search(r"\bendmodule\b", rest)
    if end_match:
        return rest[: end_match.end()]
    return rest


def _extract_port_names(full_text: str, top: str) -> list[str]:
    """
    Collect port names from an ANSI-style header if present.

    This is only used to slightly prefer port signals over internal signals
    when ranking clk/rst candidates.
    """
    m = re.search(rf"\bmodule\s+{re.escape(top)}\b", full_text)
    if not m:
        return []

    start = m.end()
    end = full_text.find(");", start)
    if end == -1:
        return []

    header = full_text[start : end + 2]
    names: list[str] = []

    # Very lightweight parse: look for "<dir> ... <name>"
    decl_pat = re.compile(
        r"\b(input|output|inout)\b"   # direction
        r"[^,);]*"                    # type / range
        r"\b([A-Za-z_]\w*)\b",        # name
        flags=re.S,
    )

    for dm in decl_pat.finditer(header):
        name = dm.group(2)
        name = re.sub(r"\[.*?\]", "", name).strip()
        if name and name not in names:
            names.append(name)

    return names


# --------------------------------------------------------------------
# Candidate extraction (old-script-style + new always-pair heuristic)
# --------------------------------------------------------------------


def _is_likely_reset_name(name: str) -> bool:
    """
    Filter out bogus reset candidates like 'NrStorePipeRegs'.

    We only accept names where 'rst' or 'reset' appears in a reset-ish context:
    - startswith rst* / reset*
    - endswith *rst, *rst_n, *rst_ni, *rst_b, *reset, *reset_n
    - contains '_rst', 'rst_', '_reset', or 'reset_'
    """
    s = name.lower()

    if s.startswith(("rst", "reset")):
        return True
    if s.endswith(("rst", "rst_n", "rst_ni", "rst_b", "reset", "reset_n")):
        return True
    if "_rst" in s or "rst_" in s or "_reset" in s or "reset_" in s:
        return True

    return False


def _find_decl_clk_rst_candidates(module_text: str):
    """
    Find clk / rst names from signal declarations ONLY, like the old script:

        (input|wire|logic|reg) ... <name_with_clk>
        (input|wire|logic|reg) ... <name_with_rst|reset>

    For reset, we further filter with _is_likely_reset_name so that
    parameters like NrStorePipeRegs are NOT treated as reset signals.
    """
    clk_pat = re.compile(
        r"\b(?:input|wire|logic|reg)\b[^;]*?\b([A-Za-z_]\w*(?:clk|clock)\w*)",
        flags=re.I | re.S,
    )
    rst_pat = re.compile(
        r"\b(?:input|wire|logic|reg)\b[^;]*?\b([A-Za-z_]\w*(?:rst|reset)\w*)",
        flags=re.I | re.S,
    )

    clk_cands = {m.group(1) for m in clk_pat.finditer(module_text)}
    rst_raw = {m.group(1) for m in rst_pat.finditer(module_text)}
    rst_cands = {n for n in rst_raw if _is_likely_reset_name(n)}

    return list(clk_cands), list(rst_cands)


def _find_sensitivity_clk_rst(module_text: str):
    """
    Fallback: look for clk/rst in always sensitivity lists, e.g.

        always_ff @(posedge clk_i or negedge rst_ni)
    """
    clk_from_sens: list[str] = []
    rst_from_sens: list[str] = []

    clk_pos_pat = re.compile(
        r"\bposedge\s+([A-Za-z_]\w*(?:clk|clock)\w*)", flags=re.I
    )
    rst_edge_pat = re.compile(
        r"\b(?:posedge|negedge)\s+([A-Za-z_]\w*(?:rst|reset)\w*)", flags=re.I
    )

    for m in clk_pos_pat.finditer(module_text):
        clk_from_sens.append(m.group(1))
    for m in rst_edge_pat.finditer(module_text):
        rst_from_sens.append(m.group(1))

    return clk_from_sens, rst_from_sens


def _find_clk_rst_always_pair(module_text: str):
    """
    Strong heuristic: look for always/always_ff with both clk & rst:

        always_ff @(posedge <clk> or negedge <rst>)
        always_ff @(negedge <rst> or posedge <clk>)

    If found, return (clk, rst). Otherwise return (None, None).
    """
    # posedge clk or negedge rst
    pat1 = re.compile(
        r"always(?:_[a-zA-Z0-9]+)?\s*@\(\s*"
        r"posedge\s+([A-Za-z_]\w*)\s+or\s+negedge\s+([A-Za-z_]\w*)"
        r"\s*\)",
        flags=re.S,
    )
    # negedge rst or posedge clk
    pat2 = re.compile(
        r"always(?:_[a-zA-Z0-9]+)?\s*@\(\s*"
        r"negedge\s+([A-Za-z_]\w*)\s+or\s+posedge\s+([A-Za-z_]\w*)"
        r"\s*\)",
        flags=re.S,
    )

    m = pat1.search(module_text)
    if m:
        clk, rst = m.group(1), m.group(2)
        if _is_likely_reset_name(rst):
            return clk, rst

    m = pat2.search(module_text)
    if m:
        rst, clk = m.group(1), m.group(2)
        if _is_likely_reset_name(rst):
            return clk, rst

    return None, None


# --------------------------------------------------------------------
# Ranking + expression building
# --------------------------------------------------------------------


def _rank_clk(cands: list[str], port_names: set[str]) -> str:
    """Pick the most likely clock signal from candidates."""
    if not cands:
        return "clk"

    def score(name: str):
        s = name.lower()
        sc = 0
        # Strongly prefer ports
        if name in port_names:
            sc += 10
        # "clk"/"clock" presence
        if "clk" in s or "clock" in s:
            sc += 5
        # Prefer names that start with clk*/clock*
        if s.startswith(("clk", "clock")):
            sc += 3
        # *_i style convention (e.g. clk_i)
        if s.endswith("_i"):
            sc += 2
        # Tiny bump for exactly 'clk', but not dominant
        if s == "clk":
            sc += 1

        # Sort: higher score first, then shorter name, then ports first
        return (-sc, len(s), 0 if name in port_names else 1)

    return sorted(set(cands), key=score)[0]


def _rank_rst(cands: list[str], port_names: set[str]) -> str:
    """Pick the most likely reset signal from candidates."""
    if not cands:
        return "rst"

    # Preserve occurrence order but unique
    cands_set = list(dict.fromkeys(cands))

    def score(name: str):
        s = name.lower()
        sc = 0
        # Strongly prefer ports
        if name in port_names:
            sc += 10
        # Prefer names that start with rst/reset
        if s.startswith(("rst", "reset")):
            sc += 8
        # Active-low suffixes
        if s.endswith(("_n", "_ni", "_b")):
            sc += 5
        # *_rst or rst_ in the middle gets a bit
        if "_rst" in s or "rst_" in s:
            sc += 2
        # *_i small bump
        if s.endswith("_i"):
            sc += 1

        return (-sc, len(s), 0 if name in port_names else 1)

    return sorted(cands_set, key=score)[0]


def _build_rst_expr(rst_name: str) -> str:
    """Build Jasper reset expression from name (handle active-low)."""
    s = rst_name.lower()
    if s.endswith(("_n", "_ni", "_b")):
        return f"!{rst_name}"
    return rst_name


# --------------------------------------------------------------------
# Public API
# --------------------------------------------------------------------


def detect_clk_rst_for_top(src_root, top: str):
    """
    Auto-detect (clock_name, reset_name, reset_expr) for a given top module.

    - Honors HAGENT_CLK_NAME + HAGENT_RESET_EXPR if they are set
    - Otherwise, uses always-pair heuristic first, then declaration-based
      heuristics as a fallback.
    """
    src_root = Path(src_root).resolve()

    # 0) Environment override (for tricky cases)
    env_clk = os.environ.get("HAGENT_CLK_NAME")
    env_rst_expr = os.environ.get("HAGENT_RESET_EXPR")
    if env_clk and env_rst_expr:
        # Try to recover a "bare" reset signal name from the expression
        rst_tokens = re.sub(r"[!()]", " ", env_rst_expr).split()
        rst_name = rst_tokens[-1] if rst_tokens else env_rst_expr
        console.print(
            f"[green]✔ Top module clock={env_clk}, reset={rst_name} "
            f"(expression: {env_rst_expr}) from environment[/green]"
        )
        return env_clk, rst_name, env_rst_expr

    # 1) Locate and read the top file
    console.print(f"[cyan]🔍 Scanning for top module {top} under {src_root}[/cyan]")
    top_file = _find_top_file(src_root, top)
    if top_file is None:
        raise SystemExit(f"ERROR: Could not find module '{top}' under {src_root}")

    try:
        full_text = top_file.read_text(errors="ignore")
    except OSError as e:
        raise SystemExit(f"ERROR: Cannot read {top_file}: {e}") from e

    no_cmt = _strip_comments(full_text)
    module_text = _extract_module_text(no_cmt, top)

    if not module_text:
        clk_name, rst_name = "clk", "rst"
        rst_expr = _build_rst_expr(rst_name)
        console.print(
            f"[yellow]⚠ Could not extract module body; "
            f"using defaults clk={clk_name}, rst={rst_name} (expr={rst_expr}).[/yellow]"
        )
        return clk_name, rst_name, rst_expr

    # 2) Gather port names to help ranking
    port_names = set(_extract_port_names(no_cmt, top))

    # 3) Strong heuristic: always_ff @(posedge clk_i or negedge rst_ni)
    clk_pair, rst_pair = _find_clk_rst_always_pair(module_text)
    if clk_pair and rst_pair:
        clk_name = clk_pair
        rst_name = rst_pair
        rst_expr = _build_rst_expr(rst_name)
        console.print(
            f"[green]✔ Top module clock={clk_name}, reset={rst_name} "
            f"(expression: {rst_expr}) from always-block pair[/green]"
        )
        return clk_name, rst_name, rst_expr

    # 4) Main candidate extraction (declarations only, like the old script)
    clk_decls, rst_decls = _find_decl_clk_rst_candidates(module_text)

    # 5) Fallback: look at sensitivity lists
    clk_sens, rst_sens = _find_sensitivity_clk_rst(module_text)

    clk_cands = clk_decls or clk_sens
    rst_cands = rst_decls or rst_sens

    # 6) Rank + build expression
    clk_name = _rank_clk(clk_cands, port_names)
    rst_name = _rank_rst(rst_cands, port_names)
    rst_expr = _build_rst_expr(rst_name)

    console.print(
        f"[green]✔ Top module clock={clk_name}, reset={rst_name} (expression: {rst_expr})[/green]"
    )
    return clk_name, rst_name, rst_expr


# Legacy alias in case older code imports detect_clk_rst
def detect_clk_rst(src_root, top: str):
    return detect_clk_rst_for_top(src_root, top)

