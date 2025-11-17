#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Clock/Reset detection utilities for Formal Agent
------------------------------------------------
Detects clock and reset signals for the *top module* only,
including polarity inference for reset (active-high or active-low).

Supports:
  - Standard naming (clk, clock, rst, reset)
  - Lower or upper case variants (CLK, PRESETn, RESET_B, etc.)
  - Polarity inference via suffix (_n, _ni, _b, _bar, _l)
  - Hints from comments (e.g. "active low")
"""

import re
from pathlib import Path
from typing import Tuple
from rich.console import Console

console = Console()


# -----------------------------------------------------------------------------
#  Reset polarity inference
# -----------------------------------------------------------------------------
def infer_reset_polarity(name: str, text: str = "") -> Tuple[str, str]:
    """
    Infer reset polarity from name or surrounding text.
    Returns (rst_name, rst_expr), where rst_expr is the form used in TCL.
    Example:
        infer_reset_polarity("rst_n")       -> ("rst_n", "(!rst_n)")
        infer_reset_polarity("RESET_B")     -> ("RESET_B", "(!RESET_B)")
        infer_reset_polarity("rst_i")       -> ("rst_i", "rst_i")
        infer_reset_polarity("reset", "active low reset") -> ("reset", "(!reset)")
    """
    name_low = name.lower()
    # typical active-low patterns
    polarity_low = any(
        kw in name_low for kw in ("_n", "_ni", "_b", "_bar", "_l")
    )
    # also detect from comment hint text
    if not polarity_low and re.search(r"active\s*low", text, re.I):
        polarity_low = True

    rst_expr = f"(!{name})" if polarity_low else name
    return name, rst_expr


# -----------------------------------------------------------------------------
#  Top-level detection
# -----------------------------------------------------------------------------

def detect_clk_rst_for_top(rtl_dir: Path, top_module: str):
    """
    Strict, industry-grade clock/reset detector.
    - Only searches the top module's port list.
    - Case-insensitive.
    - Detects names matching clk, clock, rst, reset.
    - Infers active-low via suffix (_n, _b, _ni, _l, _bar).
    - Never falls back to scanning the entire directory (prevents false matches).
    """

    clk_default = "clk"
    rst_default = "rst"
    clk_found = None
    rst_found = None

    # Regex for module header (ANSI style)
    mod_re = re.compile(
        rf"module\s+{re.escape(top_module)}\s*(?:#\s*\([^)]*\))?\s*\((?P<ports>[^;]*)\);",
        re.S | re.I,
    )

    # Case-insensitive regexes for clk/rst
    clk_regex = re.compile(r"\b([A-Za-z_]\w*(clk|clock)\w*)\b", re.I)
    rst_regex = re.compile(r"\b([A-Za-z_]\w*(rst|reset)\w*)\b", re.I)

    # Active-low suffix patterns
    low_suffixes = ("_n", "_ni", "_b", "_bar", "_l")

    # Search all SV/V files for module header
    for p in rtl_dir.rglob("*.sv"):
        txt = p.read_text(errors="ignore")
        m = mod_re.search(txt)
        if not m:
            continue

        ports = m.group("ports")

        # Detect clock(s)
        clk_cands = [c[0] for c in clk_regex.findall(ports)]
        # Detect reset(s)
        rst_cands = [r[0] for r in rst_regex.findall(ports)]

        # Choose shortest reasonable matching names
        if clk_cands:
            clk_found = sorted(clk_cands, key=lambda s: (len(s), s.lower()))[0]
        if rst_cands:
            rst_found = sorted(rst_cands, key=lambda s: (len(s), s.lower()))[0]

        break  # Found top module; stop scanning

    # Final clock name
    clk_name = clk_found if clk_found else clk_default
    rst_name = rst_found if rst_found else rst_default

    # Polarity inference
    rst_low = rst_name.lower().endswith(low_suffixes)
    rst_expr = f"(!{rst_name})" if rst_low else rst_name

    console.print(
        f"[green]✔[/green] Top module clock=[bold]{clk_name}[/bold], reset=[bold]{rst_name}[/bold] "
        f"(expression: [cyan]{rst_expr}[/cyan])"
    )

    return clk_name, rst_name, rst_expr

