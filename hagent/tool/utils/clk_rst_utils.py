#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Clock/Reset detection utilities for Formal Agent
------------------------------------------------
Detects clock and reset signals for the *top module* only,
including polarity inference for reset (active-high or active-low).

Key behavior:
  - ONLY looks at the given top module's port list.
  - NO FALLBACK: if no clock or reset is found, it raises an error.
  - Prints all candidate clock/reset names it finds.
  - Picks a single "best" clock/reset to return (shortest name).

Supports:
  - Standard naming (clk, clock, rst, reset)
  - Prefix/suffix variants (clk_i, core_clk, rst_ni, reset_n, RESET_B, etc.)
  - Lower or upper case variants
  - Polarity inference via suffix (_n, _ni, _b, _bar, _l)
  - Optional hints from comments (e.g. "active low")
"""

import re
from pathlib import Path
from typing import Tuple
from rich.console import Console

console = Console()

# -------------------------------------------------------------------------
#  Reset polarity inference
# -------------------------------------------------------------------------


def infer_reset_polarity(name: str, text: str = "") -> Tuple[str, str, bool]:
    """
    Infer reset polarity from name or surrounding text.

    Returns:
        (rst_name, rst_expr, active_low)

    Examples:
        infer_reset_polarity("rst_n")           -> ("rst_n", "(!rst_n)", True)
        infer_reset_polarity("RESET_B")         -> ("RESET_B", "(!RESET_B)", True)
        infer_reset_polarity("rst_i")           -> ("rst_i", "rst_i", False)
        infer_reset_polarity("reset", "active low reset")
                                               -> ("reset", "(!reset)", True)
    """
    name_low = name.lower()

    # typical active-low patterns in the name
    polarity_low = any(
        name_low.endswith(sfx) for sfx in ("_n", "_ni", "_b", "_bar", "_l")
    )

    # also detect from comment/text hint
    if not polarity_low and re.search(r"active\s*low", text, re.I):
        polarity_low = True

    rst_expr = f"(!{name})" if polarity_low else name
    return name, rst_expr, polarity_low


# -------------------------------------------------------------------------
#  Top-level detection
# -------------------------------------------------------------------------


def detect_clk_rst_for_top(rtl_dir: Path, top_module: str):
    """
    Strict clock/reset detector for the given top module.

    - Searches ONLY the top module's port list (ANSI-style header).
    - Case-insensitive.
    - Detects *all* port names that look like clocks/resets:
         clock:  names containing 'clk' or 'clock'
         reset:  names containing 'rst' or 'reset'
    - Prints all candidates it finds.
    - Chooses a single "best" clock/reset (shortest name, then lexicographic).
    - Infers active-low polarity for the chosen reset.
    - NO FALLBACK: if either clock or reset is not found,
      it prints a clear warning and raises ValueError.

    Returns:
        (clk_name, rst_name, rst_expr, active_low)
    """

    rtl_dir = Path(rtl_dir)

    # Regex for module header (ANSI style):
    #   module top #( ... ) ( ... );
    mod_re = re.compile(
        rf"module\s+{re.escape(top_module)}\s*"
        r"(?:#\s*\([^)]*\)\s*)?"  # optional parameter block
        r"\((?P<ports>[^;]*)\)\s*;",
        re.S | re.I,
    )

    # Case-insensitive regexes for clk/rst *port names*
    # We capture the whole identifier as group[0].
    clk_regex = re.compile(r"\b([A-Za-z_]\w*(?:clk|clock)\w*)\b", re.I)
    rst_regex = re.compile(r"\b([A-Za-z_]\w*(?:rst|reset)\w*)\b", re.I)

    clk_candidates = []
    rst_candidates = []

    top_source_file = None
    ports_text = ""

    # Search all *.sv (you can add *.v if needed)
    for p in rtl_dir.rglob("*.sv"):
        text = p.read_text(errors="ignore")
        m = mod_re.search(text)
        if not m:
            continue

        top_source_file = p
        ports_text = m.group("ports")

        clk_candidates = [m[0] for m in clk_regex.findall(ports_text)]
        rst_candidates = [m[0] for m in rst_regex.findall(ports_text)]
        break  # Found the top module; stop scanning other files

    # If we never found the top module at all
    if top_source_file is None:
        msg = f"Top module '{top_module}' not found under {rtl_dir}"
        console.print(f"[red]❌ {msg}[/red]")
        raise ValueError(msg)

    # De-duplicate and sort candidates
    clk_candidates = sorted(set(clk_candidates), key=lambda s: (len(s), s.lower()))
    rst_candidates = sorted(set(rst_candidates), key=lambda s: (len(s), s.lower()))

    # Log what we found
    console.print(
        f"[cyan]🔍 Scanning top module[/cyan] [bold]{top_module}[/bold] "
        f"in [magenta]{top_source_file}[/magenta]"
    )

    if clk_candidates:
        console.print(
            "[green]• Candidate clock ports:[/green] "
            + ", ".join(f"[bold]{c}[/bold]" for c in clk_candidates)
        )
    else:
        console.print("[yellow]⚠ No clock-like ports found (no '*clk*' or '*clock*' in port names).[/yellow]")

    if rst_candidates:
        console.print(
            "[green]• Candidate reset ports:[/green] "
            + ", ".join(f"[bold]{r}[/bold]" for r in rst_candidates)
        )
    else:
        console.print("[yellow]⚠ No reset-like ports found (no '*rst*' or '*reset*' in port names).[/yellow]")

    # NO FALLBACK: if either is missing, stop here
    if not clk_candidates or not rst_candidates:
        msg = (
            f"Could not auto-detect clock/reset for top '{top_module}'. "
            "Please specify them explicitly (or extend clk_rst_utils heuristics)."
        )
        console.print(f"[red]❌ {msg}[/red]")
        raise ValueError(msg)

    # Choose "best" candidate = shortest name, then lexicographic
    clk_name = clk_candidates[0]
    rst_raw = rst_candidates[0]

    # Infer polarity for the chosen reset
    rst_name, rst_expr, active_low = infer_reset_polarity(rst_raw, ports_text)

    console.print(
        "[green]✔[/green] Using clock="
        f"[bold]{clk_name}[/bold], reset="
        f"[bold]{rst_name}[/bold] "
        f"(expression: [cyan]{rst_expr}[/cyan], "
        f"active_low={str(active_low).lower()})"
    )

    # Return with active_low flag as a 4th element so callers that expect
    # (clk, rst, rst_expr) or (clk, rst, rst_expr, active_low) both work.
    return clk_name, rst_name, rst_expr, active_low

