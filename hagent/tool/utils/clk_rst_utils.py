#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Clock / reset auto-detect helper for hagent.

This version is intentionally simple and robust:

* It scans the RTL under `src_root` for the top module definition.
* It extracts the module's port names from the **header port list**.
* It looks for a clock-like name (containing "clk" or "clock").
* It looks for a reset-like name (containing "rst" or "reset").
* If nothing obvious is found, it **falls back to `clk` and `rst`**
  instead of failing.
* If the environment variables HAGENT_CLK_NAME / HAGENT_RESET_EXPR
  are set, they override everything.
"""

import os
import re
from pathlib import Path
from rich.console import Console

console = Console()

# Regex template for the top module header
MODULE_RE_TMPL = r"module\s+{top}\s*(?:#\s*\([^;]*\))?\s*\((?P<ports>.*?)\)\s*;"


def _find_top_file(src_root: Path, top: str) -> Path | None:
    """Search all .sv files under src_root for `module <top> (...)`."""
    pat = re.compile(MODULE_RE_TMPL.format(top=re.escape(top)), re.S)
    for f in src_root.rglob("*.sv"):
        try:
            txt = f.read_text(errors="ignore")
        except OSError:
            continue
        if pat.search(txt):
            return f
    return None


def _extract_port_names(text: str, top: str) -> list[str]:
    """Extract port names from the ANSI-style header of the top module."""
    m = re.search(MODULE_RE_TMPL.format(top=re.escape(top)), text, re.S)
    if not m:
        return []

    ports_blob = m.group("ports")
    names: list[str] = []

    # Very tolerant: split by commas, strip types and ranges, keep last token
    for chunk in ports_blob.replace("\n", " ").split(","):
        chunk = chunk.strip()
        if not chunk:
            continue
        # Drop line comments inside the chunk
        chunk = re.sub(r"//.*$", "", chunk)
        if not chunk:
            continue
        tokens = chunk.split()
        if not tokens:
            continue
        name = tokens[-1]
        # Strip unpacked ranges from name like buf_mem[0:FIFO_DEPTH-1]
        name = re.sub(r"\[.*?\]", "", name).strip()
        if name:
            names.append(name)
    return names


def _pick_clk_rst(port_names: list[str]) -> tuple[str, str]:
    """Choose clock/reset candidates from the list of port names."""
    clk_candidates = [
        p for p in port_names
        if "clk" in p.lower() or "clock" in p.lower()
    ]
    rst_candidates = [
        p for p in port_names
        if "rst" in p.lower() or "reset" in p.lower()
    ]

    clk = clk_candidates[0] if clk_candidates else "clk"
    rst = rst_candidates[0] if rst_candidates else "rst"
    return clk, rst


def detect_clk_rst_for_top(src_root, top: str):
    """
    Return (clock_name, reset_name, reset_expr).

    * Honors env overrides:
        HAGENT_CLK_NAME
        HAGENT_RESET_EXPR
    * Otherwise uses heuristics on the top module's ports.
    * Never hard-fails just because heuristics didn't find anything;
      it falls back to 'clk' and 'rst'.
    """
    src_root = Path(src_root).resolve()

    # 1) Environment overrides win if both are present
    env_clk = os.environ.get("HAGENT_CLK_NAME")
    env_rst_expr = os.environ.get("HAGENT_RESET_EXPR")
    if env_clk and env_rst_expr:
        # Best effort: infer plain reset name from expression
        rst_name_tokens = re.sub(r"[!()]", " ", env_rst_expr).split()
        rst_name = rst_name_tokens[-1] if rst_name_tokens else env_rst_expr

        console.print(
            f"[green]✔ Top module clock={env_clk}, reset={rst_name} "
            f"(expression: {env_rst_expr}) from environment[/green]"
        )
        return env_clk, rst_name, env_rst_expr

    # 2) Find RTL file containing the top module
    console.print(
        f"[cyan]🔍 Scanning for top module {top} under {src_root}[/cyan]"
    )
    top_file = _find_top_file(src_root, top)
    if top_file is None:
        raise SystemExit(
            f"ERROR: Could not find module '{top}' under {src_root}"
        )

    try:
        txt = top_file.read_text(errors="ignore")
    except OSError as e:
        raise SystemExit(f"ERROR: Cannot read {top_file}: {e}") from e

    port_names = _extract_port_names(txt, top)

    if not port_names:
        console.print(
            "[yellow]⚠ Could not parse port list for top module; "
            "falling back to 'clk' and 'rst'.[/yellow]"
        )
        clk_name, rst_name = "clk", "rst"
    else:
        clk_name, rst_name = _pick_clk_rst(port_names)

        if not any("clk" in p.lower() or "clock" in p.lower()
                   for p in port_names):
            console.print(
                "[yellow]⚠ No clock-like port found (no '*clk*' or '*clock*' "
                "in port names); falling back to 'clk'.[/yellow]"
            )
        if not any("rst" in p.lower() or "reset" in p.lower()
                   for p in port_names):
            console.print(
                "[yellow]⚠ No reset-like port found (no '*rst*' or '*reset*' "
                "in port names); falling back to 'rst'.[/yellow]"
            )

    # 3) Build a reset expression
    if rst_name.lower().endswith(("_n", "_ni")):
        rst_expr = f"!{rst_name}"
    else:
        rst_expr = rst_name

    console.print(
        f"[green]✔ Top module clock={clk_name}, reset={rst_name} "
        f"(expression: {rst_expr})[/green]"
    )
    return clk_name, rst_name, rst_expr

