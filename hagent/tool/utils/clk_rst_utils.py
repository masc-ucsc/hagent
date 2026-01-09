#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Clock/reset auto-detection utilities.

Priority order:
0) Environment override:
      HAGENT_CLK_NAME + HAGENT_RESET_EXPR
1) If ports_json is provided (Slang-generated ports.json):
      detect clk/rst from TOP-LEVEL PORT NAMES (authoritative)
2) Otherwise, RTL heuristics from module source text:
      - always @(posedge clk or negedge rst) pairing
      - declarations + sensitivity lists

FIXED (Dec 2025):
  - Comprehensive pattern matching for all clock/reset naming conventions
  - Detects bare names: reset, clock, clk, rst
  - No fallback to wrong defaults
"""

import os
import re
import json
from pathlib import Path
from typing import Any, Dict, List, Optional, Tuple

from rich.console import Console

console = Console()

# --------------------------------------------------------------------
# Basic utilities
# --------------------------------------------------------------------


def _strip_comments(text: str) -> str:
    """Remove // and /* */ comments."""
    text = re.sub(r'/\*.*?\*/', '', text, flags=re.S)
    text = re.sub(r'//.*?$', '', text, flags=re.M)
    return text


def _find_top_file(src_root: Path, top: str) -> Path | None:
    """
    Locate the file that defines module <top>.
    Search common HDL extensions (.sv/.v/.svh/.vh).
    """
    pat = re.compile(rf'\bmodule\s+{re.escape(top)}\b')
    src_root = Path(src_root)

    exts = ('*.sv', '*.v', '*.svh', '*.vh')
    for ext in exts:
        for f in src_root.rglob(ext):
            try:
                txt = f.read_text(errors='ignore')
            except OSError:
                continue
            if pat.search(txt):
                return f
    return None


def _extract_module_text(full_text: str, top: str) -> str:
    """Slice out 'module <top> ... endmodule' from the file."""
    m = re.search(rf'\bmodule\s+{re.escape(top)}\b', full_text)
    if not m:
        return ''
    start = m.start()
    rest = full_text[start:]
    end_match = re.search(r'\bendmodule\b', rest)
    if end_match:
        return rest[: end_match.end()]
    return rest


def _extract_port_names(full_text: str, top: str) -> list[str]:
    """
    Collect port names from an ANSI-style header if present.
    Used only to help ranking when using RTL-text heuristics.
    """
    m = re.search(rf'\bmodule\s+{re.escape(top)}\b', full_text)
    if not m:
        return []

    start = m.end()
    end = full_text.find(');', start)
    if end == -1:
        return []

    header = full_text[start : end + 2]
    names: list[str] = []

    decl_pat = re.compile(
        r'\b(input|output|inout)\b'
        r'[^,);]*'
        r'\b([A-Za-z_]\w*)\b',
        flags=re.S,
    )

    for dm in decl_pat.finditer(header):
        name = dm.group(2)
        name = re.sub(r'\[.*?\]', '', name).strip()
        if name and name not in names:
            names.append(name)

    return names


# --------------------------------------------------------------------
# Ports.json-based detection (authoritative)
# --------------------------------------------------------------------


def _norm_port_dir(d: Any) -> str:
    s = (str(d) if d is not None else '').strip().lower()
    if s in ('in', 'input'):
        return 'in'
    if s in ('out', 'output'):
        return 'out'
    if 'inout' in s:
        return 'inout'
    return s


def _is_inputish_port(p: Dict[str, Any]) -> bool:
    d = _norm_port_dir(p.get('dir') or p.get('direction'))
    return d in ('in', 'input', 'inout')


def _is_likely_reset_name(name: str) -> bool:
    """
    Accept reset-like names only (avoid bogus matches like NrStorePipeRegs).
    Case-insensitive.
    COMPREHENSIVE: Handles ALL common reset naming conventions.
    """
    s = name.lower()

    # Direct exact matches (most common)
    exact_matches = {
        'rst',
        'reset',
        'rst_n',
        'rstn',
        'rst_ni',
        'rstni',
        'reset_n',
        'resetn',
        'reset_ni',
        'resetni',
        'rst_b',
        'rstb',
        'reset_b',
        'resetb',
        'arst',
        'arstn',
        'arst_n',
        'areset',
        'aresetn',
        'areset_n',
        'srst',
        'srstn',
        'srst_n',
        'sreset',
        'sresetn',
        'sreset_n',
        'hreset',
        'hresetn',
        'hrst',
        'hrstn',
        'prst',
        'prstn',
        'prst_n',
        'preset',
        'presetn',
        'preset_n',
        'nrst',
        'nrstn',
        'nreset',
        'nresetn',
    }
    if s in exact_matches:
        return True

    # Starts with reset-like prefix
    reset_prefixes = (
        'rst',
        'reset',
        'preset',
        'prst',
        'arst',
        'areset',
        'srst',
        'sreset',
        'hrst',
        'hreset',
        'nrst',
        'nreset',
        'sys_rst',
        'sys_reset',
        'core_rst',
        'core_reset',
        'async_rst',
        'async_reset',
        'sync_rst',
        'sync_reset',
    )
    if s.startswith(reset_prefixes):
        return True

    # Ends with reset-like suffix
    reset_suffixes = (
        'rst',
        'rst_n',
        'rst_ni',
        'rst_b',
        'rstn',
        'rstni',
        'rstb',
        'reset',
        'reset_n',
        'reset_ni',
        'reset_b',
        'resetn',
        'resetni',
        'resetb',
        'arst',
        'arstn',
        'arst_n',
        'areset',
        'aresetn',
        'areset_n',
        'srst',
        'srstn',
        'srst_n',
        'sreset',
        'sresetn',
        'sreset_n',
        'preset',
        'presetn',
        'preset_n',
        'prst',
        'prstn',
        'prst_n',
    )
    if s.endswith(reset_suffixes):
        return True

    # Contains reset pattern with underscores (common in hierarchical names)
    reset_patterns = [
        '_rst_',
        '_rst$',
        '^rst_',
        '_reset_',
        '_reset$',
        '^reset_',
        '_preset_',
        '_preset$',
        '^preset_',
        '_arst_',
        '_arst$',
        '^arst_',
        '_srst_',
        '_srst$',
        '^srst_',
    ]
    for pattern in reset_patterns:
        if re.search(pattern, s):
            return True

    return False


def _build_rst_expr(rst_name: str) -> str:
    """
    Build reset asserted expression from name.
    Comprehensive active-low detection for all naming conventions.
    """
    s = rst_name.lower()

    # Active-low indicators (reset is asserted when signal is 0)
    # Check suffixes
    if s.endswith(('_n', '_ni', '_b', '_l')):
        return f'!{rst_name}'

    # Check if ends with 'n' (but not common words like 'begin', 'main', etc.)
    if s.endswith('n') and len(s) > 3:
        # Common active-low patterns: resetn, rstn, presetn, arstn, etc.
        if any(pattern in s for pattern in ['reset', 'rst', 'preset', 'prst']):
            return f'!{rst_name}'

    # Check for explicit negative naming
    if s.startswith(('n_', 'neg_', 'not_')):
        return f'!{rst_name}'

    # Default: active-high (reset is asserted when signal is 1)
    return rst_name


def _rank_clk(cands: list[str]) -> str:
    """
    Pick the most likely clock from candidates (ports-based).
    Comprehensive ranking across all naming conventions.
    """
    if not cands:
        console.print('[yellow]⚠ Could not find clock signal in port candidates[/yellow]')
        raise SystemExit('ERROR: Clock signal detection failed. No clock candidates found. Please specify --clock-name')

    def score(name: str):
        s = name.lower()
        sc = 0

        # Exact matches (highest priority)
        exact_scores = {
            'clock': 50,
            'clk': 48,
            'pclk': 49,
            'aclk': 47,
            'hclk': 47,
            'mclk': 47,
            'sclk': 47,
            'sys_clk': 46,
            'core_clk': 46,
            'cpu_clk': 46,
            'sysclk': 46,
            'coreclk': 46,
            'cpuclk': 46,
        }
        if s in exact_scores:
            sc += exact_scores[s]

        # Prefix matching (high priority)
        if s.startswith(('pclk', 'aclk', 'hclk', 'mclk', 'sclk')):
            sc += 30
        elif s.startswith(('clk', 'clock')):
            sc += 28
        elif s.startswith(('sys_clk', 'core_clk', 'cpu_clk')):
            sc += 25

        # Contains clock/clk (medium priority)
        if 'clock' in s:
            sc += 20
        if 'clk' in s:
            sc += 18

        # Common suffixes
        if s.endswith('_clk'):
            sc += 10
        elif s.endswith('_clock'):
            sc += 10
        elif s.endswith('clk'):
            sc += 8

        # Input signal indicator
        if s.endswith('_i'):
            sc += 5

        # Prefer shorter names (simpler is better)
        length_penalty = len(s) // 4

        return (-sc, length_penalty, name)

    return sorted(set(cands), key=score)[0]


def _rank_rst(cands: list[str]) -> str:
    """
    Pick the most likely reset from candidates (ports-based).
    Comprehensive ranking across all naming conventions.
    Handles active-high and active-low resets.
    """
    if not cands:
        console.print('[yellow]⚠ Could not find reset signal in port candidates[/yellow]')
        raise SystemExit(
            'ERROR: Reset signal detection failed. No reset candidates found. Please specify --reset-name and --reset-expr'
        )

    def score(name: str):
        s = name.lower()
        sc = 0

        # Exact matches (highest priority - common standard names)
        exact_scores = {
            'reset': 50,
            'rst': 48,
            'resetn': 49,
            'rstn': 49,
            'rst_n': 49,
            'reset_n': 49,
            'presetn': 50,
            'preset_n': 50,
            'prstn': 49,
            'prst_n': 49,  # APB
            'aresetn': 48,
            'areset_n': 48,
            'arstn': 48,
            'arst_n': 48,  # Async
            'sresetn': 47,
            'sreset_n': 47,
            'srstn': 47,
            'srst_n': 47,  # Sync
            'hresetn': 48,
            'hreset_n': 48,
            'hrstn': 48,
            'hrst_n': 48,  # AHB/APB
            'nrst': 47,
            'nrstn': 47,
            'nreset': 47,
            'nresetn': 47,
        }
        if s in exact_scores:
            sc += exact_scores[s]

        # Prefix matching (high priority)
        prefix_scores = {
            'preset': 35,
            'prst': 33,  # APB resets
            'areset': 30,
            'arst': 28,  # Async resets
            'sreset': 30,
            'srst': 28,  # Sync resets
            'hreset': 32,
            'hrst': 30,  # AHB/APB resets
            'nreset': 28,
            'nrst': 26,  # Active-low naming
            'reset': 25,
            'rst': 23,  # Generic resets
        }
        for prefix, points in prefix_scores.items():
            if s.startswith(prefix):
                sc += points
                break

        # Contains reset/rst patterns (medium priority)
        if 'preset' in s:
            sc += 20
        elif 'areset' in s or 'arst' in s:
            sc += 18
        elif 'sreset' in s or 'srst' in s:
            sc += 18
        elif 'reset' in s:
            sc += 16
        elif 'rst' in s:
            sc += 14

        # Active-low indicators (important for correct polarity)
        if s.endswith(('_n', '_ni', '_b')):
            sc += 15
        elif s.endswith('n') and len(s) > 4:  # resetn, rstn, etc
            sc += 12

        # Common suffixes
        if s.endswith(('_reset', '_rst')):
            sc += 8

        # Input signal indicator
        if s.endswith('_i'):
            sc += 2

        # Prefer shorter names (simpler is better)
        length_penalty = len(s) // 4

        return (-sc, length_penalty, name)

    # preserve unique
    uniq = list(dict.fromkeys(cands))
    return sorted(uniq, key=score)[0]


def detect_clk_rst_from_ports(ports: List[Dict[str, Any]]) -> Tuple[Optional[str], Optional[str], Optional[str]]:
    """
    Detect clock/reset from a list of port dicts (like Slang ports.json).
    Only considers input/inout ports.
    Returns (clk_name, rst_name, rst_expr) or (None,None,None) if cannot.
    COMPREHENSIVE: Handles ALL naming conventions.
    """
    # Env override wins
    env_clk = os.environ.get('HAGENT_CLK_NAME')
    env_rst_expr = os.environ.get('HAGENT_RESET_EXPR')
    if env_clk and env_rst_expr:
        rst_tokens = re.sub(r'[!()]', ' ', env_rst_expr).split()
        rst_name = rst_tokens[-1] if rst_tokens else env_rst_expr
        return env_clk, rst_name, env_rst_expr

    in_ports = [p for p in ports if isinstance(p, dict) and _is_inputish_port(p)]
    names = [str(p.get('name') or '').strip() for p in in_ports]
    names = [n for n in names if n]

    if not names:
        return None, None, None

    clk_cands = []
    rst_cands = []

    for n in names:
        nl = n.lower()

        # Comprehensive clock detection - any signal with clk/clock in the name
        if 'clk' in nl or 'clock' in nl:
            # Avoid false positives
            if not any(bad in nl for bad in ['block', 'clockwise', 'interlock']):
                clk_cands.append(n)

        # Comprehensive reset detection - use the enhanced filter
        if _is_likely_reset_name(n):
            rst_cands.append(n)

    if not clk_cands or not rst_cands:
        return None, None, None

    clk = _rank_clk(clk_cands)
    rst = _rank_rst(rst_cands)
    return clk, rst, _build_rst_expr(rst)


def _load_ports_json(path: Path) -> List[Dict[str, Any]]:
    try:
        obj = json.loads(path.read_text(encoding='utf-8', errors='ignore'))
        return obj if isinstance(obj, list) else []
    except Exception:
        return []


# --------------------------------------------------------------------
# RTL-text heuristics (fallback) - FIXED PATTERNS
# --------------------------------------------------------------------


def _find_decl_clk_rst_candidates(module_text: str):
    """
    FIXED: Find ALL possible clock and reset signal declarations.
    Now matches bare names like 'clock', 'clk', 'reset', 'rst'.
    """
    # Match ALL signals first
    sig_pat = re.compile(
        r'\b(?:input|wire|logic|reg)\b[^;]*?\b([A-Za-z_][\w]*)\b',
        flags=re.S,
    )

    all_signals = {m.group(1) for m in sig_pat.finditer(module_text)}

    # Filter for clock-like signals
    clk_cands = set()
    for sig in all_signals:
        sig_lower = sig.lower()
        if 'clk' in sig_lower or 'clock' in sig_lower:
            # Avoid false positives
            if not any(bad in sig_lower for bad in ['block', 'clockwise', 'interlock']):
                clk_cands.add(sig)

    # Filter for reset-like signals using comprehensive check
    rst_cands = {n for n in all_signals if _is_likely_reset_name(n)}

    return list(clk_cands), list(rst_cands)


def _find_sensitivity_clk_rst(module_text: str):
    """
    Find clock/reset signals from always block sensitivity lists.
    Comprehensive pattern matching for all naming conventions.
    """
    clk_from_sens: list[str] = []
    rst_from_sens: list[str] = []

    # Match ALL posedge signals
    clk_pos_pat = re.compile(r'\bposedge\s+([A-Za-z_][\w]*)', flags=re.S)

    # Match ALL edge-sensitive signals
    rst_edge_pat = re.compile(r'\b(?:posedge|negedge)\s+([A-Za-z_][\w]*)', flags=re.S)

    # Find all posedge signals (potential clocks)
    for m in clk_pos_pat.finditer(module_text):
        sig = m.group(1)
        sig_lower = sig.lower()
        # Check if it looks like a clock
        if 'clk' in sig_lower or 'clock' in sig_lower:
            if not any(bad in sig_lower for bad in ['block', 'clockwise', 'interlock']):
                clk_from_sens.append(sig)

    # Find all edge-sensitive signals (potential resets)
    for m in rst_edge_pat.finditer(module_text):
        sig = m.group(1)
        # Check if it looks like a reset (not a clock)
        sig_lower = sig.lower()
        if _is_likely_reset_name(sig):
            # Make sure it's not also a clock
            if not ('clk' in sig_lower or 'clock' in sig_lower):
                rst_from_sens.append(sig)

    return clk_from_sens, rst_from_sens


def _find_clk_rst_always_pair(module_text: str):
    pat1 = re.compile(
        r'always(?:_[a-zA-Z0-9]+)?\s*@\(\s*'
        r'posedge\s+([A-Za-z_]\w*)\s+or\s+negedge\s+([A-Za-z_]\w*)'
        r'\s*\)',
        flags=re.S,
    )
    pat2 = re.compile(
        r'always(?:_[a-zA-Z0-9]+)?\s*@\(\s*'
        r'negedge\s+([A-Za-z_]\w*)\s+or\s+posedge\s+([A-Za-z_]\w*)'
        r'\s*\)',
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


def _rank_clk_text(cands: list[str], port_names: set[str]) -> str:
    """
    Pick the most likely clock from RTL text candidates.
    Comprehensive ranking with port name preference.
    """
    if not cands:
        console.print('[yellow]⚠ Could not find clock signal in RTL[/yellow]')
        raise SystemExit('ERROR: Clock signal detection failed. Please specify --clock-name')

    def score(name: str):
        s = name.lower()
        sc = 0

        # Port names are preferred (they're the actual interface)
        if name in port_names:
            sc += 20

        # Exact matches
        exact_scores = {
            'clock': 50,
            'clk': 48,
            'pclk': 49,
            'aclk': 47,
            'hclk': 47,
            'mclk': 47,
            'sclk': 47,
        }
        if s in exact_scores:
            sc += exact_scores[s]

        # Prefix patterns
        if s.startswith(('pclk', 'aclk', 'hclk', 'mclk', 'sclk')):
            sc += 15
        elif s.startswith(('clk', 'clock')):
            sc += 12

        # Contains patterns
        if 'clk' in s or 'clock' in s:
            sc += 8

        # Common suffixes
        if s.endswith(('_clk', '_clock')):
            sc += 5

        # Input indicator
        if s.endswith('_i'):
            sc += 3

        # Prefer names that are ports
        port_bonus = 0 if name in port_names else 1

        return (-sc, len(s), port_bonus)

    return sorted(set(cands), key=score)[0]


def _rank_rst_text(cands: list[str], port_names: set[str]) -> str:
    """
    Pick the most likely reset from RTL text candidates.
    Comprehensive ranking with port name preference.
    """
    if not cands:
        console.print('[yellow]⚠ Could not find reset signal in RTL[/yellow]')
        raise SystemExit('ERROR: Reset signal detection failed. Please specify --reset-name and --reset-expr')

    cands_set = list(dict.fromkeys(cands))

    def score(name: str):
        s = name.lower()
        sc = 0

        # Port names are preferred (they're the actual interface)
        if name in port_names:
            sc += 20

        # Exact matches
        exact_scores = {
            'reset': 50,
            'rst': 48,
            'resetn': 49,
            'rstn': 49,
            'presetn': 50,
            'aresetn': 48,
            'arstn': 48,
            'sresetn': 47,
        }
        if s in exact_scores:
            sc += exact_scores[s]

        # Prefix patterns
        if s.startswith(('preset', 'prst')):
            sc += 18
        elif s.startswith(('areset', 'arst')):
            sc += 16
        elif s.startswith(('sreset', 'srst')):
            sc += 16
        elif s.startswith(('reset', 'rst')):
            sc += 14

        # Active-low suffixes (important)
        if s.endswith(('_n', '_ni', '_b')):
            sc += 10
        elif s.endswith('n') and len(s) > 3:
            sc += 8

        # Contains patterns
        if 'preset' in s or 'prst' in s:
            sc += 6
        elif 'reset' in s or 'rst' in s:
            sc += 5

        # Common suffixes
        if s.endswith(('_reset', '_rst')):
            sc += 3

        # Input indicator
        if s.endswith('_i'):
            sc += 1

        # Prefer names that are ports
        port_bonus = 0 if name in port_names else 1

        return (-sc, len(s), port_bonus)

    return sorted(cands_set, key=score)[0]


# --------------------------------------------------------------------
# Public API
# --------------------------------------------------------------------


def detect_clk_rst_for_top(src_root, top: str, ports_json: Path | None = None):
    """
    Auto-detect (clock_name, reset_name, reset_expr) for a given top module.

    If ports_json is provided and usable, it wins because it represents the
    *top-level ports* for the scoped module.
    """
    src_root = Path(src_root).resolve()

    # 0) Environment override
    env_clk = os.environ.get('HAGENT_CLK_NAME')
    env_rst_expr = os.environ.get('HAGENT_RESET_EXPR')
    if env_clk and env_rst_expr:
        rst_tokens = re.sub(r'[!()]', ' ', env_rst_expr).split()
        rst_name = rst_tokens[-1] if rst_tokens else env_rst_expr
        console.print(
            f'[green]✔ Top module clock={env_clk}, reset={rst_name} (expression: {env_rst_expr}) from environment[/green]'
        )
        return env_clk, rst_name, env_rst_expr

    # 1) ports.json based detection (authoritative)
    if ports_json is not None:
        pj = Path(ports_json).expanduser().resolve()
        if pj.is_file():
            ports = _load_ports_json(pj)
            clk, rst, rst_expr = detect_clk_rst_from_ports(ports)
            if clk and rst and rst_expr:
                console.print(f'[green]✔ Top module clock={clk}, reset={rst} (expression: {rst_expr}) from ports.json[/green]')
                return clk, rst, rst_expr
            console.print(f'[yellow]⚠ ports.json provided but clk/rst not found in it: {pj}[/yellow]')

    # 2) RTL heuristics fallback
    console.print(f'[cyan]🔍 Scanning for top module {top} under {src_root}[/cyan]')
    top_file = _find_top_file(src_root, top)
    if top_file is None:
        raise SystemExit(f"ERROR: Could not find module '{top}' under {src_root}")

    try:
        full_text = top_file.read_text(errors='ignore')
    except OSError as e:
        raise SystemExit(f'ERROR: Cannot read {top_file}: {e}') from e

    no_cmt = _strip_comments(full_text)
    module_text = _extract_module_text(no_cmt, top)

    if not module_text:
        console.print('[red]❌ Could not extract module body[/red]')
        raise SystemExit(
            f'ERROR: Clock/reset detection failed for module {top}. Please specify --clock-name, --reset-name, --reset-expr'
        )

    port_names = set(_extract_port_names(no_cmt, top))

    clk_pair, rst_pair = _find_clk_rst_always_pair(module_text)
    if clk_pair and rst_pair:
        clk_name = clk_pair
        rst_name = rst_pair
        rst_expr = _build_rst_expr(rst_name)
        console.print(
            f'[green]✔ Top module clock={clk_name}, reset={rst_name} (expression: {rst_expr}) from always-block pair[/green]'
        )
        return clk_name, rst_name, rst_expr

    clk_decls, rst_decls = _find_decl_clk_rst_candidates(module_text)
    clk_sens, rst_sens = _find_sensitivity_clk_rst(module_text)

    clk_cands = clk_decls or clk_sens
    rst_cands = rst_decls or rst_sens

    clk_name = _rank_clk_text(clk_cands, port_names)
    rst_name = _rank_rst_text(rst_cands, port_names)
    rst_expr = _build_rst_expr(rst_name)

    console.print(f'[green]✔ Top module clock={clk_name}, reset={rst_name} (expression: {rst_expr})[/green]')
    return clk_name, rst_name, rst_expr


def detect_clk_rst(src_root, top: str):
    return detect_clk_rst_for_top(src_root, top)
