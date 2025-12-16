#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Formal Agent
Author: Divya Kohli (2025)

Automated Formal Verification Pipeline:
  1. Spec Builder CLI
  2. Property Builder CLI
  3. gen_dep_tcl_and_sva
  4. Optional JasperGold FPV run
  5. Result summary (table + CSV)
  6. Optional LLM-based CEX failure root-cause analysis

Design vs. SVA target:
  --top     : design / elaboration top (e.g. cva6)
  --sva-top : module for which spec/properties/SVA wrappers are generated
              (defaults to --top, can be submodule like load_unit)

Filelist:
  --filelist : optional plain text file with one HDL path per line.
               If given, gen_dep_tcl_and_sva uses it instead of auto
               dependency discovery.
"""

import os
import re
import sys
import shutil
import subprocess
import importlib.util
from pathlib import Path
from typing import Dict, List, Any, Optional

from rich.console import Console
from rich.table import Table
from rich.progress import Progress, SpinnerColumn, TextColumn

# --- Clock/reset detector utility ---
from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

console = Console()

# -----------------------------------------------------------------------------
# Helper utilities
# -----------------------------------------------------------------------------


def banner():
    console.print(
        '\n[bold cyan]───────────────────────────────────────────────[/bold cyan]\n'
        '[bold yellow]        🚀 FORMAL AGENT 2025 🚀[/bold yellow]\n'
        '[bold cyan]───────────────────────────────────────────────[/bold cyan]\n'
        '[bold white]Automated Formal Verification Pipeline[/bold white]\n'
        '[bold cyan]───────────────────────────────────────────────[/bold cyan]\n'
    )


def ensure_dir(p: Path):
    p.mkdir(parents=True, exist_ok=True)


def repo_root() -> Path:
    # Return repo root that contains "hagent/"
    return Path(__file__).resolve().parents[3]


# Try to load private JasperGold coverage summarizer from
#   hagent-private/JG/summarize_formal_coverage.py
def _load_private_cov_summarizer():
    root = repo_root()
    priv_script = root / 'hagent-private' / 'JG' / 'summarize_formal_coverage.py'
    if not priv_script.exists():
        # Silent: it's okay if private repo isn't present
        return None
    try:
        spec = importlib.util.spec_from_file_location('hagent_private_summarize_formal_coverage', priv_script)
        if spec is None or spec.loader is None:
            console.print('[yellow]⚠ Could not create spec for private coverage summarizer.[/yellow]')
            return None
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        summarize_fn = getattr(module, 'summarize_coverage_html', None)
        if summarize_fn is None:
            console.print("[yellow]⚠ Private coverage summarizer has no 'summarize_coverage_html' function.[/yellow]")
        return summarize_fn
    except Exception as e:
        console.print(f'[yellow]⚠ Could not import private coverage summarizer:[/yellow] {e}')
        return None


PRIVATE_COV_SUMMARIZER = _load_private_cov_summarizer()


def run_uv(cmd: List[str], cwd: Path | None = None):
    """Run a Python module or script with the *current* Python interpreter.

    Important:
    - cli_formal.py itself is often launched via `uv run --python <version> ...`
    - Nested `uv run` causes interpreter mismatches (cp314 vs cp313).
    - Here we reuse `sys.executable` and strip any leading 'python'/'python3'
      from the command list.
    """
    # If the first arg is 'python' or 'python3', drop it; we'll use sys.executable.
    if cmd and cmd[0] in ('python', 'python3'):
        cmd = cmd[1:]

    cmd_str = ' '.join(cmd)
    console.print(f'[cyan]→[/cyan] [white]{sys.executable} {cmd_str}[/white]')
    subprocess.run([sys.executable, *cmd], check=True, cwd=cwd)


# -----------------------------------------------------------------------------
# JasperGold log parsing utilities
# -----------------------------------------------------------------------------


def parse_jg_log_detailed(log_path: Path) -> Dict:
    """
    Parse JasperGold RESULTS / SUMMARY into a structured dict.

    Priority:
      1) RESULTS table (per-property lines) anywhere in the file
      2) SUMMARY block (if no RESULTS lines found)

    Returns a dict:
        {
          "properties_considered": int,
          "assertions_total": int,
          "covers_total": int,
          "assertions": { result_key: count, ... },
          "covers": { result_key: count, ... },
        }
    where result_key is things like: "proven", "cex", "covered", "unreachable", "unknown", ...
    """
    if not log_path.exists():
        console.print(f'[yellow]⚠ Jasper log not found:[/yellow] {log_path}')
        return {}

    text = log_path.read_text(errors='ignore')

    from collections import Counter

    # ------------------------------------------------------------------
    # 1) Try parsing from RESULTS table lines
    #    Example lines:
    #    [1]   Sync_FIFO.i_Sync_FIFO_prop.assert_reset_behavior        proven      PRE   Infinite  0.000 s
    #    [2]   Sync_FIFO.i_Sync_FIFO_prop.assert_reset_behavior:witness1 unreachable PRE Infinite 0.000 s
    # ------------------------------------------------------------------
    line_re = re.compile(r'\[(\d+)\]\s+(.+?)\s{2,}(\w+)\s', re.M)

    rows = []
    for m in line_re.finditer(text):
        idx = int(m.group(1))
        name = m.group(2).rstrip()
        result = m.group(3).lower()
        rows.append((idx, name, result))

    result_dict: Dict[str, Any] = {
        'properties_considered': 0,
        'assertions_total': 0,
        'covers_total': 0,
        'assertions': {},
        'covers': {},
    }

    if rows:
        a_counts: Counter[str] = Counter()
        c_counts: Counter[str] = Counter()

        for idx, full_name, res in rows:
            # Heuristic classification:
            #  - core assertions/assumptions: "assert_*" / "assume_*" without :witness/:precondition
            #  - covers + witnesses + preconditions: everything else
            if (
                ':witness' in full_name
                or ':precondition' in full_name
                or '.cover_' in full_name
                or full_name.startswith('cover_')
            ):
                section = 'covers'
            elif (
                '.assert_' in full_name
                or full_name.startswith('assert_')
                or '.assume_' in full_name
                or full_name.startswith('assume_')
            ):
                section = 'assertions'
            else:
                # default any unknown property naming to "assertions"
                section = 'assertions'

            # Normalize Jasper result strings
            if res in ('proven', 'valid'):
                key = 'proven'
            elif res in ('cex', 'falsified', 'fail'):
                key = 'cex'
            elif res in ('covered',):
                key = 'covered'
            elif res in ('unreachable',):
                key = 'unreachable'
            elif res in ('unknown', 'inconclusive', 'undetermined'):
                key = 'unknown'
            else:
                key = res  # keep raw text for anything exotic

            if section == 'assertions':
                a_counts[key] += 1
            else:
                c_counts[key] += 1

        result_dict['properties_considered'] = len(rows)
        result_dict['assertions_total'] = sum(a_counts.values())
        result_dict['covers_total'] = sum(c_counts.values())
        result_dict['assertions'] = dict(a_counts)
        result_dict['covers'] = dict(c_counts)
        return result_dict

    # ------------------------------------------------------------------
    # 2) Fallback: parse SUMMARY block if no RESULTS lines were found
    # ------------------------------------------------------------------
    def _parse_from_summary_block(text: str) -> Optional[Dict[str, Any]]:
        last_block = None
        # capture the LAST SUMMARY ... determined block in the log
        for m in re.finditer(r'SUMMARY\s*\n(.*?)(?:\n\s*determined\b|\Z)', text, re.S | re.M):
            last_block = m.group(1)

        if last_block is None:
            return None

        lines = [ln.strip() for ln in last_block.splitlines() if ln.strip()]
        out: Dict[str, Any] = {
            'properties_considered': 0,
            'assertions_total': 0,
            'covers_total': 0,
            'assertions': {},
            'covers': {},
        }
        current_section: Optional[str] = None

        for ln in lines:
            low = ln.lower()
            if low.startswith('properties considered'):
                m = re.search(r':\s*(\d+)', ln)
                if m:
                    out['properties_considered'] = int(m.group(1))
            elif low.startswith('assertions'):
                m = re.search(r':\s*(\d+)', ln)
                if m:
                    out['assertions_total'] = int(m.group(1))
                current_section = 'assertions'
            elif low.startswith('covers'):
                m = re.search(r':\s*(\d+)', ln)
                if m:
                    out['covers_total'] = int(m.group(1))
                current_section = 'covers'
            elif ln.startswith('-'):
                # e.g. "- bounded_unreachable (user): 0 (0%)"
                m2 = re.match(r'-\s*([\w\(\)_]+).*?:\s*(\d+)', ln)
                if m2 and current_section:
                    key = m2.group(1)
                    val = int(m2.group(2))
                    out[current_section][key] = val

        return out

    summary_fallback = _parse_from_summary_block(text)
    if summary_fallback is not None:
        return summary_fallback

    # If nothing matched, return empty dict (caller handles it)
    return {}


def print_jg_summary(summary: Dict):
    """Pretty print Jasper summary."""
    if not summary:
        return
    console.print('\n[bold green]' + '=' * 61 + '[/bold green]')
    console.print('[bold yellow]SUMMARY[/bold yellow]')
    console.print('[bold green]' + '=' * 61 + '[/bold green]')
    console.print(f'Properties Considered : {summary.get("properties_considered", 0)}')
    console.print(f'  Assertions          : {summary.get("assertions_total", 0)}')
    for k, v in summary.get('assertions', {}).items():
        console.print(f'    - {k:<30}: {v}')
    console.print(f'  Covers              : {summary.get("covers_total", 0)}')
    for k, v in summary.get('covers', {}).items():
        console.print(f'    - {k:<30}: {v}')
    console.print('[green]determined[/green]')


def write_summary(out_dir: Path, counts: Dict[str, int]):
    """Write summary to CSV and console table."""
    csv_path = out_dir / 'results_summary.csv'
    with csv_path.open('w') as f:
        f.write('status,count\n')
        for k, v in counts.items():
            f.write(f'{k},{v}\n')

    table = Table(title='Formal Results Summary', style='bold cyan')
    table.add_column('Status', justify='left', style='white')
    table.add_column('Count', justify='center', style='bold')
    for k, v in counts.items():
        col = 'green' if k == 'PROVEN' else 'red' if k == 'FAIL' else 'yellow'
        table.add_row(k, f'[{col}]{v}[/{col}]')
    console.print(table)


# -----------------------------------------------------------------------------
# Main pipeline
# -----------------------------------------------------------------------------


def main():
    import argparse

    ap = argparse.ArgumentParser(description='Formal Agent - FPV Pipeline')
    ap.add_argument('--slang', required=True, help='Path to slang binary or wrapper.')
    ap.add_argument('--rtl', required=True, help='RTL source directory.')
    ap.add_argument('--top', required=True, help='Design top module name (e.g. cva6).')
    ap.add_argument(
        '--sva-top',
        help=('Module to generate spec/properties/SVA for. Defaults to --top (can be submodule, e.g. load_unit).'),
    )
    ap.add_argument('--out', required=True, help='Output directory for results.')
    ap.add_argument('-I', '--include', nargs='*', default=[], help='Include directories.')
    ap.add_argument('-D', '--defines', nargs='*', default=[], help='Verilog defines.')
    ap.add_argument(
        '--filelist',
        help=(
            'Optional plain text HDL filelist (one file per line) for Jasper. If provided, passed through to gen_dep_tcl_and_sva.'
        ),
    )
    ap.add_argument(
        '--jasper-bin',
        default='<cadence jasper_bin path>',
        help='Path to Jasper binary.',
    )
    ap.add_argument('--run-jg', action='store_true', help='Run JasperGold FPV automatically.')
    args = ap.parse_args()

    banner()

    rtl_dir = Path(os.path.expanduser(args.rtl)).resolve()
    if not rtl_dir.is_dir():
        raise SystemExit(f'[❌] RTL directory not found: {rtl_dir}')

    out_base = Path(os.path.expanduser(args.out)).resolve()
    fpv_dir = out_base / f'fpv_{args.top}'
    ensure_dir(fpv_dir)
    ensure_dir(fpv_dir / 'sva')

    # SVA target module (spec/properties/bind). Defaults to design top.
    sva_top = args.sva_top or args.top

    # YAML config detection
    root = repo_root()
    spec_yaml = root / 'hagent' / 'hagent' / 'step' / 'sva_gen' / 'spec_prompt.yaml'
    prop_yaml = root / 'hagent' / 'hagent' / 'step' / 'sva_gen' / 'property_prompt.yaml'
    if not spec_yaml.exists() or not prop_yaml.exists():
        raise SystemExit(f'[❌] Missing YAML configs: {spec_yaml}, {prop_yaml}')

    # --- 🔍 Detect clock/reset for design top module ---
    cr_result = detect_clk_rst_for_top(rtl_dir, args.top)
    if len(cr_result) == 3:
        clk, rst, rst_expr = cr_result
        active_low = rst_expr.startswith('!')
    elif len(cr_result) == 4:
        clk, rst, rst_expr, active_low = cr_result
    else:
        raise ValueError(f'Unexpected return from detect_clk_rst_for_top: {cr_result}')

    console.print(f'[cyan]ℹ Design top:[/cyan] {args.top}   [cyan]ℹ SVA target:[/cyan] {sva_top}')

    # --- Pipeline steps ---
    steps = [
        (
            f'🔧 Generating formal scenarios (spec) for module {sva_top}',
            [
                'python3',
                '-m',
                'hagent.tool.tests.cli_spec_builder',
                '--mode',
                'single',
                '--slang',
                args.slang,
                '--rtl',
                str(rtl_dir),
                '--top',
                sva_top,
                '--out',
                str(fpv_dir),
                '--llm-conf',
                str(spec_yaml),
            ],
        ),
        (
            f'🔒 Generating formal properties (assert/assume/cover) for module {sva_top}',
            [
                'python3',
                '-m',
                'hagent.tool.tests.cli_property_builder',
                '--spec-md',
                str(fpv_dir / f'{sva_top}_spec.md'),
                '--csv',
                str(fpv_dir / f'{sva_top}_spec.csv'),
                '--rtl',
                str(rtl_dir),
                '--out',
                str(fpv_dir),
                '--llm-conf',
                str(prop_yaml),
            ],
        ),
        (
            '🧩 Generating TCL/SVA utility files',
            [
                'python3',
                '-m',
                'hagent.tool.gen_dep_tcl_and_sva',
                '--src',
                str(rtl_dir),
                '--top',
                args.top,
                '--out',
                str(fpv_dir / 'FPV.tcl'),   # ✅ IMPORTANT: include filename
                '--prop-include',
                str(fpv_dir / 'properties.sv'),  # or just 'properties.sv' if you prefer
                '--clock-name',
                clk,
                '--reset-expr',
                rst_expr,
                '--prove-time',
                '6h',
                '--proofgrid-jobs',
                '64',
            ],
        ),
    ]

    # Add SVA target module to gen_dep_tcl_and_sva if different from top
    msg_gen, gen_cmd = steps[2]
    gen_cmd = list(gen_cmd)
    if sva_top != args.top:
        gen_cmd += ['--sva-top', sva_top]

    # Add include, define, and filelist flags
    for inc in args.include:
        gen_cmd += ['--extra-inc', os.path.expanduser(inc)]
    for d in args.defines:
        gen_cmd += ['--defines', d]
    if args.filelist:
        gen_cmd += ['--filelist', os.path.expanduser(args.filelist)]
    steps[2] = (msg_gen, gen_cmd)

    # --- Run pipeline ---
    with Progress(SpinnerColumn(), TextColumn('[progress.description]{task.description}')) as progress:
        for idx, (msg, cmd) in enumerate(steps, 1):
            progress.add_task(description=f'[cyan]{msg}...', total=None)
            console.print(f'\n[bold cyan][{idx}/{len(steps)}][/bold cyan] {msg}')
            run_uv(cmd, cwd=Path.cwd())
            console.print(f'[green]✔[/green] {msg} completed.\n')

    # --- Move generated property file ---
    prop_src = fpv_dir / 'properties.sv'
    if not prop_src.exists():
        raise SystemExit('[❌] properties.sv not found after property builder.')
    shutil.move(str(prop_src), str(fpv_dir / 'sva' / 'properties.sv'))
    console.print('[green]✔[/green] Moved properties.sv → sva/')

    # --- Optional JasperGold run ---
    if args.run_jg:
        console.print(
            f'\n[bold yellow]⚙ Running Formal Tool: JasperGold FPV (top={args.top}, sva_top={sva_top})...[/bold yellow]'
        )
        try:
            console.print(
                f'[cyan]→[/cyan] [white]{args.jasper_bin} -allow_unsupported_OS -tcl FPV.tcl -batch[/white]'
            )
            subprocess.run(
                [
                    args.jasper_bin,
                    '-allow_unsupported_OS',
                    '-tcl',
                    'FPV.tcl',
                    '-batch',
                ],
                cwd=fpv_dir,
                check=True,
            )
        except subprocess.CalledProcessError as e:
            console.print(f'[red]⚠ Jasper exited with code {e.returncode}[/red]')

        jg_log = fpv_dir / 'jgproject' / 'jg.log'
        jg_summary = parse_jg_log_detailed(jg_log)
        print_jg_summary(jg_summary)

        counts = {
            'PROVEN': jg_summary.get('assertions', {}).get('proven', 0),
            'FAIL': jg_summary.get('assertions', {}).get('cex', 0),
            'UNREACHABLE': jg_summary.get('covers', {}).get('unreachable', 0),
            'COVER': jg_summary.get('covers', {}).get('covered', 0),
            'UNKNOWN': (jg_summary.get('assertions', {}).get('unknown', 0) + jg_summary.get('covers', {}).get('unknown', 0)),
        }
        write_summary(fpv_dir, counts)

        # --- Private formal coverage HTML summary (if available) ---
        cov_html = fpv_dir / 'formal_coverage.html'
        if PRIVATE_COV_SUMMARIZER is not None:
            if cov_html.exists():
                try:
                    out_cov_txt = PRIVATE_COV_SUMMARIZER(cov_html, console=console)
                    console.print(f'[green]✔ Formal coverage summary written to[/green] {out_cov_txt}')
                except Exception as e:
                    console.print(f'[yellow]⚠ Private coverage summary failed:[/yellow] {e}')
            else:
                console.print(f'[yellow]⚠ formal_coverage.html not found in[/yellow] {fpv_dir}')
        else:
            console.print(
                '[yellow]ℹ Private coverage summarizer not available '
                '(expected at hagent-private/JG/summarize_formal_coverage.py).[/yellow]'
            )

    console.print('\n[bold green]✅ FORMAL AGENT COMPLETED SUCCESSFULLY![/bold green]')
    console.print(
        f'Design top: [bold cyan]{args.top}[/bold cyan]   '
        f'SVA target: [bold magenta]{sva_top}[/bold magenta]\n'
        f'All results in: [bold yellow]{fpv_dir}[/bold yellow]\n'
    )


# -----------------------------------------------------------------------------
if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        console.print(f'[red]❌ Fatal Error:[/red] {e}')
        sys.exit(1)
    sys.exit(0)
