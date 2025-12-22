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

NO NEW CLI ARGS.
- No --props-csv input required.
- SpecBuilder generates <sva_top>_props.csv internally (and still writes <sva_top>_spec.csv).
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

from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

console = Console()


def banner():
    console.print(
        "\n[bold cyan]───────────────────────────────────────────────[/bold cyan]\n"
        "[bold yellow]        🚀 FORMAL AGENT 2025 🚀[/bold yellow]\n"
        "[bold cyan]───────────────────────────────────────────────[/bold cyan]\n"
        "[bold white]Automated Formal Verification Pipeline[/bold white]\n"
        "[bold cyan]───────────────────────────────────────────────[/bold cyan]\n"
    )


def ensure_dir(p: Path):
    p.mkdir(parents=True, exist_ok=True)


def repo_root() -> Path:
    return Path(__file__).resolve().parents[2]  # hagent/tool/cli_formal.py → repo-ish


def _load_private_cov_summarizer():
    root = repo_root()
    priv_script = root / "hagent-private" / "JG" / "summarize_formal_coverage.py"
    if not priv_script.exists():
        return None
    try:
        spec = importlib.util.spec_from_file_location("hagent_private_summarize_formal_coverage", priv_script)
        if spec is None or spec.loader is None:
            console.print("[yellow]⚠ Could not create spec for private coverage summarizer.[/yellow]")
            return None
        module = importlib.util.module_from_spec(spec)
        spec.loader.exec_module(module)
        summarize_fn = getattr(module, "summarize_coverage_html", None)
        if summarize_fn is None:
            console.print("[yellow]⚠ Private coverage summarizer has no 'summarize_coverage_html' function.[/yellow]")
        return summarize_fn
    except Exception as e:
        console.print(f"[yellow]⚠ Could not import private coverage summarizer:[/yellow] {e}")
        return None


PRIVATE_COV_SUMMARIZER = _load_private_cov_summarizer()


def run_uv(cmd: List[str], cwd: Path | None = None):
    if cmd and cmd[0] in ("python", "python3"):
        cmd = cmd[1:]
    cmd_str = " ".join(cmd)
    console.print(f"[cyan]→[/cyan] [white]{sys.executable} {cmd_str}[/white]")
    subprocess.run([sys.executable, *cmd], check=True, cwd=cwd)


def parse_jg_log_detailed(log_path: Path) -> Dict:
    if not log_path.exists():
        console.print(f"[yellow]⚠ Jasper log not found:[/yellow] {log_path}")
        return {}

    text = log_path.read_text(errors="ignore")
    from collections import Counter

    line_re = re.compile(r"\[(\d+)\]\s+(.+?)\s{2,}(\w+)\s", re.M)
    rows = []
    for m in line_re.finditer(text):
        rows.append((int(m.group(1)), m.group(2).rstrip(), m.group(3).lower()))

    result_dict: Dict[str, Any] = {
        "properties_considered": 0,
        "assertions_total": 0,
        "covers_total": 0,
        "assertions": {},
        "covers": {},
    }

    if rows:
        a_counts: Counter[str] = Counter()
        c_counts: Counter[str] = Counter()

        for _idx, full_name, res in rows:
            if (":witness" in full_name) or (":precondition" in full_name) or (".cover_" in full_name) or full_name.startswith("cover_"):
                section = "covers"
            elif (".assert_" in full_name) or full_name.startswith("assert_") or (".assume_" in full_name) or full_name.startswith("assume_"):
                section = "assertions"
            else:
                section = "assertions"

            if res in ("proven", "valid"):
                key = "proven"
            elif res in ("cex", "falsified", "fail"):
                key = "cex"
            elif res in ("covered",):
                key = "covered"
            elif res in ("unreachable",):
                key = "unreachable"
            elif res in ("unknown", "inconclusive", "undetermined"):
                key = "unknown"
            else:
                key = res

            if section == "assertions":
                a_counts[key] += 1
            else:
                c_counts[key] += 1

        result_dict["properties_considered"] = len(rows)
        result_dict["assertions_total"] = sum(a_counts.values())
        result_dict["covers_total"] = sum(c_counts.values())
        result_dict["assertions"] = dict(a_counts)
        result_dict["covers"] = dict(c_counts)
        return result_dict

    return {}


def print_jg_summary(summary: Dict):
    if not summary:
        return
    console.print("\n[bold green]" + "=" * 61 + "[/bold green]")
    console.print("[bold yellow]SUMMARY[/bold yellow]")
    console.print("[bold green]" + "=" * 61 + "[/bold green]")
    console.print(f"Properties Considered : {summary.get('properties_considered', 0)}")
    console.print(f"  Assertions          : {summary.get('assertions_total', 0)}")
    for k, v in summary.get("assertions", {}).items():
        console.print(f"    - {k:<30}: {v}")
    console.print(f"  Covers              : {summary.get('covers_total', 0)}")
    for k, v in summary.get("covers", {}).items():
        console.print(f"    - {k:<30}: {v}")
    console.print("[green]determined[/green]")


def write_summary(out_dir: Path, counts: Dict[str, int]):
    csv_path = out_dir / "results_summary.csv"
    with csv_path.open("w") as f:
        f.write("status,count\n")
        for k, v in counts.items():
            f.write(f"{k},{v}\n")

    table = Table(title="Formal Results Summary", style="bold cyan")
    table.add_column("Status", justify="left", style="white")
    table.add_column("Count", justify="center", style="bold")
    for k, v in counts.items():
        col = "green" if k == "PROVEN" else "red" if k == "FAIL" else "yellow"
        table.add_row(k, f"[{col}]{v}[/{col}]")
    console.print(table)


def main():
    import argparse

    ap = argparse.ArgumentParser(description="Formal Agent - FPV Pipeline")
    ap.add_argument("--slang", required=True, help="Path to slang binary or wrapper.")
    ap.add_argument("--rtl", required=True, help="RTL source directory.")
    ap.add_argument("--top", required=True, help="Design top module name (e.g. cva6).")
    ap.add_argument("--sva-top", help="Module to generate spec/properties/SVA for. Defaults to --top.")
    ap.add_argument("--out", required=True, help="Output directory for results.")
    ap.add_argument("-I", "--include", nargs="*", default=[], help="Include directories.")
    ap.add_argument("-D", "--defines", nargs="*", default=[], help="Verilog defines.")
    ap.add_argument("--filelist", help="Optional HDL filelist for design compilation (manifest/command file).")
    ap.add_argument("--jasper-bin", default="<cadence jasper_bin path>", help="Path to Jasper binary.")
    ap.add_argument("--run-jg", action="store_true", help="Run JasperGold FPV automatically.")
    args = ap.parse_args()

    banner()

    rtl_dir = Path(os.path.expanduser(args.rtl)).resolve()
    if not rtl_dir.is_dir():
        raise SystemExit(f"[❌] RTL directory not found: {rtl_dir}")

    out_base = Path(os.path.expanduser(args.out)).resolve()
    fpv_dir = out_base / f"fpv_{args.top}"
    ensure_dir(fpv_dir)
    ensure_dir(fpv_dir / "sva")

    sva_top = args.sva_top or args.top

    # YAML config detection
    root = repo_root()
    spec_yaml = root / "hagent" / "step" / "sva_gen" / "spec_prompt.yaml"
    prop_yaml = root / "hagent" / "step" / "sva_gen" / "property_prompt.yaml"
    if not spec_yaml.exists() or not prop_yaml.exists():
        raise SystemExit(f"[❌] Missing YAML configs: {spec_yaml}, {prop_yaml}")

    # Detect clock/reset for design top
    cr_result = detect_clk_rst_for_top(rtl_dir, args.top)
    if len(cr_result) == 3:
        clk, rst, rst_expr = cr_result
    elif len(cr_result) == 4:
        clk, rst, rst_expr, _active_low = cr_result
    else:
        raise ValueError(f"Unexpected return from detect_clk_rst_for_top: {cr_result}")

    console.print(f"[cyan]ℹ Design top:[/cyan] {args.top}   [cyan]ℹ SVA target:[/cyan] {sva_top}")

    steps = [
        (
            f"🔧 Generating formal scenarios (spec) for module {sva_top}",
            [
                "python3",
                "-m",
                "hagent.tool.tests.cli_spec_builder",
                "--mode",
                "single",
                "--slang",
                args.slang,
                "--rtl",
                str(rtl_dir),
                "--top",
                sva_top,
                "--design-top",
                args.top,  # important: compile design top if filelist provided
                "--out",
                str(fpv_dir),
                "--llm-conf",
                str(spec_yaml),
            ],
        ),
        (
            f"🔒 Generating formal properties (assert/assume/cover) for module {sva_top}",
            [
                "python3",
                "-m",
                "hagent.tool.tests.cli_property_builder",
                "--spec-md",
                str(fpv_dir / f"{sva_top}_spec.md"),
                "--csv",
                str(fpv_dir / f"{sva_top}_spec.csv"),
                "--rtl",
                str(rtl_dir),
                "--out",
                str(fpv_dir),
                "--llm-conf",
                str(prop_yaml),
            ],
        ),
        (
            "🧩 Generating TCL/SVA utility files",
            [
                "python3",
                "-m",
                "hagent.tool.gen_dep_tcl_and_sva",
                "--src",
                str(rtl_dir),
                "--top",
                args.top,
                "--out",
                str(fpv_dir / "FPV.tcl"),
                "--prop-include",
                str(fpv_dir / "sva" / "properties.sv"),
                "--clock-name",
                clk,
                "--reset-expr",
                rst_expr,
                "--prove-time",
                "6h",
                "--proofgrid-jobs",
                "64",
            ],
        ),
    ]

    # pass include/defines/filelist into spec step and gen_dep step
    msg0, cmd0 = steps[0]
    cmd0 = list(cmd0)
    if args.filelist:
        cmd0 += ["--filelist", os.path.expanduser(args.filelist)]
    for inc in args.include:
        cmd0 += ["--include", os.path.expanduser(inc)]
    for d in args.defines:
        cmd0 += ["--defines", d]
    steps[0] = (msg0, cmd0)

    msg2, cmd2 = steps[2]
    cmd2 = list(cmd2)
    if sva_top != args.top:
        cmd2 += ["--sva-top", sva_top]
    for inc in args.include:
        cmd2 += ["--extra-inc", os.path.expanduser(inc)]
    for d in args.defines:
        cmd2 += ["--defines", d]
    if args.filelist:
        cmd2 += ["--filelist", os.path.expanduser(args.filelist)]
    steps[2] = (msg2, cmd2)

    # run pipeline
    with Progress(SpinnerColumn(), TextColumn("[progress.description]{task.description}")) as progress:
        for idx, (msg, cmd) in enumerate(steps, 1):
            progress.add_task(description=f"[cyan]{msg}...", total=None)
            console.print(f"\n[bold cyan][{idx}/{len(steps)}][/bold cyan] {msg}")
            run_uv(cmd, cwd=Path.cwd())
            console.print(f"[green]✔[/green] {msg} completed.\n")

    # move generated property file
    prop_src = fpv_dir / "properties.sv"
    if not prop_src.exists():
        raise SystemExit("[❌] properties.sv not found after property builder.")
    shutil.move(str(prop_src), str(fpv_dir / "sva" / "properties.sv"))
    console.print("[green]✔[/green] Moved properties.sv → sva/")

    # Optional JasperGold run
    if args.run_jg:
        console.print(
            f"\n[bold yellow]⚙ Running Formal Tool: JasperGold FPV (top={args.top}, sva_top={sva_top})...[/bold yellow]"
        )

        jg_cmd_list = [args.jasper_bin, "-allow_unsupported_OS", "-tcl", "FPV.tcl", "-batch"]
        console.print(f"[cyan]→[/cyan] [white]{' '.join(jg_cmd_list)}[/white]")

        # Log files (recommended)
        jg_stdout = fpv_dir / "jg.stdout.log"
        jg_stderr = fpv_dir / "jg.stderr.log"

        try:
            console.print(f"[cyan]→[/cyan] [white]stdout:[/white] {jg_stdout}")
            console.print(f"[cyan]→[/cyan] [white]stderr:[/white] {jg_stderr}")

            with open(jg_stdout, "w") as fo, open(jg_stderr, "w") as fe:
                subprocess.run(
                    jg_cmd_list,
                    cwd=fpv_dir,
                    stdout=fo,
                    stderr=fe,
                    check=True
                )

        except subprocess.CalledProcessError as e:
            console.print(f"[red]⚠ Jasper exited with code {e.returncode}[/red]")
            # If you want to stop on failure, uncomment:
            # raise

        # ---- Everything below is unchanged from your script ----
        jg_log = fpv_dir / "jgproject" / "jg.log"
        jg_summary = parse_jg_log_detailed(jg_log)
        print_jg_summary(jg_summary)

        counts = {
            "PROVEN": jg_summary.get("assertions", {}).get("proven", 0),
            "FAIL": jg_summary.get("assertions", {}).get("cex", 0),
            "UNREACHABLE": jg_summary.get("covers", {}).get("unreachable", 0),
            "COVER": jg_summary.get("covers", {}).get("covered", 0),
            "UNKNOWN": (
                jg_summary.get("assertions", {}).get("unknown", 0)
                + jg_summary.get("covers", {}).get("unknown", 0)
            ),
        }
        write_summary(fpv_dir, counts)

        cov_html = fpv_dir / "formal_coverage.html"
        if PRIVATE_COV_SUMMARIZER is not None:
            if cov_html.exists():
                try:
                    out_cov_txt = PRIVATE_COV_SUMMARIZER(cov_html, console=console)
                    console.print(f"[green]✔ Formal coverage summary written to[/green] {out_cov_txt}")
                except Exception as e:
                    console.print(f"[yellow]⚠ Private coverage summary failed:[/yellow] {e}")
            else:
                console.print(f"[yellow]⚠ formal_coverage.html not found in[/yellow] {fpv_dir}")


    console.print("\n[bold green]✅ FORMAL AGENT COMPLETED SUCCESSFULLY![/bold green]")
    console.print(
        f"Design top: [bold cyan]{args.top}[/bold cyan]   "
        f"SVA target: [bold magenta]{sva_top}[/bold magenta]\n"
        f"All results in: [bold yellow]{fpv_dir}[/bold yellow]\n"
    )


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        console.print(f"[red]❌ Fatal Error:[/red] {e}")
        sys.exit(1)
    sys.exit(0)
