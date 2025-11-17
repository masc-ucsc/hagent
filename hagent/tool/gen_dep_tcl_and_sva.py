#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Generate:
  1) FPV.tcl using the private Jasper TCL writer in hagent-private.
  2) Minimal SVA wrapper and bind:
       <out_dir>/sva/<top>_prop.sv
       <out_dir>/sva/<top>_bind.sv

The public hagent repo does NOT embed any Jasper TCL logic.
All TCL generation must come from hagent-private.

Expected private writer:
  from hagent_private.JG.fpv_tcl_writer import write_jasper_tcl
"""

import re
import sys
import argparse
from pathlib import Path
from rich.console import Console

# Local utility imports (shared in hagent public repo)
from hagent.tool.utils.hdl_utils import (
    find_sv_files,
    index_modules_packages,
    compute_transitive_closure,
    strip_comments,
)
from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

console = Console()

# -----------------------------------------------------------------------------
#  Regex for module header parsing
# -----------------------------------------------------------------------------
HEADER_RE = re.compile(
    r"module\s+(?P<name>\w+)\s*"
    r"(?P<params>#\s*\((?P<param_body>.*?)\))?\s*"
    r"\(\s*(?P<port_body>.*?)\)\s*;",
    re.DOTALL | re.MULTILINE,
)

# -----------------------------------------------------------------------------
#  Private TCL writer loader (no fallback in public repo)
# -----------------------------------------------------------------------------
def _load_private_tcl_writer():
    """
    Load the JasperGold TCL writer from the private repo.

    There is intentionally NO fallback in the public repo.
    If the private writer is missing, this tool errors out.
    """
    try:
        # This must live ONLY in hagent-private
        from JG.fpv_tcl_writer import write_jasper_tcl
        console.print("[green]✔ Using hagent-private Jasper TCL writer[/green]")
        return write_jasper_tcl
    except Exception as e:
        console.print("[red]✖ ERROR: Private TCL writer not found.[/red]")
        console.print(
            "    Expected: [bold]hagent_private.JG.fpv_tcl_writer.write_jasper_tcl[/bold]"
        )
        console.print(
            "    Make sure 'hagent-private' is on PYTHONPATH before running this tool."
        )
        console.print(f"    Import error: {e}")
        sys.exit(1)

# single global instance
write_jasper_tcl = _load_private_tcl_writer()

# -----------------------------------------------------------------------------
#  Port / declaration helpers
# -----------------------------------------------------------------------------
def clean_decl_to_input(decl: str) -> str:
    """Normalize HDL port declarations into 'input' form."""
    decl = re.sub(r"//.*?$", "", decl, flags=re.M)
    decl = re.sub(r"/\*.*?\*/", "", decl, flags=re.S)
    decl = re.sub(r"\s+", " ", decl).strip().rstrip(",")
    # convert any direction to input
    decl = re.sub(r"\b(output|inout)\b", "input", decl)
    decl = re.sub(r"\binput\b", "input", decl)
    # strip net types
    decl = re.sub(r"\b(wire|reg|logic|var|signed|unsigned)\b", "", decl)
    return re.sub(r"\s+", " ", decl).strip()


def header_port_names(port_body: str):
    """
    Extract port names (in order) from the header port list.

    Works for:
      module m (clk, rst, a, b);
      module m (input clk, input rst, output [7:0] a, b);
    """
    # keep ranges intact but kill newlines
    tmp = re.sub(r"\[(?:[^\[\]])*?\]", lambda m: m.group(0).replace("\n", " "), port_body)

    parts, current, depth = [], "", 0
    for ch in tmp:
        if ch == "[":
            depth += 1
        elif ch == "]":
            depth = max(0, depth - 1)
        if ch == "," and depth == 0:
            if current.strip():
                parts.append(current.strip())
            current = ""
        else:
            current += ch
    if current.strip():
        parts.append(current.strip())

    names = []
    for p in parts:
        p = p.strip().rstrip(",")
        m = re.search(r"([\w$]+)\s*$", p)
        if m:
            names.append(m.group(1))
    return names


def parse_io_decls_from_body(body: str):
    """
    Parse input/output/inout declarations in the module body and build a map:
        base_name -> full declaration string

    Handles patterns like:
        input clk, rst;
        output [7:0] buf_out;
        inout [3:0] bus_a, bus_b;
    """
    body_nc = strip_comments(body)
    io_map = {}

    io_re = re.compile(
        r"\b(input|output|inout)\b\s*"
        r"(?P<packed>\[[^\]]+\]\s*)?"
        r"(?P<names>[^;]+);"
    )

    for m in io_re.finditer(body_nc):
        direction = m.group(1)
        packed = m.group("packed") or ""
        names_str = m.group("names")
        for n in [x.strip() for x in names_str.split(",") if x.strip()]:
            decl = f"{direction} {packed}{n}"
            base = re.sub(r"\[.*?\]", "", n).strip()
            io_map[base] = decl

    return io_map

# -----------------------------------------------------------------------------
#  SVA generation
# -----------------------------------------------------------------------------
def generate_prop_module_min(dut_name, params_text, port_decls, include_file):
    """
    Create a wrapper module:
      module <dut>_prop #(params) ( input ... );
        `include "properties.sv"
      endmodule
    """
    header_params = f" {params_text} " if params_text else ""
    port_lines = ",\n    ".join(clean_decl_to_input(d) for d in port_decls)

    lines = []
    lines.append(f"module {dut_name}_prop{header_params}(\n    {port_lines}\n);\n")
    lines.append("// properties here")
    if include_file:
        lines.append(f'`include "{include_file}"')
    lines.append("\nendmodule\n")
    return "\n".join(lines)


def generate_bind(dut_name, params_text, port_decls):
    """Generate bind file for DUT.

    We need to robustly extract the signal name from declarations like:
        input clk
        input [7:0] buf_in
        input [7:0] buf_mem[`BUF_SIZE -1 : 0]

    The rule: take the identifier that appears right before any trailing
    unpacked array dimensions at the end of the declaration.
    """
    sigs = []

    for decl in port_decls:
        d = decl.strip().rstrip(",")
        if not d:
            continue

        # Strip direction / types so we don't accidentally pick 'input' etc.
        # Then:  match "<name> [optional unpacked dims]  (at end of string)"
        m_name = re.search(r"([A-Za-z_]\w*)\s*(\[[^\]]*\]\s*)*$", d)
        if not m_name:
            continue

        name = m_name.group(1)  # e.g. 'clk', 'fifo_counter', 'buf_mem'
        sigs.append(name)

    assoc = ", ".join(f".{s}({s})" for s in sigs)

    params_inst = ""
    if params_text:
        pnames = re.findall(r"\bparameter\s+(?:\w+\s+)?(\w+)", params_text)
        if pnames:
            params_inst = "#(" + ", ".join(f".{p}({p})" for p in pnames) + ")"

    return f"bind {dut_name} {dut_name}_prop {params_inst} i_{dut_name}_prop ( {assoc} );\n"


def emit_prop_and_bind_for_module(
    mod_name: str,
    src_file: Path,
    out_root: Path,
    include_file: str,
):
    """
    Generate:
      <out_root>/sva/<mod_name>_prop.sv
      <out_root>/sva/<mod_name>_bind.sv

    Port handling:
      - Get port names from header (ANSI or non-ANSI).
      - Look up their full input/output/inout declarations in the body.
      - Build wrapper ports in header order.
      - Optionally add internal regs/wires/logic as extra inputs.
    """
    try:
        text = src_file.read_text(errors="ignore")
    except Exception as e:
        console.print(f"[red]⚠ Cannot read {src_file}: {e}[/red]")
        return None, None

    m = HEADER_RE.search(text)
    if not m:
        console.print(f"[yellow]⚠ No ANSI/non-ANSI header found in {src_file}; skipping {mod_name}[/yellow]")
        return None, None

    dut_name = m.group("name")
    params_text = m.group("params") or ""
    port_body = m.group("port_body")

    # 1) Port names from header (works for ANSI + non-ANSI)
    header_names = header_port_names(port_body)
    port_names_set = set(header_names)

    # 2) Extract module body
    body_match = re.search(
        r"module\s+" + re.escape(dut_name) + r"\b.*?;(?P<body>.*)endmodule",
        text,
        re.S,
    )
    body = body_match.group("body") if body_match else ""

    # 3) Map name -> full input/output/inout decl from body
    io_map = parse_io_decls_from_body(body) if body else {}

    # 4) Build port declarations in header order
    port_decls = []
    for pname in header_names:
        base = re.sub(r"\[.*?\]", "", pname).strip()
        if base in io_map:
            decl = io_map[base]
        else:
            # Fallback if nothing found in body: treat as scalar input
            decl = f"input {pname}"
        port_decls.append(decl)

    # 5) Optionally add internal regs/wires/logic as extra inputs
    internal_ports = []
    if body:
        body_nc = strip_comments(body)
        reg_re = re.compile(
            r"\b(?:reg|logic|wire)\b\s*"
            r"(?P<packed>\[[^\]]+\]\s*)?"
            r"(?P<names>[^;]+?)"
            r"(?P<unpacked>\[[^\]]+\])?\s*;",
        )
        for m2 in reg_re.finditer(body_nc):
            packed = m2.group("packed") or ""
            unpacked = m2.group("unpacked") or ""
            names_str = m2.group("names")
            names = [n.strip() for n in names_str.split(",") if n.strip()]
            for n in names:
                base = re.sub(r"\[.*?\]", "", n).strip()
                if base in port_names_set:
                    continue  # already a top-level port
                if unpacked:
                    internal_ports.append(f"input {packed}{n}{unpacked}")
                elif packed:
                    internal_ports.append(f"input {packed}{n}")
                else:
                    internal_ports.append(f"input {n}")

    # 6) Merge and dedup (by base name)
    all_ports = port_decls + internal_ports
    unique_ports = []
    seen = set()
    for decl in all_ports:
        d_clean = decl.strip().rstrip(",")
        if not d_clean:
            continue
        sig = d_clean.split()[-1]
        sig = re.sub(r"\[.*?\]", "", sig).strip()
        if sig not in seen:
            seen.add(sig)
            unique_ports.append(d_clean)

    if not unique_ports:
        console.print(f"[red]⚠ No ports found for module {dut_name} in {src_file}[/red]")
        return None, None

    # 7) Emit wrapper and bind files
    sva_dir = out_root / "sva"
    sva_dir.mkdir(parents=True, exist_ok=True)
    prop_path = sva_dir / f"{mod_name}_prop.sv"
    bind_path = sva_dir / f"{mod_name}_bind.sv"

    prop_sv = generate_prop_module_min(dut_name, params_text, unique_ports, include_file)
    bind_sv = generate_bind(dut_name, params_text, unique_ports)

    prop_path.write_text(prop_sv)
    bind_path.write_text(bind_sv)

    console.print(f"[green]✔[/green] Wrote SVA:  {prop_path}")
    console.print(f"[green]✔[/green] Wrote bind: {bind_path}")
    return prop_path, bind_path

# -----------------------------------------------------------------------------
#  Main CLI
# -----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--src", required=True, help="RTL source root (recursive)")
    ap.add_argument("--top", required=True, help="Top module name")
    ap.add_argument("--out", required=True, help="Output Tcl path, e.g. out/FPV.tcl")
    ap.add_argument(
        "--skip-dirs",
        nargs="*",
        default=[".git", "build", "out", "tb"],
        help="Directories to skip when scanning",
    )
    ap.add_argument(
        "--extra-inc",
        dest="extra_inc",
        action="append",
        default=[],
        help="Force-add include dirs",
    )
    ap.add_argument(
        "--defines",
        dest="defines",
        action="append",
        default=[],
        help="Defines NAME or NAME=VAL",
    )
    ap.add_argument(
        "--all-sva",
        action="store_true",
        help="Generate prop+bind for all reachable modules (not just top)",
    )
    ap.add_argument(
        "--prop-include",
        default="properties.sv",
        help='File to include inside *_prop.sv (e.g. "properties.sv")',
    )
    ap.add_argument("--clock-name", help="Override detected clock name")
    ap.add_argument("--reset-expr", help="Override detected reset expression")
    ap.add_argument("--prove-time", default="72h", help="Proof time limit")
    ap.add_argument(
        "--proofgrid-jobs",
        type=int,
        default=180,
        help="Proofgrid job count",
    )
    args = ap.parse_args()

    src_root = Path(args.src).resolve()
    out_tcl_path = Path(args.out).resolve()
    out_root = out_tcl_path.parent

    if not src_root.exists():
        raise SystemExit(f"ERROR: source root not found: {src_root}")

    console.print(f"[cyan]📁 Scanning HDL in {src_root}[/cyan]")
    all_files = find_sv_files(src_root, set(args.skip_dirs))
    modules, packages = index_modules_packages(all_files)

    user_incdirs = [Path(p).resolve() for p in args.extra_inc]
    files_out, incdirs_out, reachable_mods = compute_transitive_closure(
        args.top, modules, packages, src_root, user_incdirs
    )

    # Detect clock/reset (only for top)
    clk_name, rst_name, rst_expr = detect_clk_rst_for_top(src_root, args.top)
    if args.clock_name:
        clk_name = args.clock_name
    if args.reset_expr:
        rst_expr = args.reset_expr

    console.print(
        f"[green]✔ Top module clock={clk_name}, reset={rst_name} (expression: {rst_expr})[/green]"
    )

    # SVA generation
    sva_paths = []
    if args.all_sva:
        for mn in sorted(reachable_mods):
            if mn in modules:
                prop_p, bind_p = emit_prop_and_bind_for_module(
                    mn, modules[mn], out_root, args.prop_include
                )
                if prop_p and bind_p:
                    sva_paths.extend([prop_p, bind_p])
    else:
        top_src = modules[args.top]
        prop_p, bind_p = emit_prop_and_bind_for_module(
            args.top, top_src, out_root, args.prop_include
        )
        if prop_p and bind_p:
            sva_paths.extend([prop_p, bind_p])

    final_files = files_out + sva_paths

    # TCL generation via private writer ONLY
    write_jasper_tcl(
        out_path=out_tcl_path,
        output_dir=out_root,
        module_name=args.top,
        files=final_files,
        incdirs=incdirs_out,
        defines=args.defines,
        clock_name=clk_name,
        reset_expr=rst_expr,
        prove_time=args.prove_time,
        proofgrid_jobs=args.proofgrid_jobs,
    )

    console.print(f"[bold green]✔ DONE:[/bold green] SVA + FPV.tcl generated")


if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        console.print(f"[red]❌ Fatal Error:[/red] {e}")
        sys.exit(1)

