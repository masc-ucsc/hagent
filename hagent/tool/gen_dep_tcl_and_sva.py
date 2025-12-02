#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Generate:
  1) FPV.tcl using the private Jasper TCL writer.
  2) Minimal SVA wrapper and bind:
       <out_dir>/sva/<top>_prop.sv
       <out_dir>/sva/<top>_bind.sv

The public hagent repo does NOT embed any Jasper TCL logic.
All TCL generation must come from the private writer.

Expected private writer:
  from JG.fpv_tcl_writer import write_jasper_tcl
"""

import re
import sys
import argparse
from pathlib import Path
from rich.console import Console

# New HDL utils that do package resolution (riscv_pkg, etc.)
from hagent.tool.utils.hdl_utils import (
    load_sv_tree,
    build_filelist_for_top,
)

from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

console = Console()

# -----------------------------------------------------------------------------
#  Regex for module header parsing
# -----------------------------------------------------------------------------
HEADER_RE = re.compile(
    r'module\s+(?P<name>\w+)\s*'
    r'(?:import\s+.*?;\s*)*'  # optional one or more import lines
    r'(?P<params>#\s*\((?P<param_body>.*?)\))?\s*'  # optional #( ... )
    r'\(\s*(?P<port_body>.*?)\)\s*;',  # (...) ;
    re.DOTALL | re.MULTILINE,
)

# -----------------------------------------------------------------------------
#  Comment stripping helper (local; no longer from hdl_utils)
# -----------------------------------------------------------------------------
_COMMENT_RE = re.compile(
    r'//.*?$|/\*.*?\*/',
    re.DOTALL | re.MULTILINE,
)


def strip_comments(text: str) -> str:
    """Remove // and /* */ comments from HDL text."""
    return re.sub(_COMMENT_RE, '', text)


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
        # This must live ONLY in hagent-private (PYTHONPATH must include it)
        from JG.fpv_tcl_writer import write_jasper_tcl

        console.print('[green]✔ Using hagent-private Jasper TCL writer[/green]')
        return write_jasper_tcl
    except Exception as e:
        console.print('[red]✖ ERROR: Private TCL writer not found.[/red]')
        console.print('    Expected: [bold]hagent_private.JG.fpv_tcl_writer.write_jasper_tcl[/bold]')
        console.print("    Make sure 'hagent-private' is on PYTHONPATH before running this tool.")
        console.print(f'    Import error: {e}')
        sys.exit(1)


# single global instance
write_jasper_tcl = _load_private_tcl_writer()


# -----------------------------------------------------------------------------
#  Port / declaration helpers
# -----------------------------------------------------------------------------
def clean_decl_to_input(decl: str) -> str:
    """Normalize HDL port declarations into 'input' form."""
    decl = re.sub(r'//.*?$', '', decl, flags=re.M)
    decl = re.sub(r'/\*.*?\*/', '', decl, flags=re.S)
    decl = re.sub(r'\s+', ' ', decl).strip().rstrip(',')
    # convert any direction to input
    decl = re.sub(r'\b(output|inout)\b', 'input', decl)
    decl = re.sub(r'\binput\b', 'input', decl)
    # strip net/types
    decl = re.sub(r'\b(wire|reg|logic|var|signed|unsigned)\b', '', decl)
    return re.sub(r'\s+', ' ', decl).strip()


_ID_RE = re.compile(r'\b([\w$]+)\b(?!.*\b[\w$]+\b)')  # last identifier in a string


def extract_last_identifier(token: str) -> str | None:
    token = token.strip()
    if not token:
        return None
    # strip inline // comments if any slipped through
    token = re.split(r'//', token, 1)[0]
    m = _ID_RE.search(token)
    return m.group(1) if m else None


def header_port_names(port_body: str) -> list[str]:
    """
    Heuristic extraction of port names from the module header port list.
    Works for:
      - ANSI ports: 'input logic clk_i, output reg [7:0] data_o'
      - Mixed: 'input clk, rst, input [7:0] a, b'
    """
    text = strip_comments(port_body)
    ports: list[str] = []
    buf: list[str] = []

    depth_paren = 0  # for safety if someone nests ()
    depth_brack = 0  # to ignore commas inside [..]

    for ch in text:
        if ch == '(':
            depth_paren += 1
        elif ch == ')':
            if depth_paren > 0:
                depth_paren -= 1
        elif ch == '[':
            depth_brack += 1
        elif ch == ']':
            if depth_brack > 0:
                depth_brack -= 1

        if ch == ',' and depth_paren == 0 and depth_brack == 0:
            token = ''.join(buf).strip()
            if token:
                name = extract_last_identifier(token)
                if name:
                    ports.append(name)
            buf = []
        else:
            buf.append(ch)

    # last token
    token = ''.join(buf).strip()
    if token:
        name = extract_last_identifier(token)
        if name:
            ports.append(name)

    return ports


def parse_io_decls_from_body(body: str) -> dict[str, str]:
    """
    Parse non-ANSI style I/O declarations from the module body.

    Returns a map: base_name -> cleaned declaration string like:
      'input [7:0] a'
    The declaration string is already converted to 'input' and has
    net types (reg/logic/wire/var/signed/unsigned) removed.
    """
    body_nc = strip_comments(body)
    io_map: dict[str, str] = {}

    # Match "input ... ;", "output ... ;", "inout ... ;" including across newlines
    io_re = re.compile(r'\b(input|output|inout)\b(?P<rest>[^;]*);', re.MULTILINE)

    for m in io_re.finditer(body_nc):
        direction = m.group(1)
        rest = m.group('rest')
        # Split by comma at this declaration level
        names = [x.strip() for x in rest.split(',') if x.strip()]

        last_prefix = ''  # e.g. "[7:0]" to propagate to "b" in "input [7:0] a, b;"

        for n in names:
            raw_decl = f'{direction} {n}'
            decl = clean_decl_to_input(raw_decl)
            if not decl:
                continue

            tokens = decl.split()
            if len(tokens) < 2:
                continue

            base_token = tokens[-1]
            prefix_tokens = tokens[1:-1]
            prefix = ' '.join(prefix_tokens)

            # If this signal has no width/type prefix but a previous sibling did,
            # propagate that prefix (e.g., width) to this signal.
            if not prefix and last_prefix:
                decl = ' '.join([tokens[0], last_prefix, base_token]).strip()
                tokens = decl.split()
                prefix = last_prefix
            else:
                last_prefix = prefix

            # Compute base name (strip any array indexes)
            base = re.sub(r'\[.*?\]', '', base_token).strip()
            if base:
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
    header_params = f' {params_text} ' if params_text else ''
    port_lines = ',\n    '.join(clean_decl_to_input(d) for d in port_decls)

    lines = []
    lines.append(f'module {dut_name}_prop{header_params}(\n    {port_lines}\n);\n')
    lines.append('// properties here')
    if include_file:
        lines.append(f'`include "{include_file}"')
    lines.append('\nendmodule\n')
    return '\n'.join(lines)


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
        d = decl.strip().rstrip(',')
        if not d:
            continue

        # Strip direction / types so we don't accidentally pick 'input' etc.
        # Then:  match "<name> [optional unpacked dims]  (at end of string)"
        m_name = re.search(r'([A-Za-z_]\w*)\s*(\[[^\]]*\]\s*)*$', d)
        if not m_name:
            continue

        name = m_name.group(1)  # e.g. 'clk', 'fifo_counter', 'buf_mem'
        sigs.append(name)

    assoc = ', '.join(f'.{s}({s})' for s in sigs)

    params_inst = ''
    if params_text:
        # Get the parameter *names*, even with package types or 'parameter type'
        # e.g. 'parameter config_pkg::cva6_cfg_t CVA6Cfg = ...'
        #      'parameter type dcache_req_i_t = logic'
        #      'parameter integer DWIDTH = 32'
        pnames = re.findall(r'\bparameter\b[^=]*\b(\w+)\s*(?==)', params_text)
        if pnames:
            params_inst = '#(' + ', '.join(f'.{p}({p})' for p in pnames) + ')'

    return f'bind {dut_name} {dut_name}_prop {params_inst} i_{dut_name}_prop ( {assoc} );\n'


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

    New strategy:
      - Use ONLY the module header (port list) to build wrapper ports.
      - Do NOT mine the body for regs/enums/locals (too error-prone).
      - All ports are turned into 'input' (Jasper-friendly for SVA wrapper).
    """
    try:
        text = src_file.read_text(errors='ignore')
    except Exception as e:
        console.print(f'[red]⚠ Cannot read {src_file}: {e}[/red]')
        return None, None

    m = HEADER_RE.search(text)
    if not m:
        console.print(f'[yellow]⚠ No ANSI/non-ANSI header found in {src_file}; skipping {mod_name}[/yellow]')
        return None, None

    dut_name = m.group('name')
    params_text = m.group('params') or ''  # full "#( ... )" text
    port_body = m.group('port_body') or ''  # text inside "( ... )"

    # ------------------------------------------------------------------
    # 1) Split header port list into individual declarations
    # ------------------------------------------------------------------
    ports_raw: list[str] = []
    text_ports = strip_comments(port_body)
    buf: list[str] = []

    depth_paren = 0  # for safety
    depth_brack = 0  # ignore commas inside [..]

    for ch in text_ports:
        if ch == '(':
            depth_paren += 1
        elif ch == ')':
            if depth_paren > 0:
                depth_paren -= 1
        elif ch == '[':
            depth_brack += 1
        elif ch == ']':
            if depth_brack > 0:
                depth_brack -= 1

        if ch == ',' and depth_paren == 0 and depth_brack == 0:
            token = ''.join(buf).strip()
            if token:
                ports_raw.append(token)
            buf = []
        else:
            buf.append(ch)

    # last token
    token = ''.join(buf).strip()
    if token:
        ports_raw.append(token)

    # ------------------------------------------------------------------
    # 2) Normalize each header port into an 'input' declaration
    # ------------------------------------------------------------------
    port_decls: list[str] = []
    seen: set[str] = set()

    for tok in ports_raw:
        tok = tok.strip()
        if not tok:
            continue

        # Ensure there is a direction keyword
        if not re.search(r'\b(input|output|inout)\b', tok):
            tok = 'input ' + tok

        # Normalize: make everything 'input', strip net types
        decl = clean_decl_to_input(tok)

        # Extract the signal name (last identifier)
        name = extract_last_identifier(decl)
        if not name:
            continue
        if name in seen:
            continue
        seen.add(name)

        # Make sure it starts with 'input'
        if not decl.startswith('input'):
            decl = 'input ' + decl

        port_decls.append(decl)

    if not port_decls:
        console.print(f'[red]⚠ No ports found for module {dut_name} in {src_file}[/red]')
        return None, None

    # ------------------------------------------------------------------
    # 3) Emit wrapper and bind files
    # ------------------------------------------------------------------
    sva_dir = out_root / 'sva'
    sva_dir.mkdir(parents=True, exist_ok=True)
    prop_path = sva_dir / f'{mod_name}_prop.sv'
    bind_path = sva_dir / f'{mod_name}_bind.sv'

    prop_sv = generate_prop_module_min(dut_name, params_text, port_decls, include_file)
    bind_sv = generate_bind(dut_name, params_text, port_decls)

    prop_path.write_text(prop_sv)
    bind_path.write_text(bind_sv)

    console.print(f'[green]✔[/green] Wrote SVA:  {prop_path}')
    console.print(f'[green]✔[/green] Wrote bind: {bind_path}')
    return prop_path, bind_path


def order_packages_by_dependency(pkg_files):
    """
    Reorder package files so that packages providing symbols appear
    before packages that *use* them (e.g. riscv_pkg, config_pkg before ariane_pkg).

    Heuristic:
      - For each file, detect 'package <name>;' it defines.
      - For each file, detect uses of '<name>::' for any known package name.
      - If file A uses package B, ensure B's file is before A.
    """
    if len(pkg_files) <= 1:
        return pkg_files

    # Read all texts once
    texts = {}
    for f in pkg_files:
        try:
            texts[f] = f.read_text(errors='ignore')
        except Exception:
            texts[f] = ''

    # Map: package-name -> file that defines it
    pkg_name_to_file = {}
    file_to_pkg_name = {}
    for f, txt in texts.items():
        m = re.search(r'\bpackage\s+([A-Za-z_]\w*)', txt)
        if m:
            name = m.group(1)
            pkg_name_to_file[name] = f
            file_to_pkg_name[f] = name

    # Map: file -> set of package names it uses (via <name>::)
    file_uses = {f: set() for f in pkg_files}
    pkg_names = list(pkg_name_to_file.keys())
    for f, txt in texts.items():
        for pname in pkg_names:
            # look for 'pname::' usage
            if re.search(r'\b' + re.escape(pname) + r'\s*::', txt):
                file_uses[f].add(pname)

    ordered = pkg_files[:]
    changed = True

    # Bubble until no dependency violations remain
    while changed:
        changed = False
        for i, f in enumerate(list(ordered)):
            uses = file_uses.get(f, set())
            for pname in uses:
                dep_file = pkg_name_to_file.get(pname)
                if not dep_file:
                    continue
                if dep_file not in ordered:
                    continue
                j = ordered.index(dep_file)
                # If the dependency appears AFTER the user, swap them
                if j > i:
                    ordered[i], ordered[j] = ordered[j], ordered[i]
                    changed = True

    return ordered


# -----------------------------------------------------------------------------
#  Main CLI
# -----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--src', required=True, help='RTL source root (recursive)')
    ap.add_argument('--top', required=True, help='Top module name')
    ap.add_argument('--out', required=True, help='Output Tcl path, e.g. out/FPV.tcl')
    ap.add_argument(
        '--skip-dirs',
        nargs='*',
        default=['.git', 'build', 'out', 'tb'],
        help='(unused now) kept for CLI compatibility',
    )
    ap.add_argument(
        '--extra-inc',
        dest='extra_inc',
        action='append',
        default=[],
        help='Force-add include dirs (also used as -y library dirs)',
    )
    ap.add_argument(
        '--defines',
        dest='defines',
        action='append',
        default=[],
        help='Defines NAME or NAME=VAL',
    )
    ap.add_argument(
        '--all-sva',
        action='store_true',
        help='Generate prop+bind for all modules in the filelist (not just top)',
    )
    ap.add_argument(
        '--prop-include',
        default='properties.sv',
        help='File to include inside *_prop.sv (e.g. "properties.sv")',
    )
    ap.add_argument('--clock-name', help='Override detected clock name')
    ap.add_argument('--reset-expr', help='Override detected reset expression')
    ap.add_argument('--prove-time', default='72h', help='Proof time limit')
    ap.add_argument(
        '--proofgrid-jobs',
        type=int,
        default=180,
        help='Proofgrid job count',
    )
    args = ap.parse_args()

    src_root = Path(args.src).resolve()
    out_tcl_path = Path(args.out).resolve()
    out_root = out_tcl_path.parent

    if not src_root.exists():
        raise SystemExit(f'ERROR: source root not found: {src_root}')

    # User-provided include dirs (e.g. .../core/include, .../core/pmp/include)
    user_incdirs = [Path(p).resolve() for p in args.extra_inc]

    console.print(f'[cyan]📁 Scanning HDL in {src_root}[/cyan]')

    # Build ordered filelist for the top, including all required packages.
    # This is where riscv_pkg.sv (or riscv.sv) gets pulled in automatically.
    pkg_files, rtl_files, missing_pkgs = build_filelist_for_top(
        rtl_root=src_root,
        top_name=args.top,
        include_dirs=user_incdirs,
    )

    if missing_pkgs:
        console.print('[yellow]⚠ WARNING: Some packages could not be resolved: ' + ', '.join(sorted(missing_pkgs)) + '[/yellow]')

    #    files_out = pkg_files + rtl_files
    # IMPORTANT: ensure packages are ordered so that providers come
    # before users (e.g. riscv_pkg, config_pkg before ariane_pkg).
    pkg_files = order_packages_by_dependency(pkg_files)

    files_out = pkg_files + rtl_files

    # incdirs passed to Jasper (the private writer will turn these into +incdir)
    incdirs_out = list(user_incdirs)

    # build a simple module -> file map from the whole tree (for SVA)
    all_files = load_sv_tree(src_root)
    modules = {}
    for path, sv in all_files.items():
        # declared_units might include modules/interfaces/programs/packages;
        # we only really care about modules, but harmless if we index others.
        for unit in sv.declared_units():
            modules.setdefault(unit, path)

    # Detect clock/reset (only for top)
    clk_name, rst_name, rst_expr = detect_clk_rst_for_top(src_root, args.top)
    if args.clock_name:
        clk_name = args.clock_name
    if args.reset_expr:
        rst_expr = args.reset_expr

    console.print(f'[green]✔ Top module clock={clk_name}, reset={rst_name} (expression: {rst_expr})[/green]')

    # -------------------------
    # SVA generation
    # -------------------------
    sva_paths = []

    if args.all_sva:
        # Consider all modules that live in the files in our filelist.
        file_set = {p.resolve() for p in files_out}
        reachable_mods = sorted(name for name, mpath in modules.items() if mpath.resolve() in file_set)
        for mn in reachable_mods:
            src_file = modules[mn]
            prop_p, bind_p = emit_prop_and_bind_for_module(mn, src_file, out_root, args.prop_include)
            if prop_p and bind_p:
                sva_paths.extend([prop_p, bind_p])
    else:
        # Only generate for the top
        top_src = modules.get(args.top)
        if top_src is None:
            raise SystemExit(f"ERROR: top module '{args.top}' not found under {src_root}")
        prop_p, bind_p = emit_prop_and_bind_for_module(args.top, top_src, out_root, args.prop_include)
        if prop_p and bind_p:
            sva_paths.extend([prop_p, bind_p])

    final_files = files_out + sva_paths

    # -------------------------
    # TCL generation via private writer ONLY
    # -------------------------
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
        # Treat user-provided extra include dirs also as -y library dirs
        lib_dirs=user_incdirs,
        lib_files=None,
    )

    console.print('[bold green]✔ DONE:[/bold green] SVA + FPV.tcl generated')


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        console.print(f'[red]❌ Fatal Error:[/red] {e}')
        sys.exit(1)
