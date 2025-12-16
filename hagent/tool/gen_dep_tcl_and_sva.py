#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Generate:
  1) FPV.tcl using a private JasperGold TCL writer.
  2) Minimal SVA wrapper and bind:
       <out_root>/sva/<sva_top>_prop.sv
       <out_root>/sva/<sva_top>_bind.sv

Modes:

  • Auto mode (default, no --filelist):
      - Use hdl_utils.build_filelist_for_top() to discover package + RTL files
        for the design top.

  • Filelist mode (when --filelist is given):
      - Read HDL file paths from a user-supplied text file (one path per line).
      - Supports common Synopsys-style constructs:
          // comments
          #  comments
          +incdir+<path>
          -incdir+<path>
          -f <other_filelist>
          -F <other_filelist>
      - Environment variables like $VAR or ${VAR} in paths are expanded.
      - Dependencies are NOT auto-discovered; the filelist is assumed complete.

Design vs SVA module:

  --top     : design top module name (used for clock/reset detection and
              Jasper 'elaborate -top <top>')
  --sva-top : module to generate *_prop.sv and *_bind.sv for.
              Defaults to --top (can be a submodule).
"""

import re
import os
import sys
import argparse
from pathlib import Path
from rich.console import Console

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
    Load the JasperGold TCL writer from a private repo that must be on PYTHONPATH.

    There is intentionally NO public fallback. If the private writer is missing,
    this tool errors out.
    """
    try:
        from JG.fpv_tcl_writer import write_jasper_tcl  # type: ignore[import]

        console.print('[green]✔ Using private JasperGold TCL writer[/green]')
        return write_jasper_tcl
    except Exception as e:
        console.print('[red]✖ ERROR: Private TCL writer not found.[/red]')
        console.print('    Expected: [bold]JG.fpv_tcl_writer.write_jasper_tcl[/bold]')
        console.print("    Make sure your private Jasper utilities are on PYTHONPATH.")
        console.print(f'    Import error: {e}')
        sys.exit(1)


# Single global instance
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
    token = re.split(r'//', token, maxsplit=1)[0]
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

    depth_paren = 0
    depth_brack = 0

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

    io_re = re.compile(r'\b(input|output|inout)\b(?P<rest>[^;]*);', re.MULTILINE)

    for m in io_re.finditer(body_nc):
        direction = m.group(1)
        rest = m.group('rest')
        names = [x.strip() for x in rest.split(',') if x.strip()]

        last_prefix = ''

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

            if not prefix and last_prefix:
                decl = ' '.join([tokens[0], last_prefix, base_token]).strip()
                tokens = decl.split()
                prefix = last_prefix
            else:
                last_prefix = prefix

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
        m_name = re.search(r'([A-Za-z_]\w*)\s*(\[[^\]]*\]\s*)*$', d)
        if not m_name:
            continue

        name = m_name.group(1)
        sigs.append(name)

    assoc = ', '.join(f'.{s}({s})' for s in sigs)

    params_inst = ''
    if params_text:
        # Get the parameter *names*, even with package types or 'parameter type'
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

    Strategy:
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
    params_text = m.group('params') or ''
    port_body = m.group('port_body') or ''

    # ------------------------------------------------------------------
    # 1) Split header port list into individual declarations
    # ------------------------------------------------------------------
    ports_raw: list[str] = []
    text_ports = strip_comments(port_body)
    buf: list[str] = []

    depth_paren = 0
    depth_brack = 0

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

        if not re.search(r'\b(input|output|inout)\b', tok):
            tok = 'input ' + tok

        decl = clean_decl_to_input(tok)
        name = extract_last_identifier(decl)
        if not name:
            continue
        if name in seen:
            continue
        seen.add(name)

        if not decl.startswith('input'):
            decl = 'input ' + decl

        port_decls.append(decl)

    if not port_decls:
        console.print(f'[red]⚠ No ports found for module {dut_name} in {src_file}[/red]')
        return None, None

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
    before packages that *use* them (e.g. A_pkg before B_pkg that imports A_pkg).

    Heuristic:
      - For each file, detect 'package <name>;' it defines.
      - For each file, detect uses of '<name>::' for any known package name.
      - If file A uses package B, ensure B's file is before A.
    """
    if len(pkg_files) <= 1:
        return pkg_files

    texts = {}
    for f in pkg_files:
        try:
            texts[f] = f.read_text(errors='ignore')
        except Exception:
            texts[f] = ''

    pkg_name_to_file = {}
    file_to_pkg_name = {}
    for f, txt in texts.items():
        m = re.search(r'\bpackage\s+([A-Za-z_]\w*)', txt)
        if m:
            name = m.group(1)
            pkg_name_to_file[name] = f
            file_to_pkg_name[f] = name

    file_uses = {f: set() for f in pkg_files}
    pkg_names = list(pkg_name_to_file.keys())
    for f, txt in texts.items():
        for pname in pkg_names:
            if re.search(r'\b' + re.escape(pname) + r'\s*::', txt):
                file_uses[f].add(pname)

    ordered = pkg_files[:]
    changed = True

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
                if j > i:
                    ordered[i], ordered[j] = ordered[j], ordered[i]
                    changed = True

    return ordered


# -----------------------------------------------------------------------------
#  Filelist parsing (generic)
# -----------------------------------------------------------------------------
def _parse_filelist(
    filelist_path: Path,
    base_dir: Path,
    incdirs_out: set[Path],
    visited: set[Path],
) -> list[Path]:
    """Parse a Synopsys-style HDL filelist into a list of HDL files.

    Supports:
      - // and # comments
      - +incdir+<dir> and -incdir+<dir>
      - -f <other_filelist> and -F <other_filelist> (recursive)
      - Environment variable expansion ($VAR, ${VAR})
    """
    filelist_path = filelist_path.resolve()
    if filelist_path in visited:
        console.print(f'[yellow]⚠ Skipping already-processed filelist:[/yellow] {filelist_path}')
        return []

    visited.add(filelist_path)

    files: list[Path] = []
    try:
        lines = filelist_path.read_text().splitlines()
    except Exception as e:
        raise SystemExit(f'ERROR: cannot read filelist {filelist_path}: {e}')

    for raw in lines:
        line = raw.strip()
        if not line:
            continue

        # comments
        if line.startswith('//') or line.startswith('#'):
            continue

        # handle +incdir+ / -incdir+
        if line.startswith('+incdir+') or line.startswith('-incdir+'):
            # split on the first occurrence of 'incdir+'
            if '+incdir+' in line:
                _, dir_part = line.split('+incdir+', 1)
            else:
                dir_part = line[len('-incdir+') :]
            dir_part = dir_part.strip()
            dir_expanded = os.path.expandvars(dir_part)
            d = Path(dir_expanded)
            if not d.is_absolute():
                d = (base_dir / d).resolve()
            if d.exists():
                incdirs_out.add(d)
            else:
                console.print(f'[yellow]⚠ Include dir from filelist does not exist:[/yellow] {d}')
            continue

        # nested filelists: -f path or -F path
        if line.startswith('-f ') or line.startswith('-F '):
            nested = line[3:].strip()
            nested = os.path.expandvars(nested)
            nested_path = Path(nested)
            if not nested_path.is_absolute():
                nested_path = (base_dir / nested_path).resolve()
            if not nested_path.exists():
                console.print(f'[yellow]⚠ Nested filelist not found:[/yellow] {nested_path}')
                continue
            files.extend(_parse_filelist(nested_path, nested_path.parent, incdirs_out, visited))
            continue

        # Everything else: treat as HDL source file
        expanded = os.path.expandvars(line)
        p = Path(expanded)
        if not p.is_absolute():
            p = (base_dir / p).resolve()
        if not p.exists():
            console.print(f'[yellow]⚠ File from filelist does not exist:[/yellow] {p}')
            continue
        files.append(p)

    return files


# -----------------------------------------------------------------------------
#  Main CLI
# -----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--src', required=True, help='RTL source root (recursive)')
    ap.add_argument('--top', required=True, help='Design top module name')
    ap.add_argument('--out', required=True, help='Output Tcl path, e.g. out/FPV.tcl')
    ap.add_argument(
        '--skip-dirs',
        nargs='*',
        default=['.git', 'build', 'out', 'tb'],
        help='(reserved for future use)',
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
        help='Generate prop+bind for all modules in the filelist (not just one module)',
    )
    ap.add_argument(
        '--sva-top',
        help='Module name for which to generate *_prop.sv and *_bind.sv. Defaults to --top if not set (can be a submodule).',
    )
    ap.add_argument(
        '--prop-include',
        default='properties.sv',
        help='File to include inside *_prop.sv (e.g. "properties.sv")',
    )
    ap.add_argument(
        '--filelist',
        help=(
            'Optional plain-text HDL file list (one file path per line). '
            'If provided, dependencies are NOT auto-discovered and this list '
            'is used as-is.'
        ),
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

    sva_top = args.sva_top or args.top

    # User-provided include dirs (e.g. .../include)
    user_incdirs = [Path(p).resolve() for p in args.extra_inc]
    incdirs_out: set[Path] = set(user_incdirs)

    console.print(f'[cyan]📁 Scanning HDL in {src_root}[/cyan]')
    console.print(f'[cyan]ℹ Design top:[/cyan] {args.top}   [cyan]ℹ SVA target:[/cyan] {sva_top}')

    # -------------------------
    # Filelist vs auto dependency mode
    # -------------------------
    if args.filelist:
        filelist_path = Path(args.filelist).resolve()
        if not filelist_path.is_file():
            raise SystemExit(f'ERROR: filelist not found: {filelist_path}')

        console.print(f'[green]✔ Using user-provided filelist:[/green] {filelist_path}')

        files_out = _parse_filelist(
            filelist_path=filelist_path,
            base_dir=filelist_path.parent,
            incdirs_out=incdirs_out,
            visited=set(),
        )

        pkg_files: list[Path] = []
        rtl_files: list[Path] = files_out
        missing_pkgs: set[str] = set()
    else:
        # Build ordered filelist for the top, including required packages.
        pkg_files, rtl_files, missing_pkgs = build_filelist_for_top(
            rtl_root=src_root,
            top_name=args.top,
            include_dirs=user_incdirs,
        )

        if missing_pkgs:
            console.print(
                '[yellow]⚠ WARNING: Some packages could not be resolved: '
                + ', '.join(sorted(missing_pkgs))
                + '[/yellow]'
            )

        pkg_files = order_packages_by_dependency(pkg_files)
        files_out = pkg_files + rtl_files

    # Final incdirs passed to Jasper (private writer will convert to +incdir)
    incdirs_list = sorted({d.resolve() for d in incdirs_out})

    # -------------------------
    # Build module → file map (restricted to files_out)
    # -------------------------
    all_files = load_sv_tree(src_root)
    file_set = {p.resolve() for p in files_out}

    modules: dict[str, Path] = {}
    for path, sv in all_files.items():
        if path.resolve() not in file_set:
            continue
        for unit in sv.declared_units():
            modules.setdefault(unit, path)

    # Detect clock/reset (only for design top)
    clk_name, rst_name, rst_expr = detect_clk_rst_for_top(src_root, args.top)
    if args.clock_name:
        clk_name = args.clock_name
    if args.reset_expr:
        rst_expr = args.reset_expr

    console.print(
        f'[green]✔ Top module clock={clk_name}, reset={rst_name} '
        f'(expression: {rst_expr})[/green]'
    )

    # -------------------------
    # SVA generation
    # -------------------------
    sva_paths: list[Path] = []

    if args.all_sva:
        reachable_mods = sorted(
            name for name, mpath in modules.items() if mpath.resolve() in file_set
        )
        for mn in reachable_mods:
            src_file = modules[mn]
            prop_p, bind_p = emit_prop_and_bind_for_module(
                mn, src_file, out_root, args.prop_include
            )
            if prop_p and bind_p:
                sva_paths.extend([prop_p, bind_p])
    else:
        target_mod = sva_top
        target_src = modules.get(target_mod)
        if target_src is None:
            raise SystemExit(f"ERROR: module '{target_mod}' not found in provided HDL files.")
        prop_p, bind_p = emit_prop_and_bind_for_module(
            target_mod, target_src, out_root, args.prop_include
        )
        if prop_p and bind_p:
            sva_paths.extend([prop_p, bind_p])

    final_files = files_out + sva_paths

    # -------------------------
    # TCL generation via private writer ONLY
    # -------------------------
    write_jasper_tcl(
        out_path=out_tcl_path,
        output_dir=out_root,
        module_name=args.top,  # design/elaboration top
        files=final_files,
        incdirs=incdirs_list,
        defines=args.defines,
        clock_name=clk_name,
        reset_expr=rst_expr,
        prove_time=args.prove_time,
        proofgrid_jobs=args.proofgrid_jobs,
        lib_dirs=list(incdirs_list),  # treat include dirs also as -y library dirs
        lib_files=None,
    )

    console.print('[bold green]✔ DONE:[/bold green] SVA + FPV.tcl generated')
    console.print(
        f'   Design top : [cyan]{args.top}[/cyan]\n'
        f'   SVA target : [magenta]{sva_top}[/magenta]\n'
        f'   Filelist   : '
        + ('[cyan]user-provided[/cyan]' if args.filelist else '[cyan]auto-discovered[/cyan]')
    )


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        console.print(f'[red]❌ Fatal Error:[/red] {e}')
        sys.exit(1)

