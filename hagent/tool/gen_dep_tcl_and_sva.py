#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Generate:
  1) FPV.tcl using the private Jasper TCL writer.
  2) Minimal SVA wrapper and bind:
       <out_dir>/sva/<sva_top>_prop.sv
       <out_dir>/sva/<sva_top>_bind.sv

Modes:

  • Auto mode (default, no --filelist):
      - Use hdl_utils.build_filelist_for_top() to discover package + RTL files
        for the design top.

  • Filelist mode (when --filelist is given):
      - Read HDL file paths from a user-supplied text file (e.g. Flist.cva6).
      - Supports the common Synopsys-style directives:
            +incdir+<dir>
            -F <other_filelist>
      - Uses the filelist as the *authoritative* design source description.
        No extra dependency discovery is done.

Design vs SVA module:

  --top     : design top module name (used for clock/reset detection and
              Jasper 'elaborate -top <top>' inside the private writer)
  --sva-top : module to generate *_prop.sv and *_bind.sv for.
              Defaults to --top (can be a submodule).
"""

import os
import re
import sys
import argparse
from pathlib import Path
from rich.console import Console

# New HDL utils that do package resolution etc.
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
    r'(?:import\s+.*?;\s*)*'  # optional import lines
    r'(?P<params>#\s*\((?P<param_body>.*?)\))?\s*'  # optional #( ... )
    r'\(\s*(?P<port_body>.*?)\)\s*;',               # (...) ;
    re.DOTALL | re.MULTILINE,
)

# -----------------------------------------------------------------------------
#  Comment stripping helper (local; no longer from hdl_utils)
# -----------------------------------------------------------------------------
_COMMENT_RE = re.compile(
    r'//.*?$|/\*.*?\*/',
    re.DOTALL | re.MULTILINE,
)


def _expand_path(raw: str) -> str:
    """Expand environment variables and ~ in a path-like string."""
    # First expand env vars like ${CVA6_REPO_DIR}, ${TARGET_CFG}, etc.
    s = os.path.expandvars(raw)
    # Then expand ~user
    s = os.path.expanduser(s)
    return s


def parse_filelist(filelist_path: Path, src_root: Path):
    """
    Parse a Verilog-style filelist that may contain:
      - plain file paths
      - +incdir+<path>
      - nested -F <filelist>
    Returns (files, incdirs).

    All paths go through os.path.expandvars so constructs like
    ${CVA6_REPO_DIR} and ${TARGET_CFG} are handled generically.
    """
    files: list[Path] = []
    incdirs: list[Path] = []

    filelist_path = filelist_path.resolve()
    fl_dir = filelist_path.parent

    console.print(f'[cyan]ℹ Parsing filelist:[/cyan] {filelist_path}')

    def _handle_line(raw_line: str, base_dir: Path):
        nonlocal files, incdirs

        line = raw_line.strip()
        if not line:
            return
        if line.startswith('//') or line.startswith('#'):
            return

        # --- nested filelist: -F <path> ---
        if line.startswith('-F'):
            nested = line[2:].strip()
            if not nested:
                return
            nested = _expand_path(nested)
            npath = Path(nested)
            if not npath.is_absolute():
                npath = (base_dir / npath).resolve()
            if not npath.is_file():
                console.print(f'[yellow]⚠ Nested filelist not found:[/yellow] {npath}')
                return
            # recurse
            nf, ni = _parse_filelist_impl(npath, npath.parent)
            files.extend(nf)
            incdirs.extend(ni)
            return

        # --- include directories: +incdir+<path> ---
        if line.startswith('+incdir+'):
            inc_raw = line[len('+incdir+'):]
            inc_str = _expand_path(inc_raw)
            inc_path = Path(inc_str)
            if not inc_path.is_absolute():
                inc_path = (base_dir / inc_path).resolve()
            if not inc_path.exists():
                console.print(f'[yellow]⚠ Include dir from filelist does not exist:[/yellow] {inc_path}')
            incdirs.append(inc_path)
            return

        # --- plain file path ---
        p_str = _expand_path(line)
        p = Path(p_str)
        if not p.is_absolute():
            # interpret relative to filelist dir *first* (matches simulator Makefiles)
            p = (base_dir / p).resolve()

        if not p.exists():
            console.print(f'[yellow]⚠ File from filelist does not exist:[/yellow] {p}')
            return

        files.append(p)

    def _parse_filelist_impl(path: Path, base_dir: Path):
        local_files: list[Path] = []
        local_incdirs: list[Path] = []
        with path.open() as fl:
            for raw in fl:
                # we'll reuse the outer handler but capture to local lists
                before_files = len(files)
                before_inc = len(incdirs)
                _handle_line(raw, base_dir)
                # pull out any new entries that got appended for this recursion
                if len(files) > before_files:
                    local_files.extend(files[before_files:])
                if len(incdirs) > before_inc:
                    local_incdirs.extend(incdirs[before_inc:])
        return local_files, local_incdirs

    files, incdirs = _parse_filelist_impl(filelist_path, fl_dir)

    # Deduplicate while preserving order
    def _dedup(seq: list[Path]) -> list[Path]:
        seen = set()
        out = []
        for x in seq:
            if x not in seen:
                seen.add(x)
                out.append(x)
        return out

    return _dedup(files), _dedup(incdirs)


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

        console.print('[green]✔ Using private JasperGold TCL writer[/green]')
        return write_jasper_tcl
    except Exception as e:
        console.print('[red]✖ ERROR: Private TCL writer not found.[/red]')
        console.print('    Expected: [bold]hagent-private.JG.fpv_tcl_writer.write_jasper_tcl[/bold]')
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

        last_prefix = ''  # e.g. "[7:0]"

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
#  SVA generation helpers
# -----------------------------------------------------------------------------
def generate_prop_module_min(dut_name: str, params_text: str, port_decls: list[str], include_file: str):
    """
    Create a wrapper module:
      module <dut>_prop #(params) ( input ... );
        `include "<include_file>"
      endmodule

    All DUT ports are turned into inputs so the wrapper is checker-only.
    """
    header_params = f' {params_text} ' if params_text else ''
    port_lines = ',\n    '.join(clean_decl_to_input(d) for d in port_decls)

    lines = []
    lines.append(f'module {dut_name}_prop{header_params}(\n    {port_lines}\n);\n')
    lines.append('// Auto-generated property wrapper. Connect DUT ports as inputs.\n')
    if include_file:
        lines.append(f'`include "{include_file}"\n')
    lines.append('endmodule\n')
    return ''.join(lines)


def generate_bind(dut_name: str, params_text: str, port_decls: list[str], bind_target: str | None = None):
    """Generate bind statement for DUT.

    bind_target:
        - If None: we bind to the DUT module name (type bind): bind <dut_name> ...
        - If a string: used verbatim as the bind scope; can be a module name
          or a hierarchical path under the design top, e.g.
              cva6_i.load_store_unit_i.load_unit_i
    """
    bind_scope = bind_target or dut_name
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
        # Get the parameter *names*
        pnames = re.findall(r'\bparameter\b[^=]*\b(\w+)\s*(?==)', params_text)
        if pnames:
            params_inst = '#(' + ', '.join(f'.{p}({p})' for p in pnames) + ')'

    return f'bind {bind_scope} {dut_name}_prop {params_inst} i_{dut_name}_prop ( {assoc} );\n'


def emit_prop_and_bind_for_module(
    mod_name: str,
    src_file: Path,
    out_root: Path,
    include_file: str,
    bind_scope: str | None = None,
):
    """
    Generate:
      <out_root>/sva/<mod_name>_prop.sv
      <out_root>/sva/<mod_name>_bind.sv
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
    bind_sv = generate_bind(dut_name, params_text, port_decls, bind_scope)

    prop_path.write_text(prop_sv)
    bind_path.write_text(bind_sv)

    console.print(f'[green]✔[/green] Wrote SVA:  {prop_path}')
    console.print(f'[green]✔[/green] Wrote bind: {bind_path}')
    return prop_path, bind_path


def order_packages_by_dependency(pkg_files):
    """
    Reorder package files so that packages providing symbols appear
    before packages that *use* them.
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
#  Legacy generic filelist parser (kept for compatibility, unused by --filelist)
# -----------------------------------------------------------------------------
def _parse_filelist(
    filelist_path: Path,
    src_root: Path,
    user_incdirs: list[Path],
    files_out: list[Path],
    seen_filelists: set[Path],
):
    """
    Legacy Synopsys-style filelist parser.

    NOTE: Not used in the new --filelist flow; kept only so older callers
    that imported this symbol do not break.
    """
    filelist_path = filelist_path.resolve()
    if filelist_path in seen_filelists:
        console.print(f'[yellow]⚠ Nested filelist already processed (cycle?):[/yellow] {filelist_path}')
        return

    if not filelist_path.is_file():
        console.print(f'[yellow]⚠ Nested filelist not found:[/yellow] {filelist_path}')
        return

    seen_filelists.add(filelist_path)
    console.print(f'[cyan]ℹ Parsing filelist:[/cyan] {filelist_path}')

    with filelist_path.open() as fl:
        for raw in fl:
            line = raw.strip()
            if not line or line.startswith('#') or line.startswith('//'):
                continue

            # Expand environment variables if present
            line_expanded = os.path.expandvars(line)

            # +incdir+<dir>
            if line_expanded.startswith('+incdir+'):
                inc_str = line_expanded[len('+incdir+') :].strip()
                if not inc_str:
                    continue
                inc_path = Path(inc_str)
                if not inc_path.is_absolute():
                    inc_path = (src_root.parent / inc_path).resolve()
                if inc_path.is_dir():
                    if inc_path not in user_incdirs:
                        user_incdirs.append(inc_path)
                else:
                    console.print(f'[yellow]⚠ Include dir from filelist does not exist:[/yellow] {inc_path}')
                continue

            # Nested filelist: -F <path> or -F<path> (also accept -f)
            if line_expanded.startswith(('-F', '-f')):
                parts = line_expanded.split(None, 1)
                if len(parts) == 2:
                    nested_str = parts[1].strip()
                else:
                    nested_str = line_expanded[2:].strip()
                if not nested_str:
                    continue
                nested_path = Path(os.path.expandvars(nested_str))
                if not nested_path.is_absolute():
                    nested_path = (filelist_path.parent / nested_path).resolve()
                _parse_filelist(nested_path, src_root, user_incdirs, files_out, seen_filelists)
                continue

            # Plain HDL file entry
            path_str = line_expanded
            p = Path(path_str)
            if not p.is_absolute():
                p = (src_root.parent / p).resolve()
            if not p.exists():
                console.print(f'[yellow]⚠ File from filelist does not exist:[/yellow] {p}')
                continue
            if p not in files_out:
                files_out.append(p)


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
        help='Generate prop+bind for all modules in the filelist (not just one module)',
    )
    ap.add_argument(
        '--sva-top',
        help=('Module name for which to generate *_prop.sv and *_bind.sv. '
              'Defaults to --top if not set (can be a submodule).'),
    )
    ap.add_argument(
        '--bind-scope',
        help=(
            'Optional bind scope. If set, used verbatim in the bind statement, e.g. '
            '"cva6_i.load_store_unit_i.load_unit_i". If omitted, we bind to the '
            'module type (e.g., "load_unit") which is generic and works under any top.'
        ),
    )
    ap.add_argument(
        '--prop-include',
        default='properties.sv',
        help='File to include inside *_prop.sv (e.g. "properties.sv")',
    )
    ap.add_argument(
        '--filelist',
        help=(
            'Optional plain-text HDL file list (e.g. core/Flist.cva6). '
            'When provided, this list is treated as the authoritative '
            'design source description (parsed and flattened here).'
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

    # User-provided include dirs (e.g. .../core/include, .../core/pmp/include)
    user_incdirs = [Path(os.path.expanduser(p)).resolve() for p in args.extra_inc]

    console.print(f'[cyan]📁 Scanning HDL in {src_root}[/cyan]')
    console.print(f'[cyan]ℹ Design top:[/cyan] {args.top}   [cyan]ℹ SVA target:[/cyan] {sva_top}')

    # -------------------------
    # Filelist vs auto dependency mode
    # -------------------------
    if args.filelist:
        # FILELIST MODE:
        # Use the given Flist (e.g. core/Flist.cva6) as the authoritative RTL
        # description, but we flatten it into concrete file paths here.
        filelist_path = Path(args.filelist).resolve()
        if not filelist_path.is_file():
            raise SystemExit(f'ERROR: filelist not found: {filelist_path}')

        console.print(f'[green]✔ Using user-provided filelist:[/green] {filelist_path}')

        # Parse filelist (handles +incdir, -F, env vars)
        rtl_files, fl_incdirs = parse_filelist(filelist_path, src_root)

        # No separate pkg_files in filelist mode
        pkg_files: list[Path] = []
        missing_pkgs = set()

        # Merge include dirs from CLI and filelist
        incdirs_out = list({*user_incdirs, *fl_incdirs})

        files_out: list[Path] = rtl_files

    else:
        # AUTO MODE:
        # Build ordered filelist for the top, including all required packages.
        pkg_files, rtl_files, missing_pkgs = build_filelist_for_top(
            rtl_root=src_root,
            top_name=args.top,
            include_dirs=user_incdirs,
        )

        if missing_pkgs:
            console.print(
                '[yellow]⚠ WARNING: Some packages could not be resolved: ' +
                ', '.join(sorted(missing_pkgs)) + '[/yellow]'
            )

        # Ensure packages are ordered so that providers come before users
        pkg_files = order_packages_by_dependency(pkg_files)
        files_out = pkg_files + rtl_files

        # Include dirs passed to Jasper (the private writer will turn these into +incdir)
        incdirs_out = []
        for d in user_incdirs:
            if d not in incdirs_out:
                incdirs_out.append(d)

    # -------------------------
    # Build module → file map (restricted to files_out)
    # -------------------------
    all_files = load_sv_tree(src_root)
    file_set = {p.resolve() for p in files_out}

    modules = {}
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
    # Fallback if detect function didn't provide an expression
    if not rst_expr and rst_name:
        rst_expr = f'!{rst_name}'

    console.print(f'[green]✔ Top module clock={clk_name}, reset={rst_name} (expression: {rst_expr})[/green]')

    # -------------------------
    # SVA generation
    # -------------------------
    sva_paths = []

    bind_scope = args.bind_scope  # may be None; then we bind to module type

    if args.all_sva:
        # Consider all modules that live in the files in our filelist.
        reachable_mods = sorted(
            name for name, mpath in modules.items() if mpath.resolve() in file_set
        )
        for mn in reachable_mods:
            src_file = modules[mn]
            prop_p, bind_p = emit_prop_and_bind_for_module(
                mn,
                src_file,
                out_root,
                args.prop_include,
                bind_scope if mn == sva_top else None,
            )
            if prop_p and bind_p:
                sva_paths.extend([prop_p, bind_p])
    else:
        # Only generate for requested sva_top (or design top if not given)
        target_mod = sva_top
        target_src = modules.get(target_mod)
        if target_src is None:
            raise SystemExit(f"ERROR: module '{target_mod}' not found in provided HDL files.")
        prop_p, bind_p = emit_prop_and_bind_for_module(
            target_mod,
            target_src,
            out_root,
            args.prop_include,
            bind_scope,
        )
        if prop_p and bind_p:
            sva_paths.extend([prop_p, bind_p])

    final_files = files_out + sva_paths

    # -------------------------
    # TCL generation via private writer ONLY
    # -------------------------
    # NOTE: We *never* emit Jasper commands (analyze/elaborate/etc.) here.
    #       All Jasper-specific Tcl is generated inside the private
    #       hagent-private JG.fpv_tcl_writer.write_jasper_tcl().
    write_jasper_tcl(
        out_path=out_tcl_path,
        output_dir=out_root,
        module_name=args.top,  # design/elaboration top
        files=final_files,
        incdirs=incdirs_out,
        defines=args.defines,
        clock_name=clk_name,
        reset_expr=rst_expr,
        prove_time=args.prove_time,
        proofgrid_jobs=args.proofgrid_jobs,
        # Treat user-provided extra include dirs also as -y library dirs
        lib_dirs=incdirs_out,
        lib_files=None,
    )

    console.print('[bold green]✔ DONE:[/bold green] SVA + FPV.tcl generated')
    console.print(
        f'   Design top : [cyan]{args.top}[/cyan]\n'
        f'   SVA target : [magenta]{sva_top}[/magenta]\n'
        f'   Filelist   : ' +
        ('[cyan]user-provided (flattened here)[/cyan]' if args.filelist else '[cyan]auto-discovered[/cyan]')
    )


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        console.print(f'[red]❌ Fatal Error:[/red] {e}')
        sys.exit(1)
