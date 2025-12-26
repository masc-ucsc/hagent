#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Generate:
  1) FPV.tcl using the private Jasper TCL writer.
  2) Minimal SVA wrapper and bind:
       <out_dir>/sva/<sva_top>_prop.sv
       <out_dir>/sva/<sva_top>_bind.sv

IMPORTANT POLICY (public repo):
  - This script MUST NOT inject or patch any Jasper-related TCL commands.
    All Jasper TCL content/policy lives ONLY in the private writer:
        JG.fpv_tcl_writer.write_jasper_tcl

Modes:
  • Auto mode (default, no --filelist):
      - Use hdl_utils.build_filelist_for_top() to discover package + RTL files.

  • Filelist mode (when --filelist is given):
      - DO NOT parse/flatten the user filelist.
      - Reference it via: -F <user_filelist>
      - Generate SVA wrapper/bind as usual.
      - Call private write_jasper_tcl().
      - Overwrite <out_dir>/files.vc with:
            header lines
            +incdir+<out_dir>/sva
            -F <user_filelist>
            <absolute paths to generated SVA files>

Enhancements / Fixes:
  - Optional --ports-json: use Slang-generated ports.json for wrapper ports.
  - Optional --scoped-ast-json: used as fallback to derive parameter ports/types.
  - FIX: normalize illegal "module.type" strings from ports.json into valid SV:
        "<sva_top>.<T>" -> "<T>"
"""

import os
import re
import sys
import json
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
# Regex for module header parsing (ANSI headers)
# -----------------------------------------------------------------------------
HEADER_RE = re.compile(
    r'\bmodule\s+(?P<name>\w+)\s*'
    r'(?:import\s+.*?;\s*)*'
    r'(?P<params>#\s*\((?P<param_body>.*?)\))?\s*'
    r'\(\s*(?P<port_body>.*?)\)\s*;',
    re.DOTALL | re.MULTILINE,
)

_COMMENT_RE = re.compile(r'//.*?$|/\*.*?\*/', re.DOTALL | re.MULTILINE)


def strip_comments(text: str) -> str:
    return re.sub(_COMMENT_RE, '', text)


# -----------------------------------------------------------------------------
# Private TCL writer loader (no fallback in public repo)
# -----------------------------------------------------------------------------
def _load_private_tcl_writer():
    try:
        from JG.fpv_tcl_writer import write_jasper_tcl

        console.print('[green]✔ Using private JasperGold TCL writer[/green]')
        return write_jasper_tcl
    except Exception as e:
        console.print('[red]✖ ERROR: Private TCL writer not found.[/red]')
        console.print('    Expected: [bold]hagent-private/JG/fpv_tcl_writer.py (module: JG.fpv_tcl_writer)[/bold]')
        console.print("    Make sure 'hagent-private' is on PYTHONPATH before running this tool.")
        console.print(f'    Import error: {e}')
        sys.exit(1)


write_jasper_tcl = _load_private_tcl_writer()


# -----------------------------------------------------------------------------
# Declaration helpers (old path: parse module header)
# -----------------------------------------------------------------------------
def clean_decl_to_input(decl: str) -> str:
    decl = re.sub(r'//.*?$', '', decl, flags=re.M)
    decl = re.sub(r'/\*.*?\*/', '', decl, flags=re.S)
    decl = re.sub(r'\s+', ' ', decl).strip().rstrip(',')
    decl = re.sub(r'\b(output|inout)\b', 'input', decl)
    decl = re.sub(r'\binput\b', 'input', decl)
    decl = re.sub(r'\b(wire|reg|logic|var|signed|unsigned)\b', '', decl)
    return re.sub(r'\s+', ' ', decl).strip()


_ID_RE = re.compile(r'\b([\w$]+)\b(?!.*\b[\w$]+\b)')


def extract_last_identifier(token: str) -> str | None:
    token = token.strip()
    if not token:
        return None
    token = re.split(r'//', token, maxsplit=1)[0]
    m = _ID_RE.search(token)
    return m.group(1) if m else None


# -----------------------------------------------------------------------------
# ports.json / scoped AST helpers (new path)
# -----------------------------------------------------------------------------
def _fix_logic_width_syntax(t: str) -> str:
    # "logic[63:0]" -> "logic [63:0]"
    return re.sub(r'\b(logic|bit|byte|int|shortint|longint|integer)\s*\[', r'\1 [', t)


def normalize_sv_type(type_str: str, sva_top: str, known_type_params: set[str]) -> str:
    """
    Fix illegal "module.type" forms emitted in some downstream JSON:
      load_unit.lsu_ctrl_t -> lsu_ctrl_t
    Keep pkg::type unchanged.
    """
    if not type_str or type_str.strip() in ('-', ''):
        return 'logic'

    t = type_str.strip()
    t = _fix_logic_width_syntax(t)

    # If it's already package-qualified, keep as-is.
    if '::' in t:
        return t

    # If it is "mod.type", and mod == sva_top, strip prefix.
    m = re.match(r'^(?P<mod>[A-Za-z_]\w*)\.(?P<name>[A-Za-z_]\w*)$', t)
    if m and m.group('mod') == sva_top:
        inner = m.group('name')
        # Only strip if it matches a known type-parameter (safe).
        if inner in known_type_params:
            return inner
        # Still strip for safety because SV "module.type" is never legal.
        return inner

    return t


def load_known_type_params_from_scoped_ast(scoped_ast_json: Path) -> set[str]:
    """
    Read your Slang 'scoped_ast.json' (the one created by cli_spec_builder)
    and pull out type parameter port names so we can normalize types safely.
    """
    try:
        data = json.loads(scoped_ast_json.read_text())
        members = data.get('body', {}).get('members', [])
        tp = set()
        for m in members:
            if m.get('kind') == 'TypeParameter' and m.get('isPort'):
                n = m.get('name')
                if n:
                    tp.add(n)
        return tp
    except Exception as e:
        console.print(f'[yellow]⚠ Could not parse scoped ast json {scoped_ast_json}: {e}[/yellow]')
        return set()


def build_params_text_from_scoped_ast(scoped_ast_json: Path) -> str:
    """
    Fallback only: build a minimal parameter port list from scoped AST:
      #(parameter <type> <name>, parameter type <name>, ...)
    No defaults (bind passes actual params).
    """
    try:
        data = json.loads(scoped_ast_json.read_text())
        members = data.get('body', {}).get('members', [])

        value_params = []
        type_params = []

        for m in members:
            if m.get('isPort') and m.get('kind') == 'Parameter':
                ptype = (m.get('type') or 'int').strip()
                pname = (m.get('name') or '').strip()
                if pname:
                    value_params.append((ptype, pname))

            if m.get('isPort') and m.get('kind') == 'TypeParameter':
                pname = (m.get('name') or '').strip()
                if pname:
                    type_params.append(pname)

        if not value_params and not type_params:
            return ''

        lines = ['#(']
        first = True
        for ptype, pname in value_params:
            comma = ',' if not first else ''
            lines.append(f'    {comma}parameter {ptype} {pname}')
            first = False
        for pname in type_params:
            comma = ',' if not first else ''
            lines.append(f'    {comma}parameter type {pname}')
            first = False
        lines.append(')')
        return '\n'.join(lines)
    except Exception:
        return ''


def port_decls_from_ports_json(
    ports_json: Path,
    sva_top: str,
    known_type_params: set[str],
) -> list[str]:
    """
    Convert Slang ports.json into wrapper port decls:
      input <type> <name>
    Force all directions to input (wrapper is passive).
    """
    data = json.loads(ports_json.read_text())
    decls: list[str] = []
    seen: set[str] = set()

    for p in data:
        name = (p.get('name') or '').strip()
        if not name or name in seen:
            continue
        seen.add(name)

        t = normalize_sv_type(p.get('type') or 'logic', sva_top=sva_top, known_type_params=known_type_params)
        # Some ports.json entries may be like "logic[2:0]" already fixed by normalize.
        decls.append(f'input {t} {name}')

    return decls


# -----------------------------------------------------------------------------
# SVA generation
# -----------------------------------------------------------------------------
def generate_prop_module_min(dut_name: str, params_text: str, port_decls: list[str], include_file: str):
    header_params = f' {params_text} ' if params_text else ''
    port_lines = ',\n    '.join(port_decls)

    lines = []
    lines.append(f'module {dut_name}_prop{header_params}(\n    {port_lines}\n);\n')
    lines.append('// Auto-generated property wrapper. Connect DUT ports as inputs.\n')
    if include_file:
        lines.append(f'`include "{include_file}"\n')
    lines.append('endmodule\n')
    return ''.join(lines)


def generate_bind(dut_name: str, params_text: str, port_decls: list[str], bind_target: str | None = None):
    bind_scope = bind_target or dut_name
    sigs = []

    for decl in port_decls:
        d = decl.strip().rstrip(',')
        if not d:
            continue
        m_name = re.search(r'([A-Za-z_]\w*)\s*(\[[^\]]*\]\s*)*$', d)
        if not m_name:
            continue
        sigs.append(m_name.group(1))

    assoc = ', '.join(f'.{s}({s})' for s in sigs)

    params_inst = ''
    if params_text:
        # Extract parameter names including "parameter type X" and "parameter <T> X"
        pnames = re.findall(r'\bparameter\b(?:\s+type)?(?:\s+[\w:$.]+\s+)?\b(\w+)\b\s*(?==|,|\))', params_text)
        pnames = [p for p in pnames if p not in ('parameter', 'type')]
        if pnames:
            params_inst = '#(' + ', '.join(f'.{p}({p})' for p in pnames) + ')'

    return f'bind {bind_scope} {dut_name}_prop {params_inst} i_{dut_name}_prop ( {assoc} );\n'


def find_module_header(text: str, mod_name: str):
    for m in HEADER_RE.finditer(text):
        if m.group('name') == mod_name:
            return m
    return None


def emit_prop_and_bind_for_module(
    mod_name: str,
    src_file: Path,
    out_root: Path,
    include_file: str,
    bind_scope: str | None = None,
    ports_json: Path | None = None,
    scoped_ast_json: Path | None = None,
):
    try:
        text = src_file.read_text(errors='ignore')
    except Exception as e:
        console.print(f'[red]⚠ Cannot read {src_file}: {e}[/red]')
        return None, None

    m = find_module_header(text, mod_name)
    params_text = ''
    port_decls: list[str] = []

    known_type_params: set[str] = set()
    if scoped_ast_json and scoped_ast_json.is_file():
        known_type_params = load_known_type_params_from_scoped_ast(scoped_ast_json)

    # Prefer params from actual module header (keeps defaults)
    if m:
        dut_name = m.group('name')
        params_text = m.group('params') or ''
        port_body = m.group('port_body') or ''
    else:
        dut_name = mod_name
        console.print(f'[yellow]⚠ Could not parse module header for {mod_name} in {src_file}; will fallback.[/yellow]')
        if scoped_ast_json and scoped_ast_json.is_file():
            params_text = build_params_text_from_scoped_ast(scoped_ast_json)
        port_body = ''

    # Prefer ports.json if provided
    if ports_json and ports_json.is_file():
        console.print(f'[cyan]✔ Using ports.json for wrapper ports: {ports_json}[/cyan]')
        port_decls = port_decls_from_ports_json(ports_json, sva_top=mod_name, known_type_params=known_type_params)
    else:
        # Old fallback: parse header port list
        if not m:
            console.print(f'[red]⚠ No ports.json and no parsable module header; cannot emit wrapper for {mod_name}[/red]')
            return None, None

        ports_raw: list[str] = []
        text_ports = strip_comments(port_body)
        buf: list[str] = []
        depth_paren = 0
        depth_brack = 0

        for ch in text_ports:
            if ch == '(':
                depth_paren += 1
            elif ch == ')':
                depth_paren = max(0, depth_paren - 1)
            elif ch == '[':
                depth_brack += 1
            elif ch == ']':
                depth_brack = max(0, depth_brack - 1)

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

        seen: set[str] = set()
        for tok in ports_raw:
            tok = tok.strip()
            if not tok:
                continue
            if not re.search(r'\b(input|output|inout)\b', tok):
                tok = 'input ' + tok
            decl = clean_decl_to_input(tok)
            name = extract_last_identifier(decl)
            if not name or name in seen:
                continue
            seen.add(name)
            if not decl.startswith('input'):
                decl = 'input ' + decl
            port_decls.append(decl)

    # Final sanity
    if not port_decls:
        console.print(f'[red]⚠ No ports found for module {dut_name} in {src_file}[/red]')
        return None, None

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


# -----------------------------------------------------------------------------
# Package ordering (auto mode)
# -----------------------------------------------------------------------------
def order_packages_by_dependency(pkg_files):
    if len(pkg_files) <= 1:
        return pkg_files

    texts = {}
    for f in pkg_files:
        try:
            texts[f] = f.read_text(errors='ignore')
        except Exception:
            texts[f] = ''

    pkg_name_to_file = {}
    for f, txt in texts.items():
        m = re.search(r'\bpackage\s+([A-Za-z_]\w*)', txt)
        if m:
            pkg_name_to_file[m.group(1)] = f

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
            for pname in file_uses.get(f, set()):
                dep_file = pkg_name_to_file.get(pname)
                if not dep_file or dep_file not in ordered:
                    continue
                j = ordered.index(dep_file)
                if j > i:
                    ordered[i], ordered[j] = ordered[j], ordered[i]
                    changed = True
    return ordered


# -----------------------------------------------------------------------------
# files.vc overwrite (FILELIST MODE ONLY)
# -----------------------------------------------------------------------------
def overwrite_files_vc_for_user_filelist(
    vc_path: Path,
    user_filelist: Path,
    out_root: Path,
    sva_files: list[Path],
    defines: list[str] | None = None,
):
    vc_path = vc_path.resolve()
    user_filelist = user_filelist.resolve()
    sva_dir = (out_root / 'sva').resolve()

    lines: list[str] = []
    lines.append('+libext+.v')
    lines.append('+libext+.sv')
    lines.append('+libext+.svh')
    lines.append('+librescan')

    for d in defines or []:
        d = (d or '').strip()
        if d:
            lines.append(f'+define+{d}')

    lines.append(f'+incdir+{sva_dir}')
    lines.append(f'-F {user_filelist}')

    for f in sva_files:
        lines.append(str(Path(f).resolve()))

    vc_path.write_text('\n'.join(lines) + '\n')
    console.print(f'[green]✔[/green] Overwrote files.vc for user filelist mode: [bold]{vc_path}[/bold]')


# -----------------------------------------------------------------------------
# Main
# -----------------------------------------------------------------------------
def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--src', required=True, help='RTL source root (recursive)')
    ap.add_argument('--top', required=True, help='Design top module name')
    ap.add_argument('--out', required=True, help='Output Tcl path, e.g. out/FPV.tcl')

    ap.add_argument(
        '--extra-inc',
        dest='extra_inc',
        action='append',
        default=[],
        help='Force-add include dirs (also used as -y library dirs) [auto mode only]',
    )
    ap.add_argument('--defines', dest='defines', action='append', default=[], help='Defines NAME or NAME=VAL')

    ap.add_argument(
        '--all-sva',
        action='store_true',
        help='Generate prop+bind for all modules (auto mode). In --filelist mode this is disabled.',
    )
    ap.add_argument('--sva-top', help='Module for which to generate *_prop.sv and *_bind.sv for. Defaults to --top.')

    ap.add_argument('--bind-scope', help='Optional bind scope (hierarchical instance path).')

    ap.add_argument('--prop-include', default='properties.sv', help='File to include inside *_prop.sv (e.g. "properties.sv")')

    ap.add_argument('--filelist', help='Optional HDL filelist (referenced via "-F <filelist>" in files.vc).')

    ap.add_argument('--clock-name', help='Override detected clock name')
    ap.add_argument('--reset-expr', help='Override detected reset expression')
    ap.add_argument('--prove-time', default='72h', help='Proof time limit')
    ap.add_argument('--proofgrid-jobs', type=int, default=180, help='Proofgrid job count')

    # NEW inputs (optional)
    ap.add_argument('--ports-json', help='Optional Slang ports.json (for wrapper port widths/types).')
    ap.add_argument('--scoped-ast-json', help='Optional Slang scoped_ast.json (for type-parameter names / fallback params).')

    args = ap.parse_args()

    src_root = Path(args.src).resolve()
    out_tcl_path = Path(args.out).resolve()
    out_root = out_tcl_path.parent.resolve()

    if not src_root.exists():
        raise SystemExit(f'ERROR: source root not found: {src_root}')

    sva_top = args.sva_top or args.top
    user_incdirs = [Path(os.path.expanduser(p)).resolve() for p in args.extra_inc]

    ports_json = Path(os.path.expanduser(args.ports_json)).resolve() if args.ports_json else None
    scoped_ast_json = Path(os.path.expanduser(args.scoped_ast_json)).resolve() if args.scoped_ast_json else None

    console.print(f'[cyan]📁 Scanning HDL in {src_root}[/cyan]')
    console.print(f'[cyan]ℹ Design top:[/cyan] {args.top}   [cyan]ℹ SVA target:[/cyan] {sva_top}')
    if ports_json:
        console.print(f'[cyan]ℹ Found ports.json:[/cyan] {ports_json}')
    if scoped_ast_json:
        console.print(f'[cyan]ℹ Found scoped_ast.json:[/cyan] {scoped_ast_json}')

    user_filelist_path: Path | None = None

    if args.filelist:
        user_filelist_path = Path(args.filelist).resolve()
        if not user_filelist_path.is_file():
            raise SystemExit(f'ERROR: filelist not found: {user_filelist_path}')

        if args.all_sva:
            console.print('[yellow]⚠ --all-sva not supported in --filelist mode; generating only for --sva-top.[/yellow]')

        files_out: list[Path] = []
        incdirs_out: list[Path] = []
    else:
        pkg_files, rtl_files, missing_pkgs = build_filelist_for_top(
            rtl_root=src_root,
            top_name=args.top,
            include_dirs=user_incdirs,
        )

        if missing_pkgs:
            console.print(
                '[yellow]⚠ WARNING: Some packages could not be resolved: ' + ', '.join(sorted(missing_pkgs)) + '[/yellow]'
            )

        pkg_files = order_packages_by_dependency(pkg_files)
        files_out = pkg_files + rtl_files

        incdirs_out = []
        for d in user_incdirs:
            if d not in incdirs_out:
                incdirs_out.append(d)

    all_files = load_sv_tree(src_root)
    modules: dict[str, Path] = {}
    for path, sv in all_files.items():
        for unit in sv.declared_units():
            modules.setdefault(unit, path)

    clk_name, rst_name, rst_expr = detect_clk_rst_for_top(src_root, args.top)
    if args.clock_name:
        clk_name = args.clock_name
    if args.reset_expr:
        rst_expr = args.reset_expr
    if not rst_expr and rst_name:
        rst_expr = f'!{rst_name}'

    console.print(f'[green]✔ Top module clock={clk_name}, reset={rst_name} (expression: {rst_expr})[/green]')

    # -------------------------
    # SVA generation
    # -------------------------
    sva_paths: list[Path] = []
    bind_scope = args.bind_scope

    if args.all_sva and not args.filelist:
        file_set = {p.resolve() for p in files_out}
        reachable_mods = sorted(name for name, mpath in modules.items() if mpath.resolve() in file_set)
        for mn in reachable_mods:
            src_file = modules[mn]
            prop_p, bind_p = emit_prop_and_bind_for_module(
                mn,
                src_file,
                out_root,
                args.prop_include,
                bind_scope if mn == sva_top else None,
                ports_json=ports_json if mn == sva_top else None,
                scoped_ast_json=scoped_ast_json if mn == sva_top else None,
            )
            if prop_p and bind_p:
                sva_paths.extend([prop_p, bind_p])
    else:
        target_mod = sva_top
        target_src = modules.get(target_mod)
        if target_src is None:
            raise SystemExit(f"ERROR: module '{target_mod}' not found under src root: {src_root}")
        prop_p, bind_p = emit_prop_and_bind_for_module(
            target_mod,
            target_src,
            out_root,
            args.prop_include,
            bind_scope,
            ports_json=ports_json,
            scoped_ast_json=scoped_ast_json,
        )
        if prop_p and bind_p:
            sva_paths.extend([prop_p, bind_p])

    # In auto mode: pass RTL+SVA to private writer.
    # In filelist mode: pass only SVA to private writer (we overwrite files.vc).
    final_files = list(sva_paths) if args.filelist else (list(files_out) + list(sva_paths))

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
        lib_dirs=incdirs_out,
        lib_files=None,
        sva_module=sva_top,
    )

    if user_filelist_path is not None:
        vc_path = out_root / 'files.vc'
        overwrite_files_vc_for_user_filelist(
            vc_path=vc_path,
            user_filelist=user_filelist_path,
            out_root=out_root,
            sva_files=sva_paths,
            defines=args.defines,
        )

    console.print('[bold green]✔ DONE:[/bold green] SVA + FPV.tcl generated')
    console.print(
        f'   Design top : [cyan]{args.top}[/cyan]\n'
        f'   SVA target : [magenta]{sva_top}[/magenta]\n'
        f'   Filelist   : '
        + ('[cyan]user-provided (referenced via -F; not parsed)[/cyan]' if args.filelist else '[cyan]auto-discovered[/cyan]')
    )


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        console.print(f'[red]❌ Fatal Error:[/red] {e}')
        sys.exit(1)
