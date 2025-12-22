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
      - DO NOT parse and DO NOT flatten the user filelist.
      - Treat the user filelist as authoritative and reference it via:
            -F <user_filelist>
      - Generate SVA wrapper/bind as usual.
      - Call private write_jasper_tcl() unchanged.
      - Immediately overwrite <out_dir>/files.vc to contain:
            header lines
            +incdir+<out_dir>/sva
            -F <user_filelist>
            <absolute paths to generated SVA files>

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
    r'(?:import\s+.*?;\s*)*'
    r'(?P<params>#\s*\((?P<param_body>.*?)\))?\s*'
    r'\(\s*(?P<port_body>.*?)\)\s*;',
    re.DOTALL | re.MULTILINE,
)

# -----------------------------------------------------------------------------
#  Comment stripping helper
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
        from JG.fpv_tcl_writer import write_jasper_tcl
        console.print('[green]✔ Using private JasperGold TCL writer[/green]')
        return write_jasper_tcl
    except Exception as e:
        console.print('[red]✖ ERROR: Private TCL writer not found.[/red]')
        console.print('    Expected: [bold]hagent-private.JG.fpv_tcl_writer.write_jasper_tcl[/bold]')
        console.print("    Make sure 'hagent-private' is on PYTHONPATH before running this tool.")
        console.print(f'    Import error: {e}')
        sys.exit(1)


write_jasper_tcl = _load_private_tcl_writer()

# -----------------------------------------------------------------------------
#  Port / declaration helpers
# -----------------------------------------------------------------------------
def clean_decl_to_input(decl: str) -> str:
    """Normalize HDL port declarations into 'input' form."""
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
#  SVA generation helpers
# -----------------------------------------------------------------------------
def generate_prop_module_min(dut_name: str, params_text: str, port_decls: list[str], include_file: str):
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

    # Split header port list into tokens on commas (ignore commas in [] or nested parens)
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
        if not name or name in seen:
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
    bind_sv = generate_bind(dut_name, params_text, port_decls, bind_scope)

    prop_path.write_text(prop_sv)
    bind_path.write_text(bind_sv)

    console.print(f'[green]✔[/green] Wrote SVA:  {prop_path}')
    console.print(f'[green]✔[/green] Wrote bind: {bind_path}')
    return prop_path, bind_path


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

def patch_autoprove_to_only_sva_module(tcl_path: Path, sva_module: str, enable: bool = True):
    """
    Replace 'autoprove -all' with:
        autoprove -property {*<sva_module>*} -regexp

    If enable=False, do nothing.
    """
    if not enable:
        return

    tcl_path = tcl_path.resolve()
    if not tcl_path.is_file():
        console.print(f"[yellow]⚠ Cannot patch autoprove; TCL not found:[/yellow] {tcl_path}")
        return

    text = tcl_path.read_text(errors="ignore").splitlines()

    new_lines = []
    replaced = False
    for line in text:
        # replace only the first matching autoprove -all (exact-ish)
        if (not replaced) and re.match(r'^\s*autoprove\s+-all\s*$', line):
            new_lines.append(f"autoprove -property {{.*{sva_module}_prop.*}} -regexp")
            replaced = True
        else:
            new_lines.append(line)

    if not replaced:
        console.print(
            f"[yellow]⚠ Did not find 'autoprove -all' in {tcl_path}. "
            f"Nothing patched.[/yellow]"
        )
        return

    tcl_path.write_text("\n".join(new_lines) + "\n")
    console.print(
        f"[green]✔[/green] Patched autoprove to only run properties matching '*{sva_module}*' in [bold]{tcl_path}[/bold]"
    )

# -----------------------------------------------------------------------------
#  files.vc overwrite (FILELIST MODE ONLY)
# -----------------------------------------------------------------------------
def overwrite_files_vc_for_user_filelist(
    vc_path: Path,
    user_filelist: Path,
    out_root: Path,
    sva_files: list[Path],
    defines: list[str] | None = None,
):
    """
    Overwrite vc_path with:
      header lines
      +define+... (optional)
      +incdir+<out_root>/sva
      -F <user_filelist>
      <absolute SVA file paths>
    """
    vc_path = vc_path.resolve()
    user_filelist = user_filelist.resolve()
    sva_dir = (out_root / 'sva').resolve()

    lines: list[str] = []
    lines.append("+libext+.v")
    lines.append("+libext+.sv")
    lines.append("+libext+.svh")
    lines.append("+librescan")

    for d in (defines or []):
        d = (d or "").strip()
        if d:
            lines.append(f"+define+{d}")

    lines.append(f"+incdir+{sva_dir}")
    lines.append(f"-F {user_filelist}")

    for f in sva_files:
        lines.append(str(Path(f).resolve()))

    vc_path.write_text("\n".join(lines) + "\n")
    console.print(f"[green]✔[/green] Overwrote files.vc for user filelist mode: [bold]{vc_path}[/bold]")


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
        help='Force-add include dirs (also used as -y library dirs) [auto mode only]',
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
        help='Generate prop+bind for all modules (auto mode). In --filelist mode this is disabled.',
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
            'Optional HDL filelist (e.g. core/Flist.cva6). In this mode we DO NOT parse/flatten; '
            'we reference it via "-F <filelist>" in files.vc and append generated SVA paths.'
        ),
    )
    ap.add_argument('--clock-name', help='Override detected clock name')
    ap.add_argument('--reset-expr', help='Override detected reset expression')
    ap.add_argument('--prove-time', default='72h', help='Proof time limit')
    ap.add_argument('--proofgrid-jobs', type=int, default=180, help='Proofgrid job count')
    args = ap.parse_args()

    src_root = Path(args.src).resolve()
    out_tcl_path = Path(args.out).resolve()
    out_root = out_tcl_path.parent.resolve()

    if not src_root.exists():
        raise SystemExit(f'ERROR: source root not found: {src_root}')

    sva_top = args.sva_top or args.top
    user_incdirs = [Path(os.path.expanduser(p)).resolve() for p in args.extra_inc]

    console.print(f'[cyan]📁 Scanning HDL in {src_root}[/cyan]')
    console.print(f'[cyan]ℹ Design top:[/cyan] {args.top}   [cyan]ℹ SVA target:[/cyan] {sva_top}')

    user_filelist_path: Path | None = None

    if args.filelist:
        # FILELIST MODE (no parse, no flatten)
        user_filelist_path = Path(args.filelist).resolve()
        if not user_filelist_path.is_file():
            raise SystemExit(f'ERROR: filelist not found: {user_filelist_path}')

        if args.all_sva:
            console.print(
                "[yellow]⚠ --all-sva is not supported in --filelist mode (no parsing/flattening). "
                "Proceeding with SVA generation for --sva-top only.[/yellow]"
            )

        # We DO NOT build files_out from the filelist.
        files_out: list[Path] = []     # intentionally empty; we will overwrite files.vc later
        incdirs_out: list[Path] = []   # keep empty; +incdir+<out>/sva will be injected into files.vc
    else:
        # AUTO MODE
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

        pkg_files = order_packages_by_dependency(pkg_files)
        files_out = pkg_files + rtl_files

        incdirs_out = []
        for d in user_incdirs:
            if d not in incdirs_out:
                incdirs_out.append(d)

    # Build module → file map
    # In --filelist mode we can't restrict to file_set (we didn't parse it),
    # so we scan src_root and locate modules globally.
    all_files = load_sv_tree(src_root)
    modules: dict[str, Path] = {}
    for path, sv in all_files.items():
        for unit in sv.declared_units():
            modules.setdefault(unit, path)

    # Detect clock/reset for design top
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

    # In filelist mode we only generate for sva_top (even if --all-sva was set).
    if args.all_sva and not args.filelist:
        # auto mode only: generate for all reachable modules in files_out
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
        )
        if prop_p and bind_p:
            sva_paths.extend([prop_p, bind_p])

    # In auto mode: pass RTL+SVA to private writer.
    # In filelist mode: pass only SVA to private writer (we will overwrite files.vc).
    if args.filelist:
        final_files = list(sva_paths)
    else:
        final_files = list(files_out) + list(sva_paths)

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
        lib_dirs=incdirs_out,
        lib_files=None,
    )

    # If we generated SVA only for a specific module (normal flow),
    # patch autoprove to only run assertions for that SVA module.
    # If you are using --all-sva (auto mode), keep autoprove -all.
    patch_autoprove_to_only_sva_module(
        tcl_path=out_tcl_path,
        sva_module=sva_top,
        enable=(not args.all_sva),
    )

    # -------------------------
    # Filelist mode: overwrite files.vc to reference user Flist and append SVA
    # -------------------------
    if user_filelist_path is not None:
        vc_path = out_root / "files.vc"
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
        f'   Filelist   : ' +
        ('[cyan]user-provided (referenced via -F; not parsed)[/cyan]' if args.filelist else '[cyan]auto-discovered[/cyan]')
    )


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        console.print(f'[red]❌ Fatal Error:[/red] {e}')
        sys.exit(1)
