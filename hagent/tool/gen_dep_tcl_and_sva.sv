#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Generate:
  1) FPV.tcl using the private Jasper TCL writer.
  2) Minimal SVA wrapper and bind:
       <out_dir>/sva/<sva_top>_prop.sv
       <out_dir>/sva/<sva_top>_bind.sv

ENHANCEMENTS (Dec 2025):
  - FIXED: Comprehensive type parameter extraction from ports
  - FIXED: Package import preservation from original module
  - FIXED: Clock/reset detection for all naming conventions
  - FIXED: Package extraction from port types (ariane_pkg::alu_bypass_t)
"""

import os
import re
import sys
import json
import argparse
import shutil
from pathlib import Path
from rich.console import Console

from hagent.tool.utils.hdl_utils import (
    load_sv_tree,
    build_filelist_for_top,
)

from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

console = Console()

# Regex patterns
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


# Load private TCL writer
def _load_private_tcl_writer():
    try:
        from JG.fpv_tcl_writer import write_jasper_tcl

        console.print('[green]✔ Using private JasperGold TCL writer[/green]')
        return write_jasper_tcl
    except Exception:
        console.print('[red]✖ ERROR: Private TCL writer not found.[/red]')
        sys.exit(1)


write_jasper_tcl = _load_private_tcl_writer()


# OLD: Basic declaration helpers
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


# NEW: Type system helpers
def is_builtin_sv_type(type_str: str) -> bool:
    """Check if type is built-in SystemVerilog."""
    builtin_types = {
        'logic',
        'bit',
        'reg',
        'wire',
        'byte',
        'shortint',
        'int',
        'longint',
        'integer',
        'time',
        'real',
        'realtime',
        'shortreal',
        'string',
        'event',
    }

    base_type = re.sub(r'\s*\[.*?\]\s*', '', type_str).strip()
    base_type = re.sub(r'\s+', ' ', base_type)

    if base_type in builtin_types:
        return True

    for bt in builtin_types:
        if base_type.startswith(bt + ' ') or base_type == bt:
            return True

    return False


def extract_custom_types_from_ports(ports: list, sva_top: str) -> set[str]:
    """Extract all custom types needing parameterization."""
    custom_types: set[str] = set()

    for p in ports:
        if not isinstance(p, dict):
            continue

        type_str = (p.get('type') or '').strip()
        if not type_str or type_str == '-':
            continue

        base_type = re.sub(r'\s*\[.*?\]\s*', '', type_str).strip()

        if is_builtin_sv_type(base_type):
            continue

        if '::' in base_type:  # Package-qualified, skip
            continue

        m = re.match(r'^(?P<mod>[A-Za-z_]\w*)\.(?P<name>[A-Za-z_]\w*)$', base_type)
        if m:
            custom_types.add(m.group('name'))
            continue

        custom_types.add(base_type)

    return custom_types


def extract_packages_from_port_types(ports_json: Path) -> list[str]:
    """
    Extract package names from package-qualified types in ports.
    E.g., ariane_pkg::alu_bypass_t -> import ariane_pkg::*;
    """
    try:
        ports = json.loads(ports_json.read_text())
    except Exception:
        return []

    packages = set()
    for p in ports:
        if not isinstance(p, dict):
            continue
        type_str = (p.get('type') or '').strip()
        # Match pkg::type patterns
        m = re.match(r'^([A-Za-z_]\w*)::(\w+)', type_str)
        if m:
            packages.add(m.group(1))

    return [f'import {pkg}::*;' for pkg in sorted(packages)]


def extract_package_imports_from_module(src_file: Path, mod_name: str) -> list[str]:
    """
    Extract package imports from module source.
    Handles both:
      module foo import pkg::*; (...)
      module foo import pkg::*; #(...) (...)
    """
    try:
        text = src_file.read_text(errors='ignore')
    except Exception:
        return []

    # Find the module declaration
    module_start = re.compile(rf'\bmodule\s+{re.escape(mod_name)}\b', re.DOTALL)

    m = module_start.search(text)
    if not m:
        return []

    # Get text from module name to the end of the header
    start_pos = m.end()
    remaining = text[start_pos:]

    # Extract just the import section - between module name and #( or (
    header_end = len(remaining)
    for marker in ['#(', '(']:
        idx = remaining.find(marker)
        if idx != -1 and idx < header_end:
            header_end = idx

    header = remaining[:header_end]

    # Match imports with or without trailing semicolons
    # Pattern handles: import pkg::*; or import pkg::*
    import_pattern = re.compile(r'import\s+([A-Za-z_]\w*)::\*\s*;?')
    imports = import_pattern.findall(header)

    return [f'import {pkg}::*;' for pkg in imports]


# Type normalization
def _fix_logic_width_syntax(t: str) -> str:
    return re.sub(r'\b(logic|bit|byte|int|shortint|longint|integer)\s*\[', r'\1 [', t)


def normalize_sv_type(type_str: str, sva_top: str, known_type_params: set[str]) -> str:
    """Normalize type strings - preserve package-qualified types and strip module. prefixes."""
    if not type_str or type_str.strip() in ('-', ''):
        return 'logic'

    t = _fix_logic_width_syntax(type_str.strip())

    # Split trailing dimensions (e.g. issue_stage.foo_t[0:0][31:0])
    base = t
    dims = ''
    while True:
        m = re.search(r'(\s*\[[^\]]+\]\s*)$', base)
        if not m:
            break
        dims = m.group(1) + dims
        base = base[: m.start()].rstrip()

    # Preserve package-qualified types
    if '::' in base:
        return base + dims

    # Strip module.type prefix when module matches sva_top
    m = re.match(r'^(?P<mod>[A-Za-z_]\w*)\.(?P<name>[A-Za-z_]\w*)$', base)
    if m and m.group('mod') == sva_top:
        inner = m.group('name')
        # If it's a known type param, use it; otherwise still prefer inner
        return inner + dims

    return base + dims


def load_known_type_params_from_scoped_ast(scoped_ast_json: Path) -> set[str]:
    """Load type parameter names from scoped AST."""
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
    except Exception:
        return set()


def build_params_text_from_scoped_ast(scoped_ast_json: Path) -> str:
    """Build parameter list from scoped AST."""
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


def build_type_parameters_from_ports(ports_json: Path, sva_top: str, scoped_ast_json: Path | None = None) -> str:
    """NEW: Build type parameter declarations from ports."""
    try:
        ports = json.loads(ports_json.read_text())
    except Exception:
        return ''

    custom_types = extract_custom_types_from_ports(ports, sva_top)

    if not custom_types:
        return ''

    type_params = [f'parameter type {t} = logic' for t in sorted(custom_types)]

    return ',\n    '.join(type_params)


def port_decls_from_ports_json(
    ports_json: Path,
    sva_top: str,
    known_type_params: set[str],
) -> list[str]:
    """Convert ports.json to input declarations."""
    data = json.loads(ports_json.read_text())
    decls: list[str] = []
    seen: set[str] = set()

    for p in data:
        name = (p.get('name') or '').strip()
        if not name or name in seen:
            continue
        seen.add(name)

        t = normalize_sv_type(p.get('type') or 'logic', sva_top=sva_top, known_type_params=known_type_params)
        decls.append(f'input {t} {name}')

    return decls


def detect_clk_rst_from_ports_json(ports_json: Path) -> tuple[str, str, str, str]:
    """Detect clock/reset from ports.json."""
    try:
        data = json.loads(ports_json.read_text(encoding='utf-8'))
    except Exception as e:
        return '', '', '', f'error:{e}'

    if not isinstance(data, list):
        return '', '', '', 'not_list'

    names: list[str] = []
    for p in data:
        if isinstance(p, dict) and p.get('name'):
            names.append(str(p['name']).strip())

    seen = set()
    ports = []
    for n in names:
        if n and n not in seen:
            ports.append(n)
            seen.add(n)

    if not ports:
        return '', '', '', 'empty'

    clk_patterns = [r'^clk$', r'^clock$', r'.*clk.*', r'.*clock.*']
    rst_patterns = [r'^rst$', r'^reset$', r'^resetn$', r'^rst_n$', r'.*reset.*', r'.*rst.*']

    def rank_match(port: str, pats: list[str]) -> int | None:
        pl = port.lower()
        for i, pat in enumerate(pats):
            if re.match(pat, pl):
                return i
        return None

    clk_best = ''
    clk_best_rank = None
    for p in ports:
        rnk = rank_match(p, clk_patterns)
        if rnk is None:
            continue
        if clk_best_rank is None or rnk < clk_best_rank:
            clk_best = p
            clk_best_rank = rnk

    rst_best = ''
    rst_best_rank = None
    for p in ports:
        rnk = rank_match(p, rst_patterns)
        if rnk is None:
            continue
        if rst_best_rank is None or rnk < rst_best_rank:
            rst_best = p
            rst_best_rank = rnk

    rst_expr = ''
    if rst_best:
        low = rst_best.lower()
        is_active_low = low.endswith('n') or low.endswith('_n') or low.endswith('ni') or low.endswith('_ni')
        rst_expr = f'!{rst_best}' if is_active_low else rst_best

    return clk_best, rst_best, rst_expr, str(ports_json)


def ensure_include_file_in_sva_dir(out_root: Path, include_file: str) -> str:
    """Ensure include file exists in sva/ directory."""
    sva_dir = (out_root / 'sva').resolve()
    sva_dir.mkdir(parents=True, exist_ok=True)

    inc = (include_file or '').strip()
    if not inc:
        inc = 'properties.sv'

    inc_path = Path(inc)
    basename = inc_path.name
    dest = (sva_dir / basename).resolve()

    candidates: list[Path] = []
    if inc_path.is_absolute():
        candidates.append(inc_path)
    else:
        candidates.append((out_root / inc).resolve())
        candidates.append((Path.cwd() / inc).resolve())
        candidates.append(inc_path.resolve())

    src = None
    for c in candidates:
        if c.is_file():
            src = c
            break

    if src:
        try:
            if src.resolve() != dest:
                shutil.copyfile(src, dest)
            console.print(f'[green]✔[/green] Include file ready: {dest}')
        except Exception:
            dest.write_text('// STUB\n', encoding='utf-8')
    else:
        try:
            if not dest.exists():
                dest.write_text('// Auto-generated stub\n', encoding='utf-8')
            console.print(f'[yellow]⚠ Wrote stub include: {dest}[/yellow]')
        except Exception:
            raise

    return basename


# MODIFIED: Wrapper generation with type parameters and package imports
def generate_prop_module_min(
    dut_name: str,
    params_text: str,
    port_decls: list[str],
    include_file: str,
    type_params_text: str = '',
    package_imports: list[str] | None = None,
):
    """Generate property wrapper with imports and type parameters."""
    lines = []

    # Module declaration
    lines.append(f'module {dut_name}_prop')

    # Add package imports AFTER module name, BEFORE parameters
    # This is the correct SystemVerilog syntax:
    #   module foo
    #     import pkg::*;
    #   #(...)
    if package_imports:
        for imp in package_imports:
            lines.append(f'  {imp}')

    # Collect all parameters
    all_params: list[str] = []

    # Extract value/type parameters from params_text
    if params_text:
        param_match = re.search(r'#\s*\((.*?)\)', params_text, re.DOTALL)
        if param_match:
            param_body = param_match.group(1)
            for line in param_body.split('\n'):
                line = line.strip().rstrip(',')
                if line and 'parameter' in line:
                    all_params.append(line)

    # Add type parameters from ports
    if type_params_text:
        for line in type_params_text.split('\n'):
            line = line.strip().rstrip(',')
            if line:
                all_params.append(line)

    # Write parameter block
    if all_params:
        lines.append('#(')
        for i, p in enumerate(all_params):
            comma = ',' if i < len(all_params) - 1 else ''
            lines.append(f'    {p}{comma}')
        lines.append(') (')
    else:
        lines.append(' (')

    # Write port declarations
    port_lines = ',\n    '.join(port_decls)
    lines.append(f'    {port_lines}')
    lines.append(');\n')

    # Module body
    lines.append('// Auto-generated property wrapper. Connect DUT ports as inputs.\n')
    if include_file:
        lines.append(f'`include "{include_file}"\n')

    lines.append('endmodule\n')

    return '\n'.join(lines)


def generate_bind(dut_name: str, params_text: str, port_decls: list[str], bind_target: str | None = None):
    """Generate bind statement."""
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
        pnames = re.findall(r'\bparameter\b(?:\s+type)?(?:\s+[\w:$.]+\s+)?\b(\w+)\b\s*(?==|,|\))', params_text)
        pnames = [p for p in pnames if p not in ('parameter', 'type')]
        if pnames:
            params_inst = '#(' + ', '.join(f'.{p}({p})' for p in pnames) + ')'

    return f'bind {bind_scope} {dut_name}_prop {params_inst} i_{dut_name}_prop ( {assoc} );\n'


def find_module_header(text: str, mod_name: str):
    """Find module header in text."""
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
    """MODIFIED: Generate wrapper with type parameters and imports."""
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

    if m:
        dut_name = m.group('name')
        params_text = m.group('params') or ''
        port_body = m.group('port_body') or ''
    else:
        dut_name = mod_name
        console.print(f'[yellow]⚠ Could not parse module header for {mod_name}[/yellow]')
        if scoped_ast_json and scoped_ast_json.is_file():
            params_text = build_params_text_from_scoped_ast(scoped_ast_json)
        port_body = ''

    # FIXED: Extract package imports from BOTH sources
    # 1. From module source (import ariane_pkg::*; in module header)
    package_imports = extract_package_imports_from_module(src_file, mod_name)
    console.print(f'[cyan]ℹ Package imports from module source: {package_imports}[/cyan]')

    # 2. From port types (ariane_pkg::alu_bypass_t -> import ariane_pkg::*)
    if ports_json and ports_json.is_file():
        type_imports = extract_packages_from_port_types(ports_json)
        console.print(f'[cyan]ℹ Package imports from port types: {type_imports}[/cyan]')
        # Merge, avoiding duplicates
        existing = set(package_imports)
        for imp in type_imports:
            if imp not in existing:
                package_imports.append(imp)
                existing.add(imp)

    console.print(f'[green]✔ Final package imports: {package_imports}[/green]')

    # Build type parameters from ports
    type_params_text = ''
    if ports_json and ports_json.is_file():
        type_params_text = build_type_parameters_from_ports(ports_json, mod_name, scoped_ast_json)

    # Build port declarations
    if ports_json and ports_json.is_file():
        console.print(f'[cyan]✔ Using ports.json: {ports_json}[/cyan]')
        port_decls = port_decls_from_ports_json(ports_json, sva_top=mod_name, known_type_params=known_type_params)
    else:
        if not m:
            console.print(f'[red]⚠ No ports for {mod_name}[/red]')
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

    if not port_decls:
        console.print(f'[red]⚠ No ports found for {dut_name}[/red]')
        return None, None

    sva_dir = out_root / 'sva'
    sva_dir.mkdir(parents=True, exist_ok=True)
    prop_path = sva_dir / f'{mod_name}_prop.sv'
    bind_path = sva_dir / f'{mod_name}_bind.sv'

    prop_sv = generate_prop_module_min(
        dut_name, params_text, port_decls, include_file, type_params_text=type_params_text, package_imports=package_imports
    )
    bind_sv = generate_bind(dut_name, params_text, port_decls, bind_scope)

    prop_path.write_text(prop_sv)
    bind_path.write_text(bind_sv)

    console.print(f'[green]✔ Wrote wrapper: {prop_path}[/green]')
    console.print(f'[green]✔ Wrote bind   : {bind_path}[/green]')
    return prop_path, bind_path


def order_packages_by_dependency(pkg_files):
    """Order package files by dependency."""
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


def overwrite_files_vc_for_user_filelist(
    vc_path: Path,
    user_filelist: Path,
    out_root: Path,
    sva_files: list[Path],
    defines: list[str] | None = None,
):
    """Overwrite files.vc for filelist mode."""
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
    console.print('[green]✔ Overwrote files.vc[/green]')


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--src', required=True, help='RTL source root')
    ap.add_argument('--top', required=True, help='Design top module')
    ap.add_argument('--out', required=True, help='Output TCL path')
    ap.add_argument('--extra-inc', dest='extra_inc', action='append', default=[], help='Include dirs')
    ap.add_argument('--defines', dest='defines', action='append', default=[], help='Defines')
    ap.add_argument('--all-sva', action='store_true', help='Generate for all modules')
    ap.add_argument('--sva-top', help='SVA target module')
    ap.add_argument('--bind-scope', help='Bind scope')
    ap.add_argument('--prop-include', default='properties.sv', help='Include file')
    ap.add_argument('--filelist', help='HDL filelist')
    ap.add_argument('--clock-name', help='Override clock')
    ap.add_argument('--reset-expr', help='Override reset')
    ap.add_argument('--prove-time', default='72h', help='Proof time')
    ap.add_argument('--proofgrid-jobs', type=int, default=180, help='Proofgrid jobs')
    ap.add_argument('--ports-json', help='Slang ports.json')
    ap.add_argument('--scoped-ast-json', help='Slang scoped AST')
    ap.add_argument('--whitebox', action='store_true', help='Also generate whitebox wrapper/bind/TCL')
    ap.add_argument('--prop-include-wb', default='properties_wb.sv', help='Whitebox include file')

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

    console.print(f'[cyan]📁 Scanning {src_root}[/cyan]')
    console.print(f'[cyan]ℹ Top: {args.top}, SVA: {sva_top}[/cyan]')

    include_basename = ensure_include_file_in_sva_dir(out_root, args.prop_include)

    user_filelist_path: Path | None = None

    if args.filelist:
        user_filelist_path = Path(args.filelist).resolve()
        if not user_filelist_path.is_file():
            raise SystemExit(f'ERROR: filelist not found: {user_filelist_path}')
        files_out: list[Path] = []
        incdirs_out: list[Path] = []
    else:
        pkg_files, rtl_files, missing_pkgs = build_filelist_for_top(
            rtl_root=src_root,
            top_name=args.top,
            include_dirs=user_incdirs,
        )

        if missing_pkgs:
            console.print('[yellow]⚠ Missing packages: ' + ', '.join(sorted(missing_pkgs)) + '[/yellow]')

        pkg_files = order_packages_by_dependency(pkg_files)
        files_out = pkg_files + rtl_files

        incdirs_out = []
        for d in user_incdirs:
            if d not in incdirs_out:
                incdirs_out.append(d)

    sva_dir = (out_root / 'sva').resolve()
    if sva_dir not in incdirs_out:
        incdirs_out.append(sva_dir)

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
        low = rst_name.lower()
        is_active_low = low.endswith('n') or low.endswith('_n') or low.endswith('ni') or low.endswith('_ni')
        rst_expr = f'!{rst_name}' if is_active_low else rst_name

    console.print(f'[green]✔ Clock/Reset: clk={clk_name}, reset_expr={rst_expr}[/green]')

    if ports_json and ports_json.is_file():
        sclk, srst, srst_expr, _ = detect_clk_rst_from_ports_json(ports_json)
        if sclk or srst:
            console.print(f'[magenta]ℹ SVA clk/rst: {sclk or "-"}/{srst or "-"}[/magenta]')

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
                include_basename,
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
            raise SystemExit(f"ERROR: module '{target_mod}' not found")
        prop_p, bind_p = emit_prop_and_bind_for_module(
            target_mod,
            target_src,
            out_root,
            include_basename,
            bind_scope,
            ports_json=ports_json,
            scoped_ast_json=scoped_ast_json,
        )
        if prop_p and bind_p:
            sva_paths.extend([prop_p, bind_p])

    # Whitebox: generate second wrapper/bind for whitebox properties
    wb_sva_paths: list[Path] = []
    if args.whitebox:
        wb_include_basename = ensure_include_file_in_sva_dir(out_root, args.prop_include_wb)
        target_mod = sva_top
        target_src = modules.get(target_mod)
        if target_src is not None:
            wb_dut_name = f'{target_mod}_wb'
            sva_dir = (out_root / 'sva').resolve()
            sva_dir.mkdir(parents=True, exist_ok=True)

            # Re-use the same port declarations but different include file
            wb_prop_path = sva_dir / f'{wb_dut_name}_prop.sv'
            wb_bind_path = sva_dir / f'{wb_dut_name}_bind.sv'

            # Build port_decls from ports_json or module header (reuse emit logic)
            known_tp: set[str] = set()
            if scoped_ast_json and scoped_ast_json.is_file():
                known_tp = load_known_type_params_from_scoped_ast(scoped_ast_json)

            wb_port_decls: list[str] = []
            wb_params_text = ''
            wb_package_imports: list[str] = []

            m_hdr = find_module_header(target_src.read_text(errors='ignore'), target_mod)
            if m_hdr:
                wb_params_text = m_hdr.group('params') or ''

            wb_package_imports = extract_package_imports_from_module(target_src, target_mod)
            if ports_json and ports_json.is_file():
                type_imports = extract_packages_from_port_types(ports_json)
                existing = set(wb_package_imports)
                for imp in type_imports:
                    if imp not in existing:
                        wb_package_imports.append(imp)
                        existing.add(imp)

            if ports_json and ports_json.is_file():
                wb_port_decls = port_decls_from_ports_json(ports_json, sva_top=target_mod, known_type_params=known_tp)
            elif m_hdr:
                port_body = m_hdr.group('port_body') or ''
                text_ports = strip_comments(port_body)
                buf2: list[str] = []
                dp, db = 0, 0
                ports_raw2: list[str] = []
                for ch in text_ports:
                    if ch == '(':
                        dp += 1
                    elif ch == ')':
                        dp = max(0, dp - 1)
                    elif ch == '[':
                        db += 1
                    elif ch == ']':
                        db = max(0, db - 1)
                    if ch == ',' and dp == 0 and db == 0:
                        t = ''.join(buf2).strip()
                        if t:
                            ports_raw2.append(t)
                        buf2 = []
                    else:
                        buf2.append(ch)
                t = ''.join(buf2).strip()
                if t:
                    ports_raw2.append(t)
                seen2: set[str] = set()
                for tok in ports_raw2:
                    tok = tok.strip()
                    if not tok:
                        continue
                    if not re.search(r'\b(input|output|inout)\b', tok):
                        tok = 'input ' + tok
                    decl = clean_decl_to_input(tok)
                    name = extract_last_identifier(decl)
                    if not name or name in seen2:
                        continue
                    seen2.add(name)
                    if not decl.startswith('input'):
                        decl = 'input ' + decl
                    wb_port_decls.append(decl)

            # Load internal signals and add them as ports to whitebox wrapper
            int_sig_path = out_root / f'{target_mod}_internal_signals.json'
            if int_sig_path.exists():
                try:
                    int_sigs = json.loads(int_sig_path.read_text())
                    if isinstance(int_sigs, list):
                        existing_names = set()
                        for d in wb_port_decls:
                            m_n = re.search(r'([A-Za-z_]\w*)\s*(\[[^\]]*\]\s*)*$', d.strip().rstrip(','))
                            if m_n:
                                existing_names.add(m_n.group(1))
                        added = 0
                        for sig in int_sigs:
                            if sig and sig not in existing_names:
                                wb_port_decls.append(f'input logic {sig}')
                                existing_names.add(sig)
                                added += 1
                        console.print(f'[cyan]ℹ Whitebox wrapper: added {added} internal signals as ports[/cyan]')
                except Exception as e:
                    console.print(f'[yellow]⚠ Failed to load internal signals: {e}[/yellow]')

            if wb_port_decls:
                wb_type_params_text = ''
                if ports_json and ports_json.is_file():
                    wb_type_params_text = build_type_parameters_from_ports(ports_json, target_mod, scoped_ast_json)

                wb_prop_sv = generate_prop_module_min(
                    wb_dut_name,
                    wb_params_text,
                    wb_port_decls,
                    wb_include_basename,
                    type_params_text=wb_type_params_text,
                    package_imports=wb_package_imports,
                )
                wb_bind_sv = generate_bind(wb_dut_name, wb_params_text, wb_port_decls, bind_scope or target_mod)

                wb_prop_path.write_text(wb_prop_sv)
                wb_bind_path.write_text(wb_bind_sv)
                wb_sva_paths = [wb_prop_path, wb_bind_path]
                console.print(f'[green]✔ Wrote whitebox wrapper: {wb_prop_path}[/green]')
                console.print(f'[green]✔ Wrote whitebox bind   : {wb_bind_path}[/green]')

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

    # Whitebox TCL generation
    if args.whitebox and wb_sva_paths:
        wb_tcl_path = out_tcl_path.parent / 'FPV_wb.tcl'
        if args.filelist:
            wb_final_files = list(wb_sva_paths)
        else:
            bb_names = {f'{sva_top}_prop.sv', f'{sva_top}_bind.sv'}
            wb_final_files = [f for f in files_out if f.name not in bb_names] + wb_sva_paths

        write_jasper_tcl(
            out_path=wb_tcl_path,
            output_dir=out_root,
            module_name=args.top,
            files=wb_final_files,
            incdirs=incdirs_out,
            defines=args.defines,
            clock_name=clk_name,
            reset_expr=rst_expr,
            prove_time=args.prove_time,
            proofgrid_jobs=args.proofgrid_jobs,
            lib_dirs=incdirs_out,
            lib_files=None,
            sva_module=f'{sva_top}_wb',
        )
        console.print(f'[green]✔ Wrote whitebox TCL: {wb_tcl_path}[/green]')

        if user_filelist_path is not None:
            overwrite_files_vc_for_user_filelist(
                vc_path=(out_root / 'files_wb.vc'),
                user_filelist=user_filelist_path,
                out_root=out_root,
                sva_files=wb_sva_paths,
                defines=args.defines,
            )

    console.print('[bold green]✔ FPV collateral generated[/bold green]')
    console.print(f'[bold green]✔ FPV dir: {out_root}[/bold green]')


if __name__ == '__main__':
    try:
        main()
    except Exception as e:
        console.print(f'[red]❌ Fatal Error:[/red] {e}')
        import traceback

        traceback.print_exc()
        sys.exit(1)
