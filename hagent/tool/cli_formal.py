#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
cli_formal.py — Formal verification pipeline driver (merged).

Stages (your requested behavior):

Stage 1: spec builder (optional, default ON)
Stage 2: property builder (optional, default ON)
Stage 3: wrapper/bind + FPV.tcl + files.vc (default ON)
Stage 4: run Jasper (only if --run-jg or --rerun-jg)
Stage 5: summarize results into results_summary.csv (after Jasper)
Stage 6: ALWAYS best-effort run private coverage summarizer (never fails run)
Stage 7: optional postcheck repair (only if --postcheck ...)
Stage 7b: optional bug detection cross-reference (only if --bug-detect)

Feedback loop policy:
  - We NEVER auto-run postcheck.
  - We ONLY run the LLM "advisor" if Jasper output indicates ERROR/CEX/FAIL/UNKNOWN.
  - Advisor prints a recommendation; user must re-run with --postcheck and choose max iters.
  - Jasper re-run after postcheck happens ONLY if user sets --postcheck-rerun-jg (and apply is enabled).

FIXED (Dec 2025):
  - Added package import extraction from module source and port types
  - Package-qualified types (ariane_pkg::alu_bypass_t) are now properly handled

FIXED (Jan 2026):
  - Private coverage summarizer CLI is now invoked with required --fpv-dir
    (and optional --jg-log/--results-csv/--out), instead of the invalid --html flag.
"""

from __future__ import annotations

import os
import re
import sys
import json
import shutil
import subprocess
import importlib.util
from pathlib import Path
from typing import Optional, List, Set, Dict, Any, Tuple

from rich.console import Console
from rich.panel import Panel
from rich.table import Table
from rich.progress import Progress, SpinnerColumn, TextColumn

from hagent.tool.utils.hdl_utils import load_sv_tree, build_filelist_for_top
from hagent.tool.utils.clk_rst_utils import detect_clk_rst_for_top

console = Console()

# ---------------------------
# Optional LLM advisor hook
# ---------------------------
try:
    from hagent.core.llm_wrap import LLM_wrap  # type: ignore
except Exception:
    LLM_wrap = None


# -----------------------------------------------------------------------------
# Pretty UI helpers
# -----------------------------------------------------------------------------
def banner():
    console.print(
        '\n[bold cyan]───────────────────────────────────────────────[/bold cyan]\n'
        '[bold yellow]        🚀 FORMAL TOOL (cli_formal.py) 🚀[/bold yellow]\n'
        '[bold cyan]───────────────────────────────────────────────[/bold cyan]\n'
        '[bold white]Spec → Props → FPV Collateral → Jasper → Feedback[/bold white]\n'
        '[bold cyan]───────────────────────────────────────────────[/bold cyan]\n'
    )


def ensure_dir(p: Path):
    p.mkdir(parents=True, exist_ok=True)


def repo_root() -> Path:
    return Path(__file__).resolve().parents[2]


def run_cmd(cmd: List[str], cwd: Optional[Path] = None):
    """
    Run a command using the *current* interpreter (works well under uv).
    Prints the command in a consistent "tool-like" way.
    """
    if cmd and cmd[0] in ('python', 'python3'):
        cmd = cmd[1:]
    cmd_str = ' '.join(cmd)
    console.print(f'[cyan]→[/cyan] [white]{sys.executable} {cmd_str}[/white]')
    subprocess.run([sys.executable, *cmd], check=True, cwd=cwd)


# -----------------------------------------------------------------------------
# File helpers
# -----------------------------------------------------------------------------
def _tail_text(p: Path, n_lines: int = 400) -> str:
    if not p.exists():
        return f'<missing: {p}>'
    try:
        lines = p.read_text(errors='ignore').splitlines()
        return '\n'.join(lines[-n_lines:])
    except Exception as e:
        return f'<failed to read {p}: {e}>'


def _read_text(p: Path, max_bytes: int = 300_000) -> str:
    if not p.exists():
        return f'<missing: {p}>'
    try:
        b = p.read_bytes()
        if len(b) > max_bytes:
            b = b[-max_bytes:]
        return b.decode('utf-8', errors='ignore')
    except Exception as e:
        return f'<failed to read {p}: {e}>'


# -----------------------------------------------------------------------------
# Private TCL writer loader (no fallback in public repo)
# -----------------------------------------------------------------------------
def _load_private_tcl_writer():
    try:
        from JG.fpv_tcl_writer import write_jasper_tcl  # type: ignore

        console.print('[green]✔ Using private JasperGold TCL writer[/green]')
        return write_jasper_tcl
    except Exception as e:
        console.print('[red]✖ ERROR: Private TCL writer not found.[/red]')
        console.print('    Expected: [bold]JG.fpv_tcl_writer.write_jasper_tcl[/bold]')
        console.print('    Make sure the private repo is on PYTHONPATH.')
        console.print(f'    Import error: {e}')
        raise SystemExit(1)


write_jasper_tcl = _load_private_tcl_writer()


# -----------------------------------------------------------------------------
# Regex for ANSI-style module headers (fallback if ports.json not available)
# -----------------------------------------------------------------------------
HEADER_RE = re.compile(
    r'\bmodule\s+(?P<name>\w+)\s*'
    r'(?:import\s+.*?;\s*)*'
    r'(?P<params>#\s*\((?P<param_body>.*?)\))?\s*'
    r'\(\s*(?P<port_body>.*?)\)\s*;',
    re.DOTALL | re.MULTILINE,
)

_COMMENT_RE = re.compile(r'//.*?$|/\*.*?\*/', re.DOTALL | re.MULTILINE)
_ID_RE = re.compile(r'\b([\w$]+)\b(?!.*\b[\w$]+\b)')


def strip_comments(text: str) -> str:
    return re.sub(_COMMENT_RE, '', text)


def clean_decl_to_input(decl: str) -> str:
    decl = re.sub(r'//.*?$', '', decl, flags=re.M)
    decl = re.sub(r'/\*.*?\*/', '', decl, flags=re.S)
    decl = re.sub(r'\s+', ' ', decl).strip().rstrip(',')
    decl = re.sub(r'\b(output|inout)\b', 'input', decl)
    decl = re.sub(r'\binput\b', 'input', decl)
    decl = re.sub(r'\b(wire|reg|logic|var|signed|unsigned)\b', '', decl)
    return re.sub(r'\s+', ' ', decl).strip()


def extract_last_identifier(token: str) -> Optional[str]:
    token = token.strip()
    if not token:
        return None
    token = re.split(r'//', token, maxsplit=1)[0]
    m = _ID_RE.search(token)
    return m.group(1) if m else None


def find_module_header(text: str, mod_name: str):
    for m in HEADER_RE.finditer(text):
        if m.group('name') == mod_name:
            return m
    return None


# -----------------------------------------------------------------------------
# NEW: Package import extraction functions
# -----------------------------------------------------------------------------
def extract_packages_from_port_types(ports_json: Path) -> List[str]:
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
        # Some Slang dumps prefix type strings with a numeric internal id.
        # Example: "3768648076360 branch_unit.fu_data_t".
        type_str = re.sub(r'^\d+\s+', '', type_str)
        # Match pkg::type patterns
        m = re.match(r'^([A-Za-z_]\w*)::(\w+)', type_str)
        if m:
            packages.add(m.group(1))

    return [f'import {pkg}::*;' for pkg in sorted(packages)]


def extract_package_imports_from_module(src_file: Path, mod_name: str) -> List[str]:
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
    import_pattern = re.compile(r'import\s+([A-Za-z_]\w*)::\*\s*;?')
    imports = import_pattern.findall(header)

    return [f'import {pkg}::*;' for pkg in imports]


# -----------------------------------------------------------------------------
# ports.json / scoped_ast.json support (preferred)
# -----------------------------------------------------------------------------
def _fix_logic_width_syntax(t: str) -> str:
    return re.sub(r'\b(logic|bit|byte|int|shortint|longint|integer)\s*\[', r'\1 [', t)


def load_known_type_params_from_scoped_ast(scoped_ast_json: Path) -> Set[str]:
    try:
        data = json.loads(scoped_ast_json.read_text())
        members = data.get('body', {}).get('members', [])
        tp: Set[str] = set()
        for m in members:
            if m.get('kind') == 'TypeParameter' and m.get('isPort'):
                n = m.get('name')
                if n:
                    tp.add(n)
        return tp
    except Exception as e:
        console.print(f'[yellow]⚠ Could not parse scoped_ast.json: {scoped_ast_json} ({e})[/yellow]')
        return set()


def build_params_text_from_scoped_ast(scoped_ast_json: Path) -> str:
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


def normalize_sv_type(type_str: str, sva_top: str, known_type_params: set[str]) -> str:
    """Normalize type strings - preserve package-qualified types and strip module. prefixes."""
    if not type_str or type_str.strip() in ('-', ''):
        return 'logic'

    t = _fix_logic_width_syntax(type_str.strip())

    # Slang sometimes prefixes type strings with a numeric internal id.
    # Example: "3768648076360 branch_unit.fu_data_t".
    t = re.sub(r'^\d+\s+', '', t).strip()

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


def port_decls_from_ports_json(ports_json: Path, sva_top: str, known_type_params: Set[str]) -> List[str]:
    data = json.loads(ports_json.read_text())
    decls: List[str] = []
    seen: Set[str] = set()

    for p in data:
        name = (p.get('name') or '').strip()
        if not name or name in seen:
            continue
        seen.add(name)
        t = normalize_sv_type(p.get('type') or 'logic', sva_top=sva_top, known_type_params=known_type_params)
        decls.append(f'input {t} {name}')
    return decls


# -----------------------------------------------------------------------------
# SVA wrapper + bind generation - FIXED with package imports
# -----------------------------------------------------------------------------
def generate_prop_module_min(
    dut_name: str, params_text: str, port_decls: List[str], include_file: str, package_imports: Optional[List[str]] = None
) -> str:
    """Generate property wrapper with package imports."""
    lines: List[str] = []

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

    # Add parameters if present
    if params_text:
        lines.append(f'{params_text}')

    # Port list
    port_lines = ',\n    '.join(port_decls)
    lines.append(f'(\n    {port_lines}\n);')

    # Module body
    lines.append('')
    lines.append('// Auto-generated property wrapper. Connect DUT ports as inputs.')
    if include_file:
        lines.append(f'`include "{include_file}"')
    lines.append('')
    lines.append('endmodule')
    lines.append('')

    return '\n'.join(lines)


def generate_bind(dut_name: str, params_text: str, port_decls: List[str], bind_target: Optional[str]) -> str:
    bind_scope = bind_target or dut_name
    sigs: List[str] = []

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


def emit_prop_and_bind_for_module(
    mod_name: str,
    src_file: Path,
    fpv_dir: Path,
    include_file: str,
    bind_scope: Optional[str],
    ports_json: Optional[Path],
    scoped_ast_json: Optional[Path],
):
    try:
        text = src_file.read_text(errors='ignore')
    except Exception as e:
        console.print(f'[red]⚠ Cannot read {src_file}: {e}[/red]')
        return None, None

    m = find_module_header(text, mod_name)
    params_text = ''
    port_decls: List[str] = []

    known_type_params: Set[str] = set()
    if scoped_ast_json and scoped_ast_json.is_file():
        known_type_params = load_known_type_params_from_scoped_ast(scoped_ast_json)

    if m:
        dut_name = m.group('name')
        params_text = m.group('params') or ''
        port_body = m.group('port_body') or ''
    else:
        dut_name = mod_name
        console.print(f'[yellow]⚠ Could not parse module header for {mod_name}; trying scoped_ast fallback.[/yellow]')
        params_text = build_params_text_from_scoped_ast(scoped_ast_json) if scoped_ast_json and scoped_ast_json.is_file() else ''
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

    if ports_json and ports_json.is_file():
        console.print(f'[cyan]✔ Using ports.json for wrapper ports:[/cyan] {ports_json}')
        port_decls = port_decls_from_ports_json(ports_json, sva_top=mod_name, known_type_params=known_type_params)
    else:
        if not m:
            console.print('[red]⚠ No ports.json and no parsable module header; cannot emit wrapper.[/red]')
            return None, None

        ports_raw: List[str] = []
        text_ports = strip_comments(port_body)
        buf: List[str] = []
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

        seen: Set[str] = set()
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

    sva_dir = fpv_dir / 'sva'
    ensure_dir(sva_dir)

    prop_path = sva_dir / f'{mod_name}_prop.sv'
    bind_path = sva_dir / f'{mod_name}_bind.sv'

    prop_sv = generate_prop_module_min(dut_name, params_text, port_decls, include_file, package_imports=package_imports)
    bind_sv = generate_bind(dut_name, params_text, port_decls, bind_scope)

    prop_path.write_text(prop_sv, encoding='utf-8')
    bind_path.write_text(bind_sv, encoding='utf-8')

    console.print(f'[green]✔[/green] Wrote wrapper: {prop_path}')
    console.print(f'[green]✔[/green] Wrote bind   : {bind_path}')
    return prop_path, bind_path


# -----------------------------------------------------------------------------
# Package ordering (auto mode only)
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
# files.vc overwrite (filelist mode only)
# -----------------------------------------------------------------------------
def overwrite_files_vc_for_user_filelist(
    vc_path: Path,
    user_filelist: Path,
    fpv_dir: Path,
    sva_files: List[Path],
    defines: Optional[List[str]] = None,
):
    vc_path = vc_path.resolve()
    user_filelist = user_filelist.resolve()
    sva_dir = (fpv_dir / 'sva').resolve()

    lines: List[str] = [
        '+libext+.v',
        '+libext+.sv',
        '+libext+.svh',
        '+librescan',
    ]

    for d in defines or []:
        d = (d or '').strip()
        if d:
            lines.append(f'+define+{d}')

    lines.append(f'+incdir+{sva_dir}')
    lines.append(f'-F {user_filelist}')

    for f in sva_files:
        lines.append(str(Path(f).resolve()))

    vc_path.write_text('\n'.join(lines) + '\n', encoding='utf-8')
    console.print(f'[green]✔[/green] Overwrote files.vc (filelist mode): [bold]{vc_path}[/bold]')


# -----------------------------------------------------------------------------
# Property deduplication (no LLM needed)
# -----------------------------------------------------------------------------
def _fix_sva_syntax(text: str) -> tuple[str, int]:
    """Fix common LLM SVA syntax errors in a properties.sv string.

    Fixes applied (no LLM needed):
    1. ``!(A or B)`` → ``!(A || B)`` — 'or' is a sequence op, not boolean-or.
    2. ``!(A and B)`` → ``!(A && B)`` — same issue with 'and'.

    Returns (fixed_text, n_fixes).
    """
    import re as _re

    n_fixes = 0

    # Replace `or` / `and` used inside !(…) boolean context.
    # Match !(...) where the content contains the keyword 'or'/'and' surrounded
    # by whitespace (not part of an identifier).
    def _replace_bool_ops(m: '_re.Match[str]') -> str:
        inner = m.group(1)
        new_inner, n = _re.subn(r'\bor\b', '||', inner)
        new_inner, n2 = _re.subn(r'\band\b', '&&', new_inner)
        return f'!({new_inner})'

    # Iteratively replace to handle nested parens; limit to 20 passes.
    for _ in range(20):
        new_text, n = re.subn(r'!\(([^()]*(?:\bor\b|\band\b)[^()]*)\)', _replace_bool_ops, text)
        if n == 0:
            break
        n_fixes += n
        text = new_text

    return text, n_fixes


def dedup_properties_sv(prop_path: Path) -> int:
    """Remove duplicate SVA property blocks and fix common syntax errors.

    Operations performed (no LLM needed):
    1. **Dedup**: duplicate ``property <name>`` blocks are removed (first wins).
    2. **Syntax fixes**: ``!(A or B)`` → ``!(A || B)``, ``!(A and B)`` → ``!(A && B)``.

    Returns the total number of changes (duplicates removed + lines fixed).
    """
    text = prop_path.read_text(encoding='utf-8')

    # Pass 1: fix SVA syntax errors
    text, n_syntax = _fix_sva_syntax(text)

    # Pass 2: remove duplicate property blocks
    lines = text.splitlines(keepends=True)
    seen_names: set[str] = set()
    out_lines: list[str] = []
    skip_until_endproperty = False
    skip_label = False
    n_dupes = 0
    i = 0

    while i < len(lines):
        line = lines[i]
        stripped = line.strip()

        # Detect start of a property block
        if stripped.startswith('property '):
            prop_name = stripped.split()[1].rstrip(';')
            if prop_name in seen_names:
                # Skip this property block and its label line
                skip_until_endproperty = True
                skip_label = True
                n_dupes += 1
                i += 1
                continue
            seen_names.add(prop_name)

        if skip_until_endproperty:
            if stripped == 'endproperty':
                skip_until_endproperty = False
                # Also drop the blank line after endproperty if present
                i += 1
                if i < len(lines) and lines[i].strip() == '':
                    i += 1
            else:
                i += 1
            continue

        if skip_label:
            # Skip the label line (assert_name: assert property(...);)
            skip_label = False
            i += 1
            continue

        out_lines.append(line)
        i += 1

    total_changes = n_syntax + n_dupes
    if total_changes:
        prop_path.write_text(''.join(out_lines), encoding='utf-8')

    return total_changes


# -----------------------------------------------------------------------------
# Jasper runner (only if asked)
# -----------------------------------------------------------------------------
def run_jasper(fpv_dir: Path, jasper_bin: str) -> Tuple[bool, Optional[int]]:
    """
    Runs Jasper and writes logs:
      jg.stdout.log / jg.stderr.log

    Returns:
      (success, exit_code)
    """
    fpv_dir = fpv_dir.resolve()
    if not (fpv_dir / 'FPV.tcl').exists():
        console.print(f'[red]✖ Missing FPV.tcl in {fpv_dir}[/red]')
        return False, None

    cmd = [jasper_bin, '-allow_unsupported_OS', '-tcl', 'FPV.tcl', '-batch']
    console.print(
        Panel.fit(
            f'[bold]Running Jasper[/bold]\n[cyan]cwd:[/cyan] {fpv_dir}\n[cyan]cmd:[/cyan] {" ".join(cmd)}',
            title='JasperGold',
            border_style='cyan',
        )
    )

    out_log = fpv_dir / 'jg.stdout.log'
    err_log = fpv_dir / 'jg.stderr.log'
    try:
        with out_log.open('w') as fo, err_log.open('w') as fe:
            subprocess.run(cmd, cwd=fpv_dir, stdout=fo, stderr=fe, check=True)
        console.print('[green]✔ Jasper finished successfully.[/green]')
        console.print(f'[green]✔[/green] Logs: {out_log} , {err_log}')
        return True, 0
    except subprocess.CalledProcessError as e:
        console.print(f'[red]✖ Jasper failed (exit={e.returncode}).[/red]')
        console.print(f'[red]✖[/red] Check logs: {out_log} , {err_log}')
        return False, e.returncode
    except FileNotFoundError:
        console.print(f'[red]✖ Jasper binary not found: {jasper_bin}[/red]')
        return False, None


# -----------------------------------------------------------------------------
# Jasper log parsing + results_summary.csv
# -----------------------------------------------------------------------------
def parse_jg_log_detailed(log_path: Path) -> Dict[str, Any]:
    if not log_path.exists():
        return {
            'properties_considered': 0,
            'assertions_total': 0,
            'covers_total': 0,
            'assertions': {},
            'covers': {},
        }

    text = log_path.read_text(errors='ignore')
    from collections import Counter

    line_re = re.compile(r'\[(\d+)\]\s+(.+?)\s{2,}(\w+)\s', re.M)
    rows = [(int(m.group(1)), m.group(2).rstrip(), m.group(3).lower()) for m in line_re.finditer(text)]

    result_dict: Dict[str, Any] = {
        'properties_considered': 0,
        'assertions_total': 0,
        'covers_total': 0,
        'assertions': {},
        'covers': {},
    }
    if not rows:
        return result_dict

    a_counts: Counter[str] = Counter()
    c_counts: Counter[str] = Counter()

    for _idx, full_name, res in rows:
        if (
            (':witness' in full_name)
            or (':precondition' in full_name)
            or ('.cover_' in full_name)
            or full_name.startswith('cover_')
        ):
            section = 'covers'
        elif (
            ('.assert_' in full_name)
            or full_name.startswith('assert_')
            or ('.assume_' in full_name)
            or full_name.startswith('assume_')
        ):
            section = 'assertions'
        else:
            section = 'assertions'

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
            key = res

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


def write_results_summary(fpv_dir: Path, jg_summary: Dict[str, Any]) -> Dict[str, int]:
    counts = {
        'PROVEN': int(jg_summary.get('assertions', {}).get('proven', 0)),
        'FAIL': int(jg_summary.get('assertions', {}).get('cex', 0)),
        'UNREACHABLE': int(jg_summary.get('covers', {}).get('unreachable', 0)),
        'COVER': int(jg_summary.get('covers', {}).get('covered', 0)),
        'UNKNOWN': int(jg_summary.get('assertions', {}).get('unknown', 0)) + int(jg_summary.get('covers', {}).get('unknown', 0)),
    }

    csv_path = fpv_dir / 'results_summary.csv'
    with csv_path.open('w', encoding='utf-8') as f:
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
    console.print(f'[green]✔[/green] Wrote {csv_path}')
    return counts


# -----------------------------------------------------------------------------
# Stage 6: ALWAYS best-effort private coverage summarizer (never fails)
# -----------------------------------------------------------------------------
def _find_private_repo_dir() -> Optional[Path]:
    env = os.environ.get('HAGENT_PRIVATE_DIR', '').strip()
    if env:
        p = Path(os.path.expanduser(env)).resolve()
        if p.exists():
            return p

    root = repo_root()
    cand1 = (root / 'hagent-private').resolve()
    cand2 = (root.parent / 'hagent-private').resolve()
    for c in (cand1, cand2):
        if c.exists():
            return c
    return None


def try_run_private_coverage_summarizer(fpv_dir: Path):
    """
    ALWAYS attempted after Jasper run. Best-effort only:
      - if private repo not found, prints a warning and continues
      - if formal_coverage.html not found, prints a warning and continues
      - never raises an exception

    IMPORTANT FIX:
      The private CLI requires --fpv-dir (NOT --html).
      We now pass:
        --fpv-dir <fpv_dir>
        [--jg-log <...>] [--results-csv <...>] [--out <...>]
    """
    fpv_dir = fpv_dir.resolve()

    # Keep the skip behavior: if Jasper didn't generate HTML, there's nothing to summarize.
    cov_html = fpv_dir / 'formal_coverage.html'
    if not cov_html.exists():
        console.print(f'[yellow]⚠ formal_coverage.html not found in {fpv_dir} (coverage summary skipped).[/yellow]')
        return

    priv = _find_private_repo_dir()
    if priv is None:
        console.print('[yellow]⚠ hagent-private not found (set HAGENT_PRIVATE_DIR to enable coverage summary).[/yellow]')
        return

    priv_script = priv / 'JG' / 'summarize_formal_coverage.py'
    if not priv_script.exists():
        console.print(f'[yellow]⚠ Private summarizer script missing: {priv_script}[/yellow]')
        return

    # Try import-path (fast path), but keep it best-effort.
    summarize_fn = None
    try:
        spec = importlib.util.spec_from_file_location('hagent_private_summarize_formal_coverage', priv_script)
        if spec and spec.loader:
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)
            import sys as _sys

            _sys.modules[spec.name] = module  # <-- IMPORTANT
            # Be tolerant to private API naming differences.
            summarize_fn = getattr(module, 'summarize_coverage_html', None) or getattr(
                module, 'summarize_formal_coverage_html', None
            )
    except Exception as e:
        console.print(f'[yellow]⚠ Private coverage summarizer import failed: {e}[/yellow]')

    if summarize_fn is not None:
        try:
            out_txt = summarize_fn(cov_html, console=console)
            console.print(f'[green]✔[/green] Coverage summary written to {out_txt}')
            return
        except Exception as e:
            console.print(f'[yellow]⚠ Private coverage summary (import path) failed: {e}[/yellow]')

    # Fallback CLI (FIXED): call with --fpv-dir and optional args.
    try:
        console.print('[cyan]→[/cyan] [white]Running private coverage summarizer CLI[/white]')

        jg_log_candidates = [
            fpv_dir / 'jgproject' / 'jg.log',
            fpv_dir / 'jg.stdout.log',
            fpv_dir / 'jg.stderr.log',
        ]
        jg_log = next((p for p in jg_log_candidates if p.exists()), None)

        results_csv = fpv_dir / 'results_summary.csv'
        out_txt = fpv_dir / 'formal_coverage_summary.txt'

        cmd = [sys.executable, str(priv_script), '--fpv-dir', str(fpv_dir)]
        if jg_log is not None:
            cmd += ['--jg-log', str(jg_log)]
        if results_csv.exists():
            cmd += ['--results-csv', str(results_csv)]
        cmd += ['--out', str(out_txt)]

        subprocess.run(cmd, cwd=priv_script.parent, check=True)
        console.print(f'[green]✔[/green] Coverage summarizer CLI completed. Output: {out_txt}')
    except Exception as e:
        console.print(f'[yellow]⚠ Coverage summarizer CLI failed: {e}[/yellow]')


# -----------------------------------------------------------------------------
# Advisor trigger: run ONLY if Jasper showed ERROR/CEX/FAIL/UNKNOWN
# -----------------------------------------------------------------------------
_ADVISOR_ERROR_PATTERNS = [
    r'\bERROR\b',
    r'\bfatal\b',
    r'\bFATAL\b',
    r'\bcex\b',
    r'\bCEX\b',
    r'\bfalsified\b',
    r'\bFAIL\b',
    r'\bunknown\b',
    r'\binconclusive\b',
]


def _looks_bad(stdout_text: str, stderr_text: str, counts: Dict[str, int], jasper_ok: bool) -> Tuple[bool, str]:
    """
    Conservative: if any of these indicate trouble, we trigger advisor.
    """
    if not jasper_ok:
        return True, 'Jasper exit non-zero'

    if counts.get('FAIL', 0) > 0:
        return True, f'FAIL={counts.get("FAIL", 0)}'
    if counts.get('UNKNOWN', 0) > 0:
        return True, f'UNKNOWN={counts.get("UNKNOWN", 0)}'

    joined = (stdout_text or '') + '\n' + (stderr_text or '')
    for pat in _ADVISOR_ERROR_PATTERNS:
        if re.search(pat, joined, flags=re.IGNORECASE):
            return True, f"matched '{pat}' in logs"

    return False, 'no error/cex/unknown detected'


def run_llm_advisor_if_needed(
    fpv_dir: Path,
    sva_top: str,
    scope_path: str,
    advisor_llm_conf: Optional[Path],
    jasper_ok: bool,
    jasper_exit: Optional[int],
    counts: Dict[str, int],
) -> None:
    """
    Runs only if trouble detected AND advisor config available.
    Never triggers postcheck automatically; prints recommendation only.
    """
    stdout_tail = _tail_text(fpv_dir / 'jg.stdout.log', 500)
    stderr_tail = _tail_text(fpv_dir / 'jg.stderr.log', 500)

    need, reason = _looks_bad(stdout_tail, stderr_tail, counts, jasper_ok)
    if not need:
        console.print('[green]✔ Advisor check: logs look clean (no CEX/ERROR/UNKNOWN).[/green]')
        return

    console.print(
        Panel.fit(
            f'[bold]Advisor triggered[/bold]\n'
            f'[cyan]Reason:[/cyan] {reason}\n'
            f'[cyan]Jasper ok:[/cyan] {jasper_ok}   [cyan]exit:[/cyan] {jasper_exit}\n'
            f'[cyan]Summary:[/cyan] FAIL={counts.get("FAIL", 0)} UNKNOWN={counts.get("UNKNOWN", 0)}',
            title='LLM ADVISOR',
            border_style='yellow',
        )
    )

    if LLM_wrap is None:
        console.print('[yellow]⚠ LLM_wrap not available; cannot run advisor. (Install/enable hagent.core.llm_wrap)[/yellow]')
        return

    if advisor_llm_conf is None or not advisor_llm_conf.exists():
        console.print('[yellow]⚠ Advisor LLM conf missing. Provide --advisor-llm-conf <yaml> to enable recommendations.[/yellow]')
        return

    payload = {
        'sva_top': sva_top,
        'scope_path': scope_path or '-',
        'jasper_ok': jasper_ok,
        'jasper_exit_code': jasper_exit,
        'results_summary_csv': _read_text(fpv_dir / 'results_summary.csv'),
        'jg_stdout_tail': stdout_tail,
        'jg_stderr_tail': stderr_tail,
        'jg_log_tail': _tail_text(fpv_dir / 'jgproject' / 'jg.log', 500),
        'coverage_summary_txt': _read_text(fpv_dir / 'formal_coverage_summary.txt'),
        'notes': (
            'Task: decide if user should run postcheck repair. '
            'Return a short recommendation and suggested command flags. '
            'DO NOT claim you ran postcheck.'
        ),
    }

    llm = LLM_wrap(
        name='default',
        conf_file=str(advisor_llm_conf),
        log_file='jg_advisor_llm.log',
    )

    try:
        res = llm.inference(payload, prompt_index='jg_advisor_recommendation', n=1)
    except Exception as e:
        console.print(f'[yellow]⚠ Advisor inference failed: {e}[/yellow]')
        return

    text = ''
    if isinstance(res, list) and res:
        text = str(res[0])
    else:
        text = str(res or '')

    text = text.strip()
    console.print(Panel.fit(text if text else '(empty advisor output)', title='Advisor Recommendation', border_style='yellow'))

    console.print(
        '[bold cyan]Next step (manual):[/bold cyan]\n'
        'If you agree with the recommendation, re-run with:\n'
        '  --postcheck --postcheck-llm-conf <...> --postcheck-max-iters <N> --postcheck-apply\n'
        'Optionally add:\n'
        '  --postcheck-rerun-jg --jasper-bin <...>\n'
        '[yellow]Note:[/yellow] postcheck will NOT run unless you explicitly request it.'
    )


# -----------------------------------------------------------------------------
# Post-check repair integration (opt-in; separate module)
# -----------------------------------------------------------------------------
def run_postcheck_if_requested(
    enabled: bool,
    fpv_dir: Path,
    sva_top: str,
    scope_path: str,
    llm_conf: Optional[Path],
    apply_patch: bool,
    rerun_jg_after: bool,
    jasper_bin: str,
    max_iters: int,
    tail_lines: int,
) -> int:
    if not enabled:
        return 0

    if llm_conf is None:
        console.print('[red]✖ --postcheck requested but --postcheck-llm-conf is missing.[/red]')
        return 2
    if not llm_conf.exists():
        console.print(f'[red]✖ --postcheck-llm-conf not found: {llm_conf}[/red]')
        return 2

    if rerun_jg_after and not apply_patch:
        console.print('[red]✖ --postcheck-rerun-jg requires --postcheck-apply (no point rerunning without applying fixes).[/red]')
        return 2

    try:
        from hagent.tool.jg_postcheck_repair import run_postcheck_repair  # type: ignore
    except Exception as e:
        console.print('[red]✖ Post-check module import failed.[/red]')
        console.print('    Expected: [bold]hagent.tool.jg_postcheck_repair[/bold] with run_postcheck_repair()')
        console.print(f'    Import error: {e}')
        return 2

    console.print(
        Panel.fit(
            f'[bold]Post-check requested[/bold]\n'
            f'[cyan]fpv_dir:[/cyan] {fpv_dir}\n'
            f'[cyan]sva_top:[/cyan] {sva_top}\n'
            f'[cyan]apply:[/cyan] {apply_patch}\n'
            f'[cyan]rerun_jg_after:[/cyan] {rerun_jg_after}\n'
            f'[cyan]max_iters:[/cyan] {max_iters}  [cyan]tail_lines:[/cyan] {tail_lines}',
            title='POSTCHECK',
            border_style='magenta',
        )
    )

    return int(
        run_postcheck_repair(
            fpv_dir=fpv_dir,
            sva_top=sva_top,
            scope_path=scope_path,
            llm_conf=llm_conf,
            apply=apply_patch,
            rerun_jg=rerun_jg_after,
            jasper_bin=jasper_bin,
            max_iters=max_iters,
            tail_lines=tail_lines,
        )
    )


# -----------------------------------------------------------------------------
# Bug detection cross-reference (auto-run after Jasper completes)
# -----------------------------------------------------------------------------
def run_bug_detect_if_requested(
    enabled: bool,
    fpv_dir: Path,
    sva_top: str,
    out_root: Path,
    label: str = 'Type:Bug',
    max_issues: int = 100,
    html_out: str = '',
    json_out: str = '',
) -> None:
    """
    Run cli_bug_detect.py against the build directory after FPV completes.
    Scans out_root.parent (the directory containing blackbox_* dirs) for FPV results,
    then cross-references open GitHub issues.
    """
    if not enabled:
        return
    console.print('\n[bold cyan]═══ Bug Detection Cross-Reference ═══[/bold cyan]')

    # The scan dir is the parent of out_root (contains blackbox_* siblings)
    scan_dir = out_root.parent

    cli_detect = Path(__file__).parent / 'cli_bug_detect.py'
    if not cli_detect.exists():
        console.print(f'[yellow]⚠ cli_bug_detect.py not found at {cli_detect}; skipping.[/yellow]')
        return

    effective_html = html_out if html_out else str(fpv_dir / f'{sva_top}_bug_detect.html')
    effective_json = json_out if json_out else str(fpv_dir / f'{sva_top}_bug_detect.json')

    cmd = [
        sys.executable,
        str(cli_detect),
        '--out-dir',
        str(scan_dir),
        '--label',
        label,
        '--max-issues',
        str(max_issues),
        '--html-out',
        effective_html,
        '--out-json',
        effective_json,
    ]
    console.print(f'[dim]→ {" ".join(cmd)}[/dim]')
    try:
        subprocess.run(cmd, check=False)
        console.print(f'[green]✔[/green] Bug report: {effective_html}')
    except Exception as exc:
        console.print(f'[yellow]⚠ Bug detection failed: {exc}[/yellow]')


# -----------------------------------------------------------------------------
# Whitebox wrapper/bind generation
# -----------------------------------------------------------------------------
def _emit_whitebox_wrapper(
    mod_name: str,
    src_file: Path,
    fpv_dir: Path,
    include_file: str,
    bind_scope: Optional[str],
    ports_json: Optional[Path],
    scoped_ast_json: Optional[Path],
) -> Tuple[Optional[Path], Optional[Path]]:
    """
    Generate a whitebox property wrapper and bind.
    The wrapper has IO ports AND internal signals as inputs.
    Internal signals are loaded from {mod_name}_internal_signals.json.
    The bind attaches it into the DUT scope, connecting both IO ports
    and internal signals so whitebox properties can reference them.
    """
    try:
        text = src_file.read_text(errors='ignore')
    except Exception as e:
        console.print(f'[red]⚠ Cannot read {src_file}: {e}[/red]')
        return None, None

    m = find_module_header(text, mod_name)
    params_text = ''
    port_decls: List[str] = []

    known_type_params: Set[str] = set()
    if scoped_ast_json and scoped_ast_json.is_file():
        known_type_params = load_known_type_params_from_scoped_ast(scoped_ast_json)

    if m:
        dut_name = m.group('name')
        params_text = m.group('params') or ''
    else:
        dut_name = mod_name
        params_text = build_params_text_from_scoped_ast(scoped_ast_json) if scoped_ast_json and scoped_ast_json.is_file() else ''

    # Package imports
    package_imports = extract_package_imports_from_module(src_file, mod_name)
    if ports_json and ports_json.is_file():
        type_imports = extract_packages_from_port_types(ports_json)
        existing = set(package_imports)
        for imp in type_imports:
            if imp not in existing:
                package_imports.append(imp)
                existing.add(imp)

    if ports_json and ports_json.is_file():
        port_decls = port_decls_from_ports_json(ports_json, sva_top=mod_name, known_type_params=known_type_params)
    else:
        if not m:
            console.print('[red]⚠ No ports.json and no parsable module header for whitebox wrapper.[/red]')
            return None, None
        port_body = m.group('port_body') or ''
        ports_raw: List[str] = []
        text_ports = strip_comments(port_body)
        buf: List[str] = []
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
        seen: Set[str] = set()
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
        console.print(f'[red]⚠ No ports found for whitebox wrapper of {dut_name}[/red]')
        return None, None

    # Load internal signals and add them as 'input logic' ports
    int_sig_path = fpv_dir / f'{mod_name}_internal_signals.json'
    if int_sig_path.exists():
        try:
            int_sigs = json.loads(int_sig_path.read_text())
            if isinstance(int_sigs, list):
                existing_names = set()
                for d in port_decls:
                    m_n = re.search(r'([A-Za-z_]\w*)\s*(\[[^\]]*\]\s*)*$', d.strip().rstrip(','))
                    if m_n:
                        existing_names.add(m_n.group(1))
                added = 0
                for sig in int_sigs:
                    if sig and sig not in existing_names:
                        port_decls.append(f'input logic {sig}')
                        existing_names.add(sig)
                        added += 1
                console.print(f'[cyan]ℹ Whitebox wrapper: added {added} internal signals as ports[/cyan]')
        except Exception as e:
            console.print(f'[yellow]⚠ Failed to load internal signals for whitebox wrapper: {e}[/yellow]')
    else:
        console.print(f'[yellow]⚠ No internal_signals.json found at {int_sig_path}; whitebox wrapper has IO ports only[/yellow]')

    sva_dir = fpv_dir / 'sva'
    ensure_dir(sva_dir)

    wb_name = f'{mod_name}_wb'
    prop_path = sva_dir / f'{wb_name}_prop.sv'
    bind_path = sva_dir / f'{wb_name}_bind.sv'

    prop_sv = generate_prop_module_min(f'{dut_name}_wb', params_text, port_decls, include_file, package_imports=package_imports)
    bind_sv = generate_bind(f'{dut_name}_wb', params_text, port_decls, bind_scope or dut_name)

    prop_path.write_text(prop_sv, encoding='utf-8')
    bind_path.write_text(bind_sv, encoding='utf-8')

    console.print(f'[green]✔[/green] Wrote whitebox wrapper: {prop_path}')
    console.print(f'[green]✔[/green] Wrote whitebox bind   : {bind_path}')
    return prop_path, bind_path


# -----------------------------------------------------------------------------
# Token counting helpers
# -----------------------------------------------------------------------------
def _collect_token_counts(fpv_dir: Path, sva_top: str, whitebox: bool) -> Dict[str, int]:
    """Collect token counts from *_tokens.json files written by spec/property builders."""
    counts: Dict[str, int] = {}
    candidates = [
        ('Spec (blackbox)', fpv_dir / f'{sva_top}_spec_tokens.json'),
        ('Property (blackbox)', fpv_dir / 'properties_tokens.json'),
    ]
    if whitebox:
        candidates += [
            ('Spec (whitebox)', fpv_dir / f'{sva_top}_spec_wb_tokens.json'),
            ('Property (whitebox)', fpv_dir / 'properties_wb_tokens.json'),
        ]
    for label, path in candidates:
        if path.exists():
            try:
                data = json.loads(path.read_text())
                counts[label] = int(data.get('total_tokens', 0))
            except Exception:
                counts[label] = 0
        else:
            counts[label] = 0
    return counts


def print_token_summary(fpv_dir: Path, sva_top: str, whitebox: bool) -> None:
    """Print a Rich table of token counts and write token_summary.json."""
    counts = _collect_token_counts(fpv_dir, sva_top, whitebox)
    total = sum(counts.values())

    table = Table(title='LLM Token Usage Summary', style='bold cyan')
    table.add_column('Stage', justify='left', style='white')
    table.add_column('Tokens', justify='right', style='bold')
    for label, n in counts.items():
        table.add_row(label, str(n))
    table.add_row('[bold]Total[/bold]', f'[bold green]{total}[/bold green]')
    console.print(table)

    summary = {**counts, 'total': total}
    summary_path = fpv_dir / 'token_summary.json'
    try:
        summary_path.write_text(json.dumps(summary, indent=2), encoding='utf-8')
        console.print(f'[green]✔[/green] Token summary: {summary_path}')
    except Exception as e:
        console.print(f'[yellow]⚠ Failed to write token summary: {e}[/yellow]')


# -----------------------------------------------------------------------------
# Main pipeline
# -----------------------------------------------------------------------------
def main() -> int:
    import argparse

    ap = argparse.ArgumentParser(description='Formal pipeline: spec → props → fpv collateral → Jasper → feedback')

    # Core I/O
    ap.add_argument('--rtl', help='RTL source directory. Required unless --rerun-jg or only postcheck.')
    ap.add_argument('--top', required=True, help='Design top module name (e.g. cva6).')
    ap.add_argument('--sva-top', help='Module to generate spec/properties/wrapper for (defaults to --top).')
    ap.add_argument(
        '--scope-path', default='', help='Hierarchical instance path to sva-top (used by spec builder + advisor context).'
    )
    ap.add_argument('--dir', required=True, help='Output directory root. Writes to: <dir>/fpv_<top>/')

    # Tool paths (spec builder)
    ap.add_argument('--slang', help='Path to slang binary/wrapper (required if running spec builder).')

    # Build context
    ap.add_argument('--filelist', help='Optional HDL filelist. In this mode, we reference it via -F in files.vc (not parsed).')
    ap.add_argument('-I', dest='include_dirs', action='append', default=[], help='Include directory (repeatable).')
    ap.add_argument('--defines', action='append', default=[], help='Define NAME or NAME=VAL (repeatable).')

    # Stage control
    ap.add_argument('--skip-spec', action='store_true', help='Skip spec generation stage.')
    ap.add_argument('--skip-props', action='store_true', help='Skip property generation stage.')
    ap.add_argument('--skip-fpv', action='store_true', help='Skip FPV collateral stage.')

    # Wrapper quality inputs (optional)
    ap.add_argument('--ports-json', help='Optional ports.json for wrapper port widths/types.')
    ap.add_argument('--scoped-ast-json', help='Optional scoped_ast.json for type params / fallback params.')

    # SVA wrapper options
    ap.add_argument('--bind-scope', help='Optional bind scope (hierarchical instance path).')
    ap.add_argument('--prop-include', default='properties.sv', help='File included inside *_prop.sv (default: "properties.sv").')

    # Jasper execution (ONLY if asked)
    ap.add_argument('--run-jg', action='store_true', help='Run Jasper after generation.')
    ap.add_argument('--rerun-jg', action='store_true', help='Rerun Jasper only (no regeneration).')
    ap.add_argument('--jasper-bin', default='jg', help='Jasper executable (default: jg).')

    # TCL knobs forwarded to private writer
    ap.add_argument('--clock-name', help='Override detected clock name.')
    ap.add_argument('--reset-expr', help='Override detected reset expression.')
    ap.add_argument('--prove-time', default='72h', help='Proof time limit (passed to private writer).')
    ap.add_argument('--proofgrid-jobs', type=int, default=180, help='Proofgrid jobs (passed to private writer).')

    # LLM prompt config overrides for spec/props
    ap.add_argument('--spec-llm-conf', help='Override spec_prompt.yaml path.')
    ap.add_argument('--prop-llm-conf', help='Override property_prompt.yaml path.')

    # Advisor config (used only when trouble detected)
    ap.add_argument(
        '--advisor-llm-conf', help='LLM prompt yaml for advisor recommendations (runs only on FAIL/UNKNOWN/ERROR/CEX).'
    )

    # Postcheck (optional, manual)
    ap.add_argument('--postcheck', action='store_true', help='Run post-check repair flow (opt-in).')
    ap.add_argument('--postcheck-llm-conf', help='Path to jg_post_repair_prompt.yaml')
    ap.add_argument('--postcheck-apply', action='store_true', help='Apply the patch produced by post-check repair.')
    ap.add_argument('--postcheck-rerun-jg', action='store_true', help='After applying patch, rerun Jasper (feedback loop).')
    ap.add_argument('--postcheck-max-iters', type=int, default=1)
    ap.add_argument('--postcheck-tail-lines', type=int, default=250)

    # Whitebox mode
    ap.add_argument('--whitebox', action='store_true', help='Generate both blackbox and whitebox SVA properties.')

    # Debug flag
    ap.add_argument('--debug', action='store_true', help='Enable debug output')

    # Bug detection (auto-run after Jasper completes)
    ap.add_argument(
        '--bug-detect',
        action='store_true',
        help='Run cli_bug_detect.py after FPV to cross-reference GitHub issues with FPV results.',
    )
    ap.add_argument('--bug-detect-label', default='Type:Bug', help='GitHub label filter (default: Type:Bug).')
    ap.add_argument('--bug-detect-max-issues', type=int, default=100, help='Max GitHub issues to fetch (default: 100).')
    ap.add_argument(
        '--bug-detect-html-out', default='', help='HTML output path for bug report (default: fpv_dir/<sva_top>_bug_detect.html).'
    )
    ap.add_argument(
        '--bug-detect-json-out', default='', help='JSON output path for bug report (default: fpv_dir/<sva_top>_bug_detect.json).'
    )

    # CEX classification (Stage 7c) — auto-classifies FAILs after Jasper
    ap.add_argument(
        '--cex-classify',
        action='store_true',
        help='Stage 7c: classify each CEX as SPEC_ERROR / BEHAVIORAL_CANDIDATE / CONFLICT / UNCERTAIN using heuristics.',
    )
    ap.add_argument(
        '--cex-classify-llm-conf',
        default='',
        help='LLM config YAML for Stage 7c deep analysis of BEHAVIORAL_CANDIDATE entries (optional; requires API key).',
    )

    # Bug-targeted SVA generation (Stage 3.5) — inject GitHub-issue-targeted assertions before Jasper
    ap.add_argument(
        '--bug-target-gen',
        action='store_true',
        help='Stage 3.5: fetch GitHub issues and generate targeted SVA assertions appended to properties.sv before Jasper.',
    )
    ap.add_argument(
        '--bug-target-gen-llm-conf',
        default='',
        help='LLM config YAML for Stage 3.5 bug-targeted assertion generation (required with --bug-target-gen).',
    )
    ap.add_argument(
        '--bug-target-gen-label', default='Type:Bug',
        help='GitHub label filter for bug-targeted gen (default: Type:Bug).',
    )
    ap.add_argument(
        '--bug-target-gen-max-issues', type=int, default=30,
        help='Max GitHub issues to fetch for bug-targeted gen (default: 30).',
    )

    args = ap.parse_args()

    banner()

    out_root = Path(os.path.expanduser(args.dir)).resolve()
    fpv_dir = out_root / f'fpv_{args.top}'
    ensure_dir(fpv_dir)
    ensure_dir(fpv_dir / 'sva')

    sva_top = args.sva_top or args.top

    console.print(
        Panel.fit(
            f'[bold]Setup[/bold]\n'
            f'[cyan]design_top:[/cyan] {args.top}\n'
            f'[cyan]sva_top   :[/cyan] {sva_top}\n'
            f'[cyan]fpv_dir   :[/cyan] {fpv_dir}\n'
            f'[cyan]mode      :[/cyan] {"rerun-only" if args.rerun_jg else "pipeline"}',
            border_style='green',
        )
    )

    # -------------------------
    # RERUN-ONLY (no regeneration)
    # -------------------------
    if args.rerun_jg:
        jasper_ok, jasper_exit = run_jasper(fpv_dir=fpv_dir, jasper_bin=args.jasper_bin)

        # Stage 5 summary (always after Jasper attempt)
        jg_log = fpv_dir / 'jgproject' / 'jg.log'
        jg_summary = parse_jg_log_detailed(jg_log)
        counts = write_results_summary(fpv_dir, jg_summary)

        # Stage 6 coverage summary (ALWAYS best-effort)
        try_run_private_coverage_summarizer(fpv_dir)

        # Advisor (only if trouble)
        advisor_conf = Path(os.path.expanduser(args.advisor_llm_conf)).resolve() if args.advisor_llm_conf else None
        run_llm_advisor_if_needed(
            fpv_dir=fpv_dir,
            sva_top=sva_top,
            scope_path=args.scope_path or '',
            advisor_llm_conf=advisor_conf,
            jasper_ok=jasper_ok,
            jasper_exit=jasper_exit,
            counts=counts,
        )

        # Stage 8: Bug detection (optional, auto-run after Jasper)
        run_bug_detect_if_requested(
            enabled=args.bug_detect,
            fpv_dir=fpv_dir,
            sva_top=sva_top,
            out_root=out_root,
            label=args.bug_detect_label,
            max_issues=args.bug_detect_max_issues,
            html_out=args.bug_detect_html_out,
            json_out=args.bug_detect_json_out,
        )

        # Postcheck if explicitly requested (manual). Rerun only after postcheck + only if asked.
        rc_post = run_postcheck_if_requested(
            enabled=args.postcheck,
            fpv_dir=fpv_dir,
            sva_top=sva_top,
            scope_path=args.scope_path or '',
            llm_conf=Path(os.path.expanduser(args.postcheck_llm_conf)).resolve() if args.postcheck_llm_conf else None,
            apply_patch=args.postcheck_apply,
            rerun_jg_after=args.postcheck_rerun_jg,
            jasper_bin=args.jasper_bin,
            max_iters=args.postcheck_max_iters,
            tail_lines=args.postcheck_tail_lines,
        )

        # Token summary (if any generation was done previously)
        print_token_summary(fpv_dir, sva_top, whitebox=args.whitebox)

        # Return nonzero if postcheck failed, else reflect Jasper success
        if rc_post != 0:
            return rc_post
        return 0 if jasper_ok else 2

    # -------------------------
    # PIPELINE requires RTL for generation stages
    # -------------------------
    if (not args.skip_spec) or (not args.skip_props) or (not args.skip_fpv):
        if not args.rtl:
            raise SystemExit('ERROR: --rtl is required for pipeline generation stages. Use --rerun-jg for rerun-only.')
        rtl_dir = Path(os.path.expanduser(args.rtl)).resolve()
        if not rtl_dir.is_dir():
            raise SystemExit(f'ERROR: RTL directory not found: {rtl_dir}')
    else:
        rtl_dir = None  # type: ignore

    root = repo_root()
    default_spec_yaml = root / 'hagent' / 'step' / 'sva_gen' / 'spec_prompt.yaml'
    default_prop_yaml = root / 'hagent' / 'step' / 'sva_gen' / 'property_prompt.yaml'
    spec_yaml = Path(os.path.expanduser(args.spec_llm_conf)).resolve() if args.spec_llm_conf else default_spec_yaml
    prop_yaml = Path(os.path.expanduser(args.prop_llm_conf)).resolve() if args.prop_llm_conf else default_prop_yaml

    if not args.skip_spec:
        if not args.slang:
            raise SystemExit('ERROR: --slang required when running spec builder (omit with --skip-spec).')
        if not spec_yaml.exists():
            raise SystemExit(f'ERROR: spec LLM config not found: {spec_yaml}')
    if not args.skip_props:
        if not prop_yaml.exists():
            raise SystemExit(f'ERROR: property LLM config not found: {prop_yaml}')

    ports_json = Path(os.path.expanduser(args.ports_json)).resolve() if args.ports_json else None
    scoped_ast_json = Path(os.path.expanduser(args.scoped_ast_json)).resolve() if args.scoped_ast_json else None

    include_dirs = [Path(os.path.expanduser(p)).resolve() for p in args.include_dirs]
    user_filelist = Path(os.path.expanduser(args.filelist)).resolve() if args.filelist else None
    if user_filelist and not user_filelist.is_file():
        raise SystemExit(f'ERROR: --filelist not found: {user_filelist}')

    steps: List[Tuple[str, callable]] = []

    # Stage 1: spec
    def _step_spec():
        cmd = [
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
            '--design-top',
            args.top,
            '--dir',
            str(fpv_dir),
            '--llm-config',
            str(spec_yaml),
        ]
        if args.scope_path:
            cmd += ['--scope-path', args.scope_path]
        if user_filelist:
            cmd += ['--filelist', str(user_filelist)]
        for inc in include_dirs:
            cmd += ['--include', str(inc)]
        for d in args.defines or []:
            cmd += ['--defines', d]
        run_cmd(cmd)

    if not args.skip_spec:
        steps.append((f'🔧 Spec generation (module={sva_top})', _step_spec))

    # Stage 1b: spec whitebox (only if --whitebox)
    def _step_spec_wb():
        cmd = [
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
            '--design-top',
            args.top,
            '--dir',
            str(fpv_dir),
            '--llm-config',
            str(spec_yaml),
            '--whitebox',
        ]
        if args.scope_path:
            cmd += ['--scope-path', args.scope_path]
        if user_filelist:
            cmd += ['--filelist', str(user_filelist)]
        for inc in include_dirs:
            cmd += ['--include', str(inc)]
        for d in args.defines or []:
            cmd += ['--defines', d]
        run_cmd(cmd)

    if not args.skip_spec and args.whitebox:
        steps.append((f'🔧 Spec generation WHITEBOX (module={sva_top})', _step_spec_wb))

    # Stage 2: props
    def _step_props():
        spec_md = fpv_dir / f'{sva_top}_spec.md'
        spec_csv = fpv_dir / f'{sva_top}_spec.csv'
        if not spec_md.exists() or not spec_csv.exists():
            raise SystemExit(f'ERROR: Missing spec outputs: {spec_md} / {spec_csv}')

        cmd = [
            'python3',
            '-m',
            'hagent.tool.tests.cli_property_builder',
            '--spec-md',
            str(spec_md),
            '--csv',
            str(spec_csv),
            '--rtl',
            str(rtl_dir),
            '--dir',
            str(fpv_dir),
            '--llm-config',
            str(prop_yaml),
            '--design-top',
            args.top,
        ]
        run_cmd(cmd)

        prop_src = fpv_dir / 'properties.sv'
        if not prop_src.exists():
            raise SystemExit('ERROR: properties.sv not found after property builder.')

        # Deduplicate + fix SVA syntax errors (no LLM needed)
        n_fixed = dedup_properties_sv(prop_src)
        if n_fixed:
            console.print(f'[yellow]⚠ Auto-fixed {n_fixed} issue(s) in properties.sv (dupes/syntax)[/yellow]')
        else:
            console.print('[green]✔[/green] No duplicate/syntax issues in properties.sv.')

        prop_dst = fpv_dir / 'sva' / 'properties.sv'
        if prop_dst.exists():
            prop_dst.unlink()
        shutil.move(str(prop_src), str(prop_dst))
        console.print('[green]✔[/green] Moved properties.sv → sva/')

    if not args.skip_props:
        steps.append((f'🔒 Property generation (module={sva_top})', _step_props))

    # Stage 2b: props whitebox (only if --whitebox)
    def _step_props_wb():
        spec_md_wb = fpv_dir / f'{sva_top}_spec_wb.md'
        spec_csv_wb = fpv_dir / f'{sva_top}_spec_wb.csv'
        if not spec_md_wb.exists() or not spec_csv_wb.exists():
            raise SystemExit(f'ERROR: Missing whitebox spec outputs: {spec_md_wb} / {spec_csv_wb}')

        int_sig_json = fpv_dir / f'{sva_top}_internal_signals.json'
        cmd = [
            'python3',
            '-m',
            'hagent.tool.tests.cli_property_builder',
            '--spec-md',
            str(spec_md_wb),
            '--csv',
            str(spec_csv_wb),
            '--rtl',
            str(rtl_dir),
            '--dir',
            str(fpv_dir),
            '--llm-config',
            str(prop_yaml),
            '--design-top',
            args.top,
            '--whitebox',
        ]
        if int_sig_json.exists():
            cmd += ['--internal-signals-json', str(int_sig_json)]
        run_cmd(cmd)

        prop_src_wb = fpv_dir / 'properties_wb.sv'
        if not prop_src_wb.exists():
            raise SystemExit('ERROR: properties_wb.sv not found after whitebox property builder.')

        # Deduplicate + fix SVA syntax errors in whitebox props (no LLM needed)
        n_removed_wb = dedup_properties_sv(prop_src_wb)
        if n_removed_wb:
            console.print(f'[yellow]⚠ Auto-fixed {n_removed_wb} issue(s) in properties_wb.sv (dupes/syntax)[/yellow]')

        prop_dst_wb = fpv_dir / 'sva' / 'properties_wb.sv'
        if prop_dst_wb.exists():
            prop_dst_wb.unlink()
        shutil.move(str(prop_src_wb), str(prop_dst_wb))
        console.print('[green]✔[/green] Moved properties_wb.sv → sva/')

    if not args.skip_props and args.whitebox:
        steps.append((f'🔒 Property generation WHITEBOX (module={sva_top})', _step_props_wb))

    # Stage 3.5: bug-targeted SVA generation (inject targeted assertions from GitHub issues)
    def _step_bug_target_gen():
        from hagent.tool.cli_cex_classify import run_bug_target_gen  # type: ignore

        btg_llm_conf_path = Path(args.bug_target_gen_llm_conf).resolve() if args.bug_target_gen_llm_conf else None
        if btg_llm_conf_path is None or not btg_llm_conf_path.exists():
            console.print('[yellow]⚠ --bug-target-gen-llm-conf not set or not found; skipping Stage 3.5.[/yellow]')
            return
        n = run_bug_target_gen(
            fpv_dir=fpv_dir,
            sva_top=sva_top,
            llm_conf=btg_llm_conf_path,
            label=args.bug_target_gen_label,
            max_issues=args.bug_target_gen_max_issues,
        )
        console.print(f'[green]✔[/green] Stage 3.5: {n} bug-targeted assertions appended to properties.sv')

    if args.bug_target_gen:
        steps.append((f'🎯 Bug-targeted SVA generation (module={sva_top})', _step_bug_target_gen))

    # Stage 3: fpv collateral
    def _step_fpv():
        pj = ports_json
        saj = scoped_ast_json
        if pj is None:
            cand = fpv_dir / f'{sva_top}_ports.json'
            if cand.exists():
                pj = cand
            else:
                cand2 = fpv_dir / 'ports.json'
                if cand2.exists():
                    pj = cand2
        if saj is None:
            cand = fpv_dir / f'{sva_top}_scoped_ast.json'
            if cand.exists():
                saj = cand
            else:
                cand2 = fpv_dir / 'scoped_ast.json'
                if cand2.exists():
                    saj = cand2

        include_basename = Path(args.prop_include).name
        inc_path = Path(os.path.expanduser(args.prop_include)).resolve()
        if inc_path.exists() and inc_path.is_file():
            dst = fpv_dir / 'sva' / include_basename
            if dst.resolve() != inc_path:
                shutil.copy2(inc_path, dst)
                console.print(f'[green]✔[/green] Copied prop-include → {dst}')

        all_files = load_sv_tree(rtl_dir)
        modules: Dict[str, Path] = {}
        for path, sv in all_files.items():
            for unit in sv.declared_units():
                modules.setdefault(unit, path)

        target_src = modules.get(sva_top)
        if target_src is None:
            raise SystemExit(f"ERROR: module '{sva_top}' not found under RTL root: {rtl_dir}")

        clk_name, rst_name, rst_expr = detect_clk_rst_for_top(rtl_dir, args.top)
        if args.clock_name:
            clk_name = args.clock_name
        if args.reset_expr:
            rst_expr = args.reset_expr
        if not rst_expr and rst_name:
            rst_expr = f'!{rst_name}'
        console.print(f'[green]✔[/green] Clock/Reset: clk={clk_name}, reset_expr={rst_expr}')

        prop_p, bind_p = emit_prop_and_bind_for_module(
            mod_name=sva_top,
            src_file=target_src,
            fpv_dir=fpv_dir,
            include_file=include_basename,
            bind_scope=args.bind_scope,
            ports_json=pj,
            scoped_ast_json=saj,
        )

        sva_paths: List[Path] = []
        if prop_p and bind_p:
            sva_paths.extend([prop_p, bind_p])

        # Whitebox: generate second wrapper/bind for whitebox properties
        if args.whitebox:
            wb_include = 'properties_wb.sv'
            wb_prop_path, wb_bind_path = _emit_whitebox_wrapper(
                mod_name=sva_top,
                src_file=target_src,
                fpv_dir=fpv_dir,
                include_file=wb_include,
                bind_scope=args.bind_scope,
                ports_json=pj,
                scoped_ast_json=saj,
            )
            if wb_prop_path and wb_bind_path:
                sva_paths.extend([wb_prop_path, wb_bind_path])

        if user_filelist:
            final_files = list(sva_paths)
            incdirs_out: List[Path] = []
        else:
            pkg_files, rtl_files, missing_pkgs = build_filelist_for_top(
                rtl_root=rtl_dir,
                top_name=args.top,
                include_dirs=include_dirs,
            )
            if missing_pkgs:
                console.print('[yellow]⚠ WARNING: Missing packages:[/yellow] ' + ', '.join(sorted(missing_pkgs)))
            pkg_files = order_packages_by_dependency(pkg_files)
            final_files = list(pkg_files) + list(rtl_files) + list(sva_paths)
            incdirs_out = list(dict.fromkeys(include_dirs))

        write_jasper_tcl(
            out_path=(fpv_dir / 'FPV.tcl'),
            output_dir=fpv_dir,
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

        if user_filelist:
            overwrite_files_vc_for_user_filelist(
                vc_path=(fpv_dir / 'files.vc'),
                user_filelist=user_filelist,
                fpv_dir=fpv_dir,
                sva_files=sva_paths,
                defines=args.defines,
            )

        # Generate whitebox TCL (separate FPV_wb.tcl) if whitebox enabled
        if args.whitebox:
            wb_sva_paths = [p for p in sva_paths if '_wb' in p.name]
            wb_final_files = list(final_files) if not user_filelist else list(wb_sva_paths)
            if not user_filelist:
                # Replace blackbox SVA files with whitebox ones in the file list
                bb_names = {f'{sva_top}_prop.sv', f'{sva_top}_bind.sv'}
                wb_final_files = [f for f in final_files if f.name not in bb_names] + wb_sva_paths

            write_jasper_tcl(
                out_path=(fpv_dir / 'FPV_wb.tcl'),
                output_dir=fpv_dir,
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
            console.print(f'[green]✔[/green] Wrote whitebox TCL: {fpv_dir / "FPV_wb.tcl"}')

            if user_filelist:
                overwrite_files_vc_for_user_filelist(
                    vc_path=(fpv_dir / 'files_wb.vc'),
                    user_filelist=user_filelist,
                    fpv_dir=fpv_dir,
                    sva_files=wb_sva_paths,
                    defines=args.defines,
                )

        console.print('[bold green]✔ FPV collateral generated[/bold green]')
        console.print(f'[green]✔[/green] FPV dir: {fpv_dir}')

    if not args.skip_fpv:
        steps.append(('🧩 FPV collateral (wrapper/bind + FPV.tcl/files.vc)', _step_fpv))

    if steps:
        with Progress(SpinnerColumn(), TextColumn('[progress.description]{task.description}')) as progress:
            for i, (msg, fn) in enumerate(steps, 1):
                progress.add_task(description=f'[cyan]{msg}...', total=None)
                console.print(f'\n[bold cyan][{i}/{len(steps)}][/bold cyan] {msg}')
                fn()
                console.print(f'[green]✔[/green] {msg} completed.\n')

    # Stage 4: Jasper only if asked
    jasper_ok = True
    jasper_exit: Optional[int] = 0
    counts: Dict[str, int] = {'PROVEN': 0, 'FAIL': 0, 'UNKNOWN': 0, 'COVER': 0, 'UNREACHABLE': 0}

    if args.run_jg:
        jasper_ok, jasper_exit = run_jasper(fpv_dir=fpv_dir, jasper_bin=args.jasper_bin)

        # Stage 5 summary (always after Jasper attempt)
        jg_log = fpv_dir / 'jgproject' / 'jg.log'
        jg_summary = parse_jg_log_detailed(jg_log)
        counts = write_results_summary(fpv_dir, jg_summary)

        # Stage 6 coverage summary (ALWAYS best-effort)
        try_run_private_coverage_summarizer(fpv_dir)

        # Advisor (only if trouble; AFTER summary + coverage)
        advisor_conf = Path(os.path.expanduser(args.advisor_llm_conf)).resolve() if args.advisor_llm_conf else None
        run_llm_advisor_if_needed(
            fpv_dir=fpv_dir,
            sva_top=sva_top,
            scope_path=args.scope_path or '',
            advisor_llm_conf=advisor_conf,
            jasper_ok=jasper_ok,
            jasper_exit=jasper_exit,
            counts=counts,
        )

    # Stage 7b: Bug detection (optional, auto-run after Jasper + summary)
    if args.run_jg:
        run_bug_detect_if_requested(
            enabled=args.bug_detect,
            fpv_dir=fpv_dir,
            sva_top=sva_top,
            out_root=out_root,
            label=args.bug_detect_label,
            max_issues=args.bug_detect_max_issues,
            html_out=args.bug_detect_html_out,
            json_out=args.bug_detect_json_out,
        )

    # Stage 7c: CEX classification (heuristic + optional LLM — runs whenever Jasper was run and FAILs > 0)
    if (args.run_jg or args.rerun_jg) and (args.cex_classify or counts.get('FAIL', 0) > 0 and args.cex_classify):
        try:
            from hagent.tool.cli_cex_classify import run_cex_classify  # type: ignore

            cex_llm_conf_path = (
                Path(os.path.expanduser(args.cex_classify_llm_conf)).resolve()
                if args.cex_classify_llm_conf
                else None
            )
            run_cex_classify(
                fpv_dir=fpv_dir,
                sva_top=sva_top,
                llm_conf=cex_llm_conf_path,
                html_out=fpv_dir / f'{sva_top}_cex_classify.html',
                json_out=fpv_dir / f'{sva_top}_cex_classify.json',
            )
        except Exception as exc:
            console.print(f'[yellow]⚠ Stage 7c CEX classification failed: {exc}[/yellow]')

    # Stage 7: Postcheck ONLY if user explicitly requested (manual feedback loop)
    rc_post = run_postcheck_if_requested(
        enabled=args.postcheck,
        fpv_dir=fpv_dir,
        sva_top=sva_top,
        scope_path=args.scope_path or '',
        llm_conf=Path(os.path.expanduser(args.postcheck_llm_conf)).resolve() if args.postcheck_llm_conf else None,
        apply_patch=args.postcheck_apply,
        rerun_jg_after=args.postcheck_rerun_jg,
        jasper_bin=args.jasper_bin,
        max_iters=args.postcheck_max_iters,
        tail_lines=args.postcheck_tail_lines,
    )
    if rc_post != 0:
        return rc_post

    # Token summary (always print after generation stages)
    print_token_summary(fpv_dir, sva_top, whitebox=args.whitebox)

    # Final status:
    # - If Jasper wasn't run, success is based on generation stages.
    # - If Jasper was run and failed, return nonzero (but we still produced summary/coverage/advice).
    if args.run_jg and not jasper_ok:
        return 2

    console.print(
        Panel.fit(
            f'[bold green]DONE[/bold green]\n'
            f'[cyan]fpv_dir:[/cyan] {fpv_dir}\n'
            f'[cyan]ran_jasper:[/cyan] {bool(args.run_jg or args.rerun_jg)}\n'
            f'[cyan]postcheck:[/cyan] {bool(args.postcheck)}\n'
            f'[cyan]whitebox:[/cyan] {bool(args.whitebox)}',
            border_style='green',
        )
    )
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        console.print('\n[yellow]Interrupted.[/yellow]')
        raise SystemExit(130)
