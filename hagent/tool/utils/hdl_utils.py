"""
hdl_utils.py

Small helper library for dealing with SystemVerilog / Verilog dependencies.

Features:
  - Recursively scan an RTL tree for .sv/.svh/.v files.
  - Index all 'package <name>;' declarations.
  - Find where a package is used (import pkg::*;  pkg::symbol).
  - Resolve package dependencies for a given set of RTL files.
  - Build an ordered list: all package files first, then other RTL files.

Notes:
  - No project-specific hardcoded paths.
  - Special handling for the common pattern:
        package riscv;
        file name: riscv_pkg.sv  or riscv.sv
    so that references to `riscv::...` are resolved even if the file is
    named riscv_pkg.sv.
"""

from __future__ import annotations

import re
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable, Dict, List, Set, Tuple


# ---------------------------------------------------------------------------
# Regexes for SystemVerilog parsing (light-weight, not a full parser)
# ---------------------------------------------------------------------------

# package <name>;
RE_PACKAGE_DECL = re.compile(r'(?m)^\s*package\s+([a-zA-Z_]\w*)\s*;')

# import pkg::*;
RE_IMPORT_PKG_STAR = re.compile(r'(?m)^\s*import\s+([a-zA-Z_]\w*)::\*;')

# Any occurrence of pkg::symbol
RE_PKG_SCOPE_USE = re.compile(r'\b([a-zA-Z_]\w*)::[a-zA-Z_]\w*')

# module / interface / program / package names (for optional top detection)
RE_TOP_LIKE = re.compile(r'(?m)^\s*(module|interface|program|package)\s+([a-zA-Z_]\w*)\b')


SV_EXTENSIONS = {'.sv', '.svh', '.v'}


@dataclass(frozen=True)
class SvFile:
    """Represents a SystemVerilog file and some cached info."""

    path: Path
    text: str

    def declared_packages(self) -> Set[str]:
        return set(RE_PACKAGE_DECL.findall(self.text))

    def used_packages(self) -> Set[str]:
        pkgs: Set[str] = set()
        pkgs.update(RE_IMPORT_PKG_STAR.findall(self.text))
        pkgs.update(RE_PKG_SCOPE_USE.findall(self.text))
        return pkgs

    def declared_units(self) -> Set[str]:
        """All module/interface/program/package names declared in this file."""
        return {m.group(2) for m in RE_TOP_LIKE.finditer(self.text)}


# ---------------------------------------------------------------------------
# Basic file discovery
# ---------------------------------------------------------------------------


def iter_sv_files(root: Path) -> Iterable[Path]:
    """
    Recursively yield all SystemVerilog-ish files under `root`.
    """
    for p in root.rglob('*'):
        if p.is_file() and p.suffix in SV_EXTENSIONS:
            yield p


def load_sv_tree(root: Path) -> Dict[Path, SvFile]:
    """
    Load all SV files under `root` into a dict {path: SvFile}.
    """
    root = root.resolve()
    files: Dict[Path, SvFile] = {}
    for p in iter_sv_files(root):
        try:
            txt = p.read_text(encoding='utf-8', errors='ignore')
        except OSError:
            continue
        files[p] = SvFile(path=p, text=txt)
    return files


# ---------------------------------------------------------------------------
# Package indexing and resolution
# ---------------------------------------------------------------------------


def index_packages(files: Dict[Path, SvFile]) -> Dict[str, Path]:
    """
    Map package name -> file containing 'package <name>;'

    If multiple files declare the same package (shouldn't normally happen),
    the shortest path (lexicographically) wins to keep things deterministic.
    """
    pkg_to_file: Dict[str, Path] = {}
    for path, sv in files.items():
        for pkg in sv.declared_packages():
            old = pkg_to_file.get(pkg)
            if old is None or str(path) < str(old):
                pkg_to_file[pkg] = path
    return pkg_to_file


def guess_alt_pkg_filenames(pkg: str) -> List[str]:
    """
    Given a package name, return possible base filenames (without directories).
    Example:
        pkg='riscv' -> ['riscv_pkg.sv', 'riscv.sv']
        pkg='ariane_pkg' -> ['ariane_pkg.sv']
    """
    names: List[str] = []

    # Direct match
    names.append(f'{pkg}.sv')
    # Common pattern: <name>_pkg.sv when the package is just 'name'
    if not pkg.endswith('_pkg'):
        names.append(f'{pkg}_pkg.sv')

    # Deduplicate while preserving order
    seen = set()
    out = []
    for n in names:
        if n not in seen:
            seen.add(n)
            out.append(n)
    return out


def find_pkg_file_by_name(pkg: str, search_roots: Iterable[Path]) -> Path | None:
    """
    Fallback search: if we don't have this package in our index,
    look for a file whose basename matches common patterns:
      - <pkg>.sv
      - <pkg>_pkg.sv   (for riscv_pkg.sv, config_pkg.sv style files)

    This is exactly what you want for the 'riscv' package when the file is
    named 'riscv_pkg.sv' or 'riscv.sv'.
    """
    candidate_basenames = set(guess_alt_pkg_filenames(pkg))
    for root in search_roots:
        root = root.resolve()
        for p in root.rglob('*.sv'):
            if p.name in candidate_basenames:
                return p
    return None


def resolve_package(
    pkg: str,
    pkg_index: Dict[str, Path],
    search_roots: Iterable[Path],
) -> Path | None:
    """
    Resolve a package name to a file:

      1. If it's in pkg_index, use that.
      2. Otherwise, search for <pkg>.sv or <pkg>_pkg.sv in the search_roots.

    Returns None if not found.
    """
    if pkg in pkg_index:
        return pkg_index[pkg]

    return find_pkg_file_by_name(pkg, search_roots)


# ---------------------------------------------------------------------------
# Dependency closure for packages
# ---------------------------------------------------------------------------


def collect_pkg_closure_for_files(
    start_files: Iterable[Path],
    all_files: Dict[Path, SvFile],
    pkg_index: Dict[str, Path],
    search_roots: Iterable[Path],
) -> Tuple[List[Path], Set[str]]:
    """
    Starting from a set of SV files, compute the transitive closure of
    package dependencies and return:

      (ordered_pkg_files, missing_pkg_names)

    The order is stable and deterministic: sorted by path.
    """
    search_roots = [Path(r).resolve() for r in search_roots]
    visited_pkgs: Set[str] = set()
    missing_pkgs: Set[str] = set()
    pkg_files: Set[Path] = set()

    worklist_files: List[Path] = [Path(f).resolve() for f in start_files]

    while worklist_files:
        fpath = worklist_files.pop()
        sv = all_files.get(fpath)
        if sv is None:
            continue

        used_pkgs = sv.used_packages()
        for pkg in used_pkgs:
            if pkg in visited_pkgs:
                continue
            visited_pkgs.add(pkg)

            pkg_file = resolve_package(pkg, pkg_index, search_roots)
            if pkg_file is None:
                missing_pkgs.add(pkg)
                continue

            pkg_file = pkg_file.resolve()
            if pkg_file not in pkg_files:
                pkg_files.add(pkg_file)
                worklist_files.append(pkg_file)

    ordered_pkg_files = sorted(pkg_files, key=lambda p: str(p))
    return ordered_pkg_files, missing_pkgs


# ---------------------------------------------------------------------------
# High-level helper: build ordered filelist for a top
# ---------------------------------------------------------------------------


def find_candidate_top_files(
    rtl_root: Path,
    top_name: str,
) -> List[Path]:
    """
    Very simple heuristic: search for any file under rtl_root
    that declares 'module <top_name>' or 'interface <top_name>', etc.
    Returns all matches (you can pick the first if you know it's unique).
    """
    rtl_root = rtl_root.resolve()
    matches: List[Path] = []
    for p in iter_sv_files(rtl_root):
        try:
            txt = p.read_text(encoding='utf-8', errors='ignore')
        except OSError:
            continue

        for m in RE_TOP_LIKE.finditer(txt):
            unit_name = m.group(2)
            if unit_name == top_name:
                matches.append(p.resolve())
                break
    return matches


def build_filelist_for_top(
    rtl_root: Path,
    top_name: str,
    include_dirs: Iterable[Path] | None = None,
) -> Tuple[List[Path], List[Path], Set[str]]:
    """
    Build an ordered list of SV files for Jasper (or any simulator)
    for a given top module name.

    Returns:
        (pkg_files, rtl_files, missing_pkgs)

    Where:
      - pkg_files: all package files needed (transitively), sorted.
      - rtl_files: the 'main' RTL files starting from the top file.
                   (currently just [top_file], but you may extend this
                    to include extra RTL around it.)
      - missing_pkgs: any package names that could not be resolved.

    Notes:
      - `include_dirs` are extra places to search for packages such as:
            core/include
            core/pmp/include
        You *should* pass your CVA6 include dirs here.
    """
    rtl_root = rtl_root.resolve()
    include_dirs = [Path(d).resolve() for d in (include_dirs or [])]

    # Load everything once
    all_files = load_sv_tree(rtl_root)
    pkg_index = index_packages(all_files)

    # Find top
    candidates = find_candidate_top_files(rtl_root, top_name)
    if not candidates:
        raise FileNotFoundError(f"Top '{top_name}' not found under RTL root {rtl_root}")

    # For now, pick the first candidate
    top_file = candidates[0]
    rtl_files: List[Path] = [top_file]

    # Compute package closure
    search_roots = [rtl_root] + include_dirs
    pkg_files, missing_pkgs = collect_pkg_closure_for_files(
        start_files=rtl_files,
        all_files=all_files,
        pkg_index=pkg_index,
        search_roots=search_roots,
    )

    return pkg_files, rtl_files, missing_pkgs


# ---------------------------------------------------------------------------
# JasperGold .vc writer
# ---------------------------------------------------------------------------


def write_jasper_vc(
    out_path: Path,
    pkg_files: Iterable[Path],
    rtl_files: Iterable[Path],
    include_dirs: Iterable[Path] | None = None,
) -> None:
    """
    Write a JasperGold-style .vc file with:

        +libext+.v
        +libext+.sv
        +libext+.svh
        +librescan
        +incdir+...
        -y <include_dir>        (optional, if you like library search)
        <pkg_files...>
        <rtl_files...>

    No project-specific paths: everything is whatever you pass in.
    """
    include_dirs = [Path(d).resolve() for d in (include_dirs or [])]
    pkg_files = [Path(f).resolve() for f in pkg_files]
    rtl_files = [Path(f).resolve() for f in rtl_files]

    lines: List[str] = []
    lines.append('+libext+.v')
    lines.append('+libext+.sv')
    lines.append('+libext+.svh')
    lines.append('+librescan')

    for inc in include_dirs:
        lines.append(f'+incdir+{inc}')

    # Optional: treat include dirs as libraries too
    for inc in include_dirs:
        lines.append(f'-y {inc}')

    for f in pkg_files:
        lines.append(str(f))
    for f in rtl_files:
        if f not in pkg_files:
            lines.append(str(f))

    out_path = out_path.resolve()
    out_path.write_text('\n'.join(lines) + '\n', encoding='utf-8')


# ---------------------------------------------------------------------------
# Example: CLI usage (optional)
# ---------------------------------------------------------------------------


def _cli() -> None:
    """
    Minimal CLI so you can do:

        python -m hagent.tool.utils.hdl_utils \\
            --rtl /path/to/cva6/core \\
            --top load_unit \\
            --vc /path/to/files.vc \\
            --inc /path/to/cva6/core/include \\
            --inc /path/to/cva6/core/pmp/include

    This is purely optional; `gen_dep_tcl_and_sva.py` can instead import and
    call `build_filelist_for_top` + `write_jasper_vc` directly.
    """
    import argparse

    p = argparse.ArgumentParser()
    p.add_argument('--rtl', type=Path, required=True, help='RTL root directory')
    p.add_argument('--top', type=str, required=True, help='Top module name')
    p.add_argument('--vc', type=Path, required=True, help='Output .vc file')
    p.add_argument(
        '--inc',
        type=Path,
        action='append',
        default=[],
        help='Extra include directories (can be repeated)',
    )

    args = p.parse_args()

    pkg_files, rtl_files, missing = build_filelist_for_top(
        rtl_root=args.rtl,
        top_name=args.top,
        include_dirs=args.inc,
    )

    if missing:
        print('WARNING: some packages could not be resolved: ' + ', '.join(sorted(missing)))

    write_jasper_vc(
        out_path=args.vc,
        pkg_files=pkg_files,
        rtl_files=rtl_files,
        include_dirs=args.inc,
    )

    print(f'Wrote JasperGold filelist to {args.vc}')


if __name__ == '__main__':
    _cli()
