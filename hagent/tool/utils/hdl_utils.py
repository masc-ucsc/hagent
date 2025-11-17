#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
HDL Utilities
-------------
Reusable HDL utilities for:
  - SystemVerilog / Verilog file discovery
  - Module and package indexing
  - Dependency closure (module instantiations, package imports, includes)
  - Include-path resolution

Features:
  ✅ Recursively finds Verilog/SystemVerilog files
  ✅ Detects `_pkg.sv` / `_pkg.svh` even if no 'package' keyword
  ✅ Follows `import pkg::*;` and `\`include "foo.svh"`
  ✅ Produces closure of all reachable dependencies

Used by:
  - gen_dep_tcl_and_sva.py
  - other formal or synthesis dependency generators
"""

import re
from pathlib import Path
from typing import List, Dict, Tuple, Set
from collections import deque
from rich.console import Console

console = Console()

SV_EXTS = {".sv", ".v"}
HDR_EXTS = {".svh", ".vh"}


# -----------------------------------------------------------------------------
#  Comment stripping (shared utility)
# -----------------------------------------------------------------------------
def strip_comments(text: str) -> str:
    """Remove both block and line comments from HDL text."""
    text = re.sub(r"/\*.*?\*/", "", text, flags=re.S)  # block comments
    text = re.sub(r"//.*?$", "", text, flags=re.M)     # line comments
    return text


# -----------------------------------------------------------------------------
#  File scanning and indexing
# -----------------------------------------------------------------------------
def find_sv_files(root: Path, skip_dirs: Set[str]) -> List[Path]:
    """Recursively collect all .sv/.v/.svh/.vh files, skipping unwanted dirs."""
    files = []
    for p in root.rglob("*"):
        if p.is_dir():
            continue
        if any(part in skip_dirs for part in p.parts):
            continue
        if p.suffix in SV_EXTS.union(HDR_EXTS):
            files.append(p.resolve())
    return files


def index_modules_packages(files: List[Path]) -> Tuple[Dict[str, Path], Dict[str, Path]]:
    """
    Return (modules: name->file, packages: name->file).

    Adds fallback support:
      - filenames containing '_pkg'
      - included-only package files (even if no 'package' keyword)
    """
    modules = {}
    packages = {}

    mod_re = re.compile(r"\bmodule\s+([A-Za-z_]\w*)\b")
    pkg_re = re.compile(r"\bpackage\s+([A-Za-z_]\w*)\b")

    for f in files:
        try:
            txt = strip_comments(f.read_text(errors="ignore"))
        except Exception:
            continue

        # Detect modules
        for m in mod_re.finditer(txt):
            modules[m.group(1)] = f

        # Detect declared packages
        pkg_found = False
        for m in pkg_re.finditer(txt):
            packages[m.group(1)] = f
            pkg_found = True

        # Fallback: file name heuristic (e.g. config_pkg.sv)
        if not pkg_found and "_pkg" in f.stem.lower():
            pkg_name = f.stem.replace(".sv", "").replace(".svh", "")
            packages[pkg_name] = f

    return modules, packages


# -----------------------------------------------------------------------------
#  Include and import parsing
# -----------------------------------------------------------------------------
def find_includes(text: str) -> List[str]:
    """Find `include "file.sv"` patterns."""
    return re.findall(r'`include\s+"([^"]+)"', text)


def find_pkg_imports(text: str) -> Set[str]:
    """Find package import statements like `import foo_pkg::*;`"""
    return set(re.findall(r"\bimport\s+([A-Za-z_]\w*)::\*\s*;", text))


def find_module_insts(text: str, known_modules: Set[str]) -> Set[str]:
    """Find instantiated submodules within HDL text."""
    insts = set()
    for stmt in re.split(r";", text):
        for mn in known_modules:
            if re.search(rf"\b{re.escape(mn)}\b\s*(#\s*\([^;]*\))?\s+[A-Za-z_]\w*\s*\(", stmt):
                insts.add(mn)
    return insts


# -----------------------------------------------------------------------------
#  Include resolution
# -----------------------------------------------------------------------------
def resolve_include_path(token: str, src_dir: Path, incdirs: List[Path]) -> Path | None:
    """Resolve an include file relative to the source and incdirs."""
    candidates = [src_dir / token] + [d / token for d in incdirs]
    for c in candidates:
        if c.exists():
            return c.resolve()
    return None


# -----------------------------------------------------------------------------
#  Dependency graph resolution
# -----------------------------------------------------------------------------
def collect_file_deps(
    fpath: Path,
    src_root: Path,
    incdirs_initial: List[Path],
    known_modules: Set[str],
) -> Tuple[Set[str], Set[str], Set[Path], Set[Path]]:
    """
    Collect dependencies for a single file.

    Returns:
      (instantiated_module_names, imported_pkg_names, header_paths, header_dirs)
    """
    try:
        txt = strip_comments(fpath.read_text(errors="ignore"))
    except Exception:
        return set(), set(), set(), set()

    insts = find_module_insts(txt, known_modules)
    pkgs = find_pkg_imports(txt)
    hdr_tokens = find_includes(txt)

    headers = set()
    header_dirs = set()
    q = deque(hdr_tokens)
    seen_hdr = set()
    base_incdirs = [fpath.parent.resolve()] + incdirs_initial

    while q:
        tok = q.popleft()
        if tok in seen_hdr:
            continue
        seen_hdr.add(tok)
        resolved = resolve_include_path(tok, src_root, base_incdirs)
        if not resolved:
            continue
        headers.add(resolved)
        header_dirs.add(resolved.parent.resolve())
        try:
            htxt = strip_comments(resolved.read_text(errors="ignore"))
        except Exception:
            continue
        for ntok in find_includes(htxt):
            if ntok not in seen_hdr:
                q.append(ntok)

    return insts, pkgs, headers, header_dirs


def compute_transitive_closure(
    top_module: str,
    modules: Dict[str, Path],
    packages: Dict[str, Path],
    src_root: Path,
    user_incdirs: List[Path],
) -> Tuple[List[Path], List[Path], Set[str]]:
    """
    Compute transitive dependency closure starting from top module.

    Returns (ordered_files, incdirs, reachable_module_names)
    Includes:
      - all instantiated submodules
      - all packages imported directly/indirectly
      - all included header files
    """
    if top_module not in modules:
        raise SystemExit(f"ERROR: top module '{top_module}' not found in source files.")

    known_mods = set(modules.keys())
    needed_files: Set[Path] = set()
    needed_incdirs: Set[Path] = set(user_incdirs)
    pending_mods = deque([top_module])
    visited_mods = set()

    while pending_mods:
        mod = pending_mods.popleft()
        if mod in visited_mods:
            continue
        visited_mods.add(mod)

        mod_file = modules.get(mod)
        if not mod_file:
            continue
        needed_files.add(mod_file.resolve())

        insts, pkgs, headers, hdr_dirs = collect_file_deps(
            mod_file, src_root, list(needed_incdirs), known_mods
        )

        # Add submodules recursively
        for child in insts:
            if child not in visited_mods:
                pending_mods.append(child)

        # Add package dependencies
        for pn in pkgs:
            pfile = packages.get(pn)
            if not pfile:
                # fallback: filename heuristic for missing imports
                alt_pkg = next((f for name, f in packages.items() if pn.lower() in name.lower()), None)
                if alt_pkg:
                    pfile = alt_pkg
            if pfile:
                needed_files.add(pfile.resolve())
                _, _, p_headers, p_hdr_dirs = collect_file_deps(
                    pfile, src_root, list(needed_incdirs), known_mods
                )
                needed_files.update(p_headers)
                needed_incdirs.update(p_hdr_dirs)

        # Add headers (includes)
        needed_files.update(headers)
        needed_incdirs.update(hdr_dirs)

    # Sort: RTL first, headers later
    rtl_files = [p for p in sorted(needed_files) if p.suffix in SV_EXTS]
    hdr_files = [p for p in sorted(needed_files) if p.suffix in HDR_EXTS]
    files_out = rtl_files + hdr_files
    incdirs_out = sorted(set(d for d in needed_incdirs))
    return files_out, incdirs_out, visited_mods
