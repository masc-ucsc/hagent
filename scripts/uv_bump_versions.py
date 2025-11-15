#!/usr/bin/env python3
"""
Bump dependency lower bounds in pyproject.toml to at least the currently installed versions.

- Converts 'pkg==X.Y.Z' -> 'pkg>=X.Y.Z'
- If lower bound exists but is below installed, raises it to installed.
- Keeps extras and markers.
- Keeps upper bounds if still compatible; drops only when incompatible with installed.
- Works on:
  - [project.dependencies]
  - [project.optional-dependencies]
  - [tool.uv.dependency-groups]   (if present)

Run:
  python tools/bump_min_versions.py

Requires: packaging, tomlkit
"""

from __future__ import annotations
import shutil
from pathlib import Path
from typing import Dict, List, Tuple

import importlib.metadata as im
from packaging.requirements import Requirement
from packaging.specifiers import SpecifierSet
from packaging.utils import canonicalize_name
from tomlkit import parse, dumps

PYPROJECT = Path('pyproject.toml')


def installed_versions() -> Dict[str, str]:
    """Return {normalized_project_name: version} for all installed distributions."""
    out = {}
    for dist in im.distributions():
        name = canonicalize_name(dist.metadata['Name'])
        out[name] = dist.version
    return out


def _split_req_and_markers(req: Requirement) -> Tuple[str, str]:
    """Return (base, marker_suffix) where marker_suffix includes leading '; ' if present."""
    base = req.name
    if req.extras:
        base += '[' + ','.join(sorted(req.extras)) + ']'
    marker_suffix = ''
    if req.marker:
        marker_suffix = f'; {req.marker}'
    return base, marker_suffix


def _rebuild_specifiers(specs: SpecifierSet) -> str:
    """Rebuild a normalized specifier string with stable ordering."""
    # SpecifierSet string repr is stable but we want a predictable order: >=, >, ==, !=, ~=, <=, <
    order = {'>=': 0, '>': 1, '==': 2, '!=': 3, '~=': 4, '<=': 5, '<': 6}
    items = sorted((s.operator, s.version) for s in specs)
    items.sort(key=lambda t: order.get(t[0], 99))
    return ','.join(f'{op}{ver}' for op, ver in items)


def bump_requirement(req_str: str, versions: Dict[str, str]) -> str:
    """
    Return a possibly-updated requirement string with lower bound >= installed version.
    Keeps markers/extras; drops incompatible upper bounds; converts '==' to '>='.
    """
    req = Requirement(req_str)
    name_key = canonicalize_name(req.name)
    installed = versions.get(name_key)
    if not installed:
        # Package not installed in the current env; leave as-is.
        return req_str

    # Build a new SpecifierSet preserving compatible constraints.
    new_specs = SpecifierSet()
    lower_ver = installed

    # Examine existing specifiers and keep those compatible; note any lower bound.
    for s in req.specifier:
        op, ver = s.operator, s.version
        if op == '==':
            # Replace equality pin with >= installed
            continue
        if op in ('>=', '>'):
            # If existing lower is below installed, we’ll lift to installed
            # If existing lower is above installed, keep it (stricter)
            if (op == '>=' and ver > installed) or (op == '>' and ver >= installed):
                new_specs &= SpecifierSet(str(s))
            # else we will insert >= installed later
            continue
        # Keep other operators only if compatible with installed
        if SpecifierSet(str(s)).contains(installed):
            new_specs &= SpecifierSet(str(s))
        else:
            # Drop incompatible upper bounds (e.g., < installed)
            pass

    # Ensure a lower bound at installed
    # If there is a '>' lower bound above installed already, we kept it.
    if not any(sp.operator in ('>', '>=') for sp in new_specs):
        new_specs &= SpecifierSet(f'>={lower_ver}')

    base, marker_suffix = _split_req_and_markers(req)
    spec_part = _rebuild_specifiers(new_specs)
    if spec_part:
        return f'{base}{spec_part and " "}{spec_part}{marker_suffix}'
    else:
        return f'{base}{marker_suffix}'


def bump_dep_list(dep_list: List[str], versions: Dict[str, str]) -> List[str]:
    out = []
    for dep in dep_list:
        try:
            out.append(bump_requirement(dep, versions))
        except Exception:
            # If parsing fails, keep original to avoid breaking the file.
            out.append(dep)
    return out


def main() -> None:
    if not PYPROJECT.exists():
        raise SystemExit('pyproject.toml not found.')
    backup = PYPROJECT.with_suffix('.toml.bak')
    shutil.copy2(PYPROJECT, backup)

    with PYPROJECT.open('r', encoding='utf-8') as f:
        doc = parse(f.read())

    vers = installed_versions()

    # [project].dependencies
    proj = doc.get('project')
    if proj and 'dependencies' in proj:
        proj['dependencies'] = bump_dep_list(list(proj['dependencies']), vers)

    # [project].optional-dependencies (table of lists)
    if proj and 'optional-dependencies' in proj:
        opt = proj['optional-dependencies']
        for k, v in list(opt.items()):
            opt[k] = bump_dep_list(list(v), vers)

    # [tool.uv.dependency-groups] (if used)
    tool = doc.get('tool')
    if tool and 'uv' in tool:
        uv_table = tool['uv']
        if 'dependency-groups' in uv_table:
            dg = uv_table['dependency-groups']
            for k, v in list(dg.items()):
                dg[k] = bump_dep_list(list(v), vers)

    with PYPROJECT.open('w', encoding='utf-8') as f:
        f.write(dumps(doc))

    print('Updated pyproject.toml (backup at pyproject.toml.bak)')


if __name__ == '__main__':
    main()
