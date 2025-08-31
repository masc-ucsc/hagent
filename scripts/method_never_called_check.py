#!/usr/bin/env python3
"""
Report class methods that appear to be never called anywhere in the repo
(including tests). Methods defined in test files are ignored.

Heuristics match method_privacy_check:
- Skip double-underscore dunder methods (e.g., __init__).
- Skip methods decorated as properties/getters/setters to avoid false positives.
- Very shallow call resolution: self.m(), ClassName.m(), or obj.m() when obj
  is trivially mapped to ClassName in the same function.

Outputs single-line findings and exits non-zero if any issues.
"""

from __future__ import annotations
import ast
import fnmatch
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Set, Tuple

TEST_DIR_NAMES = {'tests', 'test'}
DEFAULT_EXCLUDE_DIRS = {
    '.git',
    '.venv',
    'venv',
    '.tox',
    '.mypy_cache',
    '__pycache__',
    'site-packages',
    'build',
    'dist',
    '.eggs',
}

DEFAULT_TEST_FILE_PATTERNS = [
    'test_*.py',
    '*_test.py',
    'tests.py',
]


def is_test_file(path: Path, test_globs: List[str]) -> bool:
    name = path.name
    if any(part in TEST_DIR_NAMES for part in path.parts):
        return True
    for pat in test_globs:
        if fnmatch.fnmatch(name, pat):
            return True
    return False


def iter_py_files(root: Path, include_tests: bool, test_globs: List[str], exclude_dirs: Set[str]) -> Iterable[Path]:
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = [d for d in dirnames if d not in exclude_dirs]
        for f in filenames:
            if not f.endswith('.py'):
                continue
            p = Path(dirpath) / f
            if not include_tests and is_test_file(p, test_globs):
                continue
            yield p


@dataclass(frozen=True)
class MethodDef:
    file: Path
    class_name: str
    method: str
    lineno: int
    decorators: Tuple[str, ...]


class MethodCollector(ast.NodeVisitor):
    def __init__(self, file: Path) -> None:
        self.file = file
        self.methods: List[MethodDef] = []

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        cls = node.name
        for ch in node.body:
            if isinstance(ch, (ast.FunctionDef, ast.AsyncFunctionDef)):
                name = ch.name
                decos: List[str] = []
                for dec in ch.decorator_list:
                    if isinstance(dec, ast.Name):
                        decos.append(dec.id)
                    elif isinstance(dec, ast.Attribute):
                        decos.append(dec.attr)
                self.methods.append(MethodDef(self.file, cls, name, ch.lineno, tuple(decos)))
        self.generic_visit(node)


class CallCollector(ast.NodeVisitor):
    def __init__(self, known_classes: Set[str]) -> None:
        self.known_classes = known_classes
        self.class_stack: List[str] = []
        self.var_class_map_stack: List[Dict[str, str]] = []
        self.calls: List[Tuple[str, str]] = []

    def _map(self) -> Dict[str, str]:
        return self.var_class_map_stack[-1] if self.var_class_map_stack else {}

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self.class_stack.append(node.name)
        self.generic_visit(node)
        self.class_stack.pop()

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self.var_class_map_stack.append({})
        for arg in list(node.args.posonlyargs) + list(node.args.args) + list(node.args.kwonlyargs):
            if arg.annotation and isinstance(arg.annotation, ast.Name):
                if arg.annotation.id in self.known_classes:
                    self._map()[arg.arg] = arg.annotation.id
        self.generic_visit(node)
        self.var_class_map_stack.pop()

    visit_AsyncFunctionDef = visit_FunctionDef

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        if isinstance(node.target, ast.Name) and isinstance(node.annotation, ast.Name):
            if node.annotation.id in self.known_classes:
                self._map()[node.target.id] = node.annotation.id
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name):
            ctor = node.value.func.id
            if ctor in self.known_classes:
                for tgt in node.targets:
                    if isinstance(tgt, ast.Name):
                        self._map()[tgt.id] = ctor
        self.generic_visit(node)

    def visit_Call(self, node: ast.Call) -> None:
        f = node.func
        if isinstance(f, ast.Attribute) and isinstance(f.value, ast.Name):
            recv = f.value.id
            meth = f.attr
            if recv == 'self' and self.class_stack:
                self.calls.append((self.class_stack[-1], meth))
            elif recv in self.known_classes:
                self.calls.append((recv, meth))
            else:
                c = self._map().get(recv)
                if c:
                    self.calls.append((c, meth))
        self.generic_visit(node)


def main(argv: Optional[List[str]] = None) -> int:
    root = Path(argv[1]).resolve() if argv and len(argv) > 1 else Path.cwd()
    test_globs = list(DEFAULT_TEST_FILE_PATTERNS)

    # Collect methods from all files (we'll later skip those defined in tests)
    methods: List[MethodDef] = []
    files_all = list(iter_py_files(root, include_tests=True, test_globs=test_globs, exclude_dirs=DEFAULT_EXCLUDE_DIRS))
    for pf in files_all:
        try:
            src = pf.read_text(encoding='utf-8')
        except Exception:
            continue
        try:
            tree = ast.parse(src, filename=str(pf))
        except SyntaxError:
            continue
        mc = MethodCollector(pf)
        mc.visit(tree)
        methods.extend(mc.methods)

    known_classes: Set[str] = {m.class_name for m in methods}

    # Collect calls from ALL files including tests
    calls_by_method: Dict[Tuple[str, str], int] = {}
    files_calls = list(iter_py_files(root, include_tests=True, test_globs=test_globs, exclude_dirs=DEFAULT_EXCLUDE_DIRS))
    for pf in files_calls:
        try:
            src = pf.read_text(encoding='utf-8')
        except Exception:
            continue
        try:
            tree = ast.parse(src, filename=str(pf))
        except SyntaxError:
            continue
        cc = CallCollector(known_classes)
        cc.visit(tree)
        for cls, meth in cc.calls:
            calls_by_method[(cls, meth)] = calls_by_method.get((cls, meth), 0) + 1

    issues: List[str] = []

    for m in methods:
        # Skip test-defined methods
        if is_test_file(m.file, test_globs):
            continue
        # Skip dunder methods
        if m.method.startswith('__'):
            continue
        # Skip property-like methods to avoid many false positives
        deco_lower = ','.join(m.decorators).lower()
        if any(k in deco_lower for k in ('property', 'setter', 'getter')):
            continue
        # Count calls
        called = calls_by_method.get((m.class_name, m.method), 0)
        if called == 0:
            issues.append(
                f'UNUSED: {m.file}:{m.lineno} {m.class_name}.{m.method} appears never called. Hint: Add a test or remove/refactor.'
            )

    for line in issues:
        print(line)

    return 1 if issues else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
