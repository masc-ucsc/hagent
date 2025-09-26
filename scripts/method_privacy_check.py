#!/usr/bin/env python3
"""
Checks method privacy/usage conventions:

- Private-like methods (single leading underscore, non-dunder) must only be
  called inside their defining file or from test files.
- Public methods that are only called within their defining file or by tests
  should be made private (prefix with a single underscore).

Heuristic static analysis (similar scope as find_used_methods.py):
- Collect class methods (def inside class) per file.
- Collect call sites from non-test code via three patterns:
  - self.method(...)
  - ClassName.method(...)
  - obj.method(...) where obj is trivially mapped to ClassName via simple
    assignment/annotation patterns in the same function.

Outputs human-readable findings with hints and exits non-zero on any issues.
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

# Methods that are considered public API by convention in this repo and
# should not be suggested to become private even if only used internally.
PUBLIC_ALWAYS: Set[str] = {
    'run',
    'parse',
    'setup',
    'get_error',
    'set_error',
}


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
    private_like: bool
    dunder: bool
    decorators: Tuple[str, ...]
    class_bases: Tuple[str, ...]


class MethodCollector(ast.NodeVisitor):
    def __init__(self, file: Path) -> None:
        self.file = file
        self.methods: List[MethodDef] = []

    def _base_to_name(self, b: ast.expr) -> str:
        if isinstance(b, ast.Name):
            return b.id
        parts: List[str] = []
        cur = b
        while isinstance(cur, ast.Attribute):
            parts.append(cur.attr)
            cur = cur.value
        if isinstance(cur, ast.Name):
            parts.append(cur.id)
        parts.reverse()
        return '.'.join(parts) if parts else ''

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        cls = node.name
        bases = tuple(self._base_to_name(b) for b in node.bases)
        for ch in node.body:
            if isinstance(ch, (ast.FunctionDef, ast.AsyncFunctionDef)):
                name = ch.name
                dunder = name.startswith('__') and name.endswith('__')
                private_like = name.startswith('_') and not dunder
                decos: List[str] = []
                for dec in ch.decorator_list:
                    if isinstance(dec, ast.Name):
                        decos.append(dec.id)
                    elif isinstance(dec, ast.Attribute):
                        decos.append(dec.attr)
                self.methods.append(
                    MethodDef(
                        file=self.file,
                        class_name=cls,
                        method=name,
                        lineno=ch.lineno,
                        private_like=private_like,
                        dunder=dunder,
                        decorators=tuple(decos),
                        class_bases=bases,
                    )
                )
        self.generic_visit(node)


class CallCollector(ast.NodeVisitor):
    """Collect (class_name, method_name, in_main_block) for calls in this file.

    Tracks very shallow var->ClassName maps within a function to resolve
    obj.method() to ClassName.method. Also tracks whether a call happens
    under an `if __name__ == "__main__":` guard to treat those usages as
    CLI/public entrypoints.
    """

    def __init__(self, known_classes: Set[str]) -> None:
        self.known_classes = known_classes
        self.class_stack: List[str] = []
        self.var_class_map_stack: List[Dict[str, str]] = []
        self.main_block_stack: List[bool] = []
        self.calls: List[Tuple[str, str, bool]] = []

    def _map(self) -> Dict[str, str]:
        return self.var_class_map_stack[-1] if self.var_class_map_stack else {}

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self.class_stack.append(node.name)
        self.generic_visit(node)
        self.class_stack.pop()

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self.var_class_map_stack.append({})
        # param annotations
        for arg in list(node.args.posonlyargs) + list(node.args.args) + list(node.args.kwonlyargs):
            if arg.annotation and isinstance(arg.annotation, ast.Name):
                if arg.annotation.id in self.known_classes:
                    self._map()[arg.arg] = arg.annotation.id
        self.generic_visit(node)
        self.var_class_map_stack.pop()

    visit_AsyncFunctionDef = visit_FunctionDef

    # --- main guard handling ---
    def _is_main_guard(self, test: ast.expr) -> bool:
        # Matches: if __name__ == "__main__":
        if isinstance(test, ast.Compare):
            # left == right
            left = test.left
            comps = test.comparators
            if len(comps) != 1 or len(test.ops) != 1:
                return False
            op = test.ops[0]
            right = comps[0]

            def is_name_main(n: ast.AST) -> bool:
                return isinstance(n, ast.Name) and n.id == '__name__'

            def is_const_main(n: ast.AST) -> bool:
                return isinstance(n, ast.Constant) and n.value == '__main__'

            if isinstance(op, ast.Eq) and (
                (is_name_main(left) and is_const_main(right)) or (is_const_main(left) and is_name_main(right))
            ):
                return True
        return False

    def _in_main(self) -> bool:
        return any(self.main_block_stack)

    def visit_If(self, node: ast.If) -> None:
        if self._is_main_guard(node.test):
            # Traverse body under main flag, orelse without
            self.main_block_stack.append(True)
            for stmt in node.body:
                self.visit(stmt)
            self.main_block_stack.pop()
            for stmt in node.orelse:
                self.visit(stmt)
        else:
            self.generic_visit(node)

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
                self.calls.append((self.class_stack[-1], meth, self._in_main()))
            elif recv in self.known_classes:
                self.calls.append((recv, meth, self._in_main()))
            else:
                c = self._map().get(recv)
                if c:
                    self.calls.append((c, meth, self._in_main()))
        self.generic_visit(node)


def main(argv: Optional[List[str]] = None) -> int:
    root = Path(argv[1]).resolve() if argv and len(argv) > 1 else Path.cwd()
    test_globs = list(DEFAULT_TEST_FILE_PATTERNS)

    # Pass 1: collect methods from all files (including tests to learn class names)
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

    # Pass 2: collect non-test call sites per file
    calls_by_method: Dict[Tuple[str, str], Set[Path]] = {}
    calls_in_main: Dict[Tuple[str, str], Set[Path]] = {}
    files_for_calls = list(iter_py_files(root, include_tests=False, test_globs=test_globs, exclude_dirs=DEFAULT_EXCLUDE_DIRS))
    for pf in files_for_calls:
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
        for cls, meth, in_main in cc.calls:
            key = (cls, meth)
            calls_by_method.setdefault(key, set()).add(pf)
            if in_main:
                calls_in_main.setdefault(key, set()).add(pf)

    # Analyze
    issues: List[str] = []

    def _has_base_suffix(bases: Tuple[str, ...], suffix: str) -> bool:
        return any(b.endswith(suffix) for b in bases)

    for m in methods:
        # Skip any methods defined in test files entirely; tests are free to
        # use private/public methods without policy constraints.
        if is_test_file(m.file, test_globs):
            continue
        # Skip methods on unittest.TestCase subclasses
        if _has_base_suffix(m.class_bases, 'TestCase'):
            continue
        key = (m.class_name, m.method)
        callers: Set[Path] = calls_by_method.get(key, set())
        # Filter: ignore obvious property-like methods to reduce false positives
        if any('property' in d for d in m.decorators):
            continue
        # Skip double-underscore methods entirely (e.g., __init__, __enter__)
        if m.method.startswith('__'):
            continue
        # Skip common visitor pattern methods
        if m.method.startswith('visit_') or _has_base_suffix(m.class_bases, 'NodeVisitor'):
            continue

        # 1) Private-like method called from outside its defining file (non-test)
        if m.private_like:
            external_callers = [c for c in callers if c.resolve() != m.file.resolve()]
            if external_callers:
                for c in sorted(external_callers):
                    issues.append(
                        f'PRIVACY: Private method called externally: {c}:{m.class_name}.{m.method} -> defined at {m.file}:{m.lineno}. '
                        f"Hint: Only call private methods within the same file or tests; otherwise remove '_' or refactor."
                    )

        # 2) Public method used only internally (same file) or by tests -> should be private
        else:
            cross_file_callers = [c for c in callers if c.resolve() != m.file.resolve()]
            # Treat calls from a __main__ guard in the same file as external/public usage
            main_in_same_file = m.file.resolve() in {p.resolve() for p in calls_in_main.get(key, set())}
            if not cross_file_callers and not main_in_same_file:
                # Respect conventional public API names
                if m.method in PUBLIC_ALWAYS:
                    continue
                issues.append(
                    f'PRIVACY: Public method appears internal-only: {m.file}:{m.lineno} {m.class_name}.{m.method}. '
                    f'Hint: Consider renaming to _{m.method} if not part of public API or add test or delete it.'
                )

    # Emit
    for line in issues:
        print(line)

    return 1 if issues else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
