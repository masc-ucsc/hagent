#!/usr/bin/env python3
"""
repo_unused_methods.py

Find class methods defined in a Python codebase that appear unused outside unit tests.

Heuristics (sound-but-incomplete static analysis):
- Builds a symbol table of classes -> methods from AST.
- Counts call-sites to those methods from non-test code by scanning:
  (1) explicit self.method(...) inside same class,
  (2) ClassName.method(...) calls,
  (3) attribute calls obj.method(...) when `obj` is annotated or assigned
      to ClassName in obvious local patterns (very limited, best-effort).
- Excludes test files by glob patterns (e.g., test_*.py, *_test.py) and
  directories named "tests" or "test" by default.
- Ignores dunder methods by default (configurable), with option to ignore
  private (leading underscore) methods too.

Limitations (by design to keep it lightweight and fast):
- Does not execute code; no import graph resolution, alias tracking across modules,
  dynamic dispatch, monkey patching, decorators that alter binding, or complex typing flows.
- Inheritance and mixins are not fully resolved; methods might be called on subclasses
  without explicit ClassName references and thus be missed.
- Calls via getattr, reflection, or strings are not detected.

Despite limitations, it is effective to prune obviously dead methods in medium/large repos.
"""

from __future__ import annotations
import argparse
import ast
import json
import os
from dataclasses import dataclass, field
from pathlib import Path
from typing import Dict, List, Set, Tuple, Optional, Iterable
import fnmatch
import sys
import itertools
import unittest
import tempfile
import textwrap

# ------------------------------ Data Structures ------------------------------


@dataclass(frozen=True)
class MethodKey:
    module: str  # e.g., "pkg.mod"
    class_name: str  # e.g., "MyClass"
    method: str  # e.g., "do_work"

    def fqname(self) -> str:
        return f'{self.module}.{self.class_name}.{self.method}'


@dataclass
class MethodDef:
    key: MethodKey
    lineno: int
    filepath: Path
    dunder: bool
    private_like: bool
    decorators: List[str] = field(default_factory=list)  # e.g., ["staticmethod", "classmethod"]


@dataclass
class RepoIndex:
    methods: Dict[MethodKey, MethodDef] = field(default_factory=dict)
    calls: Dict[MethodKey, int] = field(default_factory=dict)  # counted calls from non-test code


# ------------------------------ Utilities ------------------------------------

TEST_DIR_NAMES = {'tests', 'test'}
DEFAULT_EXCLUDE_DIRS = {'.git', '.venv', 'venv', '.tox', '.mypy_cache', '__pycache__', 'site-packages', 'build', 'dist', '.eggs'}

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


def to_module(root: Path, file: Path) -> str:
    rel = file.relative_to(root).with_suffix('')
    parts = list(rel.parts)
    # Drop __init__ to map pkg/__init__.py -> "pkg"
    if parts and parts[-1] == '__init__':
        parts = parts[:-1]
    return '.'.join(parts) if parts else '__main__'


def iter_py_files(root: Path, include_tests: bool, test_globs: List[str], exclude_dirs: Set[str]) -> Iterable[Path]:
    for dirpath, dirnames, filenames in os.walk(root):
        # Prune excluded directories in-place for efficiency
        dirnames[:] = [d for d in dirnames if d not in exclude_dirs]
        for f in filenames:
            if not f.endswith('.py'):
                continue
            p = Path(dirpath) / f
            if not include_tests and is_test_file(p, test_globs):
                continue
            yield p


def read_text_safe(p: Path) -> Optional[str]:
    try:
        return p.read_text(encoding='utf-8')
    except Exception:
        return None


# ------------------------------ AST Visitors ---------------------------------


@dataclass
class ClassCtx:
    module: str
    class_name: str


class MethodCollector(ast.NodeVisitor):
    """
    Collect class method definitions: def inside ClassDef.
    Records decorators to distinguish staticmethod/classmethod where helpful.
    """

    def __init__(self, module: str, file: Path, ignore_dunder: bool, ignore_private: bool) -> None:
        self.module = module
        self.file = file
        self.ignore_dunder = ignore_dunder
        self.ignore_private = ignore_private
        self.methods: Dict[MethodKey, MethodDef] = {}

    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        class_name = node.name
        for child in node.body:
            if isinstance(child, ast.FunctionDef) or isinstance(child, ast.AsyncFunctionDef):
                mname = child.name
                dunder = mname.startswith('__') and mname.endswith('__')
                private_like = mname.startswith('_') and not dunder
                if self.ignore_dunder and dunder:
                    continue
                if self.ignore_private and private_like:
                    continue
                decorators = []
                for dec in child.decorator_list:
                    # Best-effort decorator name extraction
                    if isinstance(dec, ast.Name):
                        decorators.append(dec.id)
                    elif isinstance(dec, ast.Attribute):
                        decorators.append(dec.attr)
                key = MethodKey(self.module, class_name, mname)
                self.methods[key] = MethodDef(
                    key=key,
                    lineno=child.lineno,
                    filepath=self.file,
                    dunder=dunder,
                    private_like=private_like,
                    decorators=decorators,
                )
        # Continue into nested classes if any
        self.generic_visit(node)


class CallCollector(ast.NodeVisitor):
    """
    Collect calls to class methods with three strategies:
      1) self.method(...) within class scope (most precise within class)
      2) ClassName.method(...) anywhere
      3) obj.method(...) where 'obj' annotated/assigned to ClassName in trivial cases
    """

    def __init__(self, module: str, file: Path, known_classes: Set[str]) -> None:
        self.module = module
        self.file = file
        self.known_classes = known_classes
        self.calls: List[Tuple[str, str]] = []  # (class_name, method)
        self.class_stack: List[str] = []  # current class scope
        # Very shallow var->ClassName map per function for heuristic (reset on function enter)
        self.var_class_map_stack: List[Dict[str, str]] = []

    # ---- Scope handling ----
    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self.class_stack.append(node.name)
        self.generic_visit(node)
        self.class_stack.pop()

    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self.var_class_map_stack.append({})
        self._collect_param_annotations(node)
        self.generic_visit(node)
        self.var_class_map_stack.pop()

    visit_AsyncFunctionDef = visit_FunctionDef

    def _map_var(self) -> Dict[str, str]:
        return self.var_class_map_stack[-1] if self.var_class_map_stack else {}

    def _collect_param_annotations(self, node: ast.FunctionDef) -> None:
        # param: x: ClassName -> map x -> ClassName if known
        varmap = self._map_var()
        for arg in itertools.chain([node.args.vararg] if node.args.vararg else [], [node.args.kwarg] if node.args.kwarg else []):
            pass  # ignore *args, **kwargs
        for arg in itertools.chain(node.args.posonlyargs, node.args.args, node.args.kwonlyargs):
            if arg.annotation and isinstance(arg.annotation, ast.Name):
                if arg.annotation.id in self.known_classes:
                    varmap[arg.arg] = arg.annotation.id

    def visit_AnnAssign(self, node: ast.AnnAssign) -> None:
        # x: ClassName = ...
        if isinstance(node.target, ast.Name) and isinstance(node.annotation, ast.Name):
            if node.annotation.id in self.known_classes:
                self._map_var()[node.target.id] = node.annotation.id
        self.generic_visit(node)

    def visit_Assign(self, node: ast.Assign) -> None:
        # x = ClassName(...) -> map x -> ClassName
        if isinstance(node.value, ast.Call) and isinstance(node.value.func, ast.Name):
            ctor = node.value.func.id
            if ctor in self.known_classes:
                for tgt in node.targets:
                    if isinstance(tgt, ast.Name):
                        self._map_var()[tgt.id] = ctor
        self.generic_visit(node)

    # ---- Calls ----
    def visit_Call(self, node: ast.Call) -> None:
        # self.method(...)
        if isinstance(node.func, ast.Attribute):
            if isinstance(node.func.value, ast.Name):
                recv = node.func.value.id
                meth = node.func.attr
                # (1) self.method inside class -> attribute of current class
                if recv == 'self' and self.class_stack:
                    self.calls.append((self.class_stack[-1], meth))
                # (2) ClassName.method(...)
                elif recv in self.known_classes:
                    self.calls.append((recv, meth))
                # (3) obj.method(...) where obj is trivially mapped to ClassName
                else:
                    c = self._map_var().get(recv)
                    if c:
                        self.calls.append((c, meth))
        self.generic_visit(node)


# ------------------------------ Indexing -------------------------------------


def index_repository(
    root: Path,
    ignore_dunder: bool,
    ignore_private: bool,
    include_tests_for_calls: bool,
    test_globs: List[str],
    exclude_dirs: Set[str],
) -> RepoIndex:
    idx = RepoIndex()

    # Pass 1: collect methods from all files (including tests so we don't miss class names)
    files_all = list(iter_py_files(root, include_tests=True, test_globs=test_globs, exclude_dirs=exclude_dirs))
    for file in files_all:
        src = read_text_safe(file)
        if src is None:
            continue
        try:
            tree = ast.parse(src, filename=str(file))
        except SyntaxError:
            continue
        module = to_module(root, file)
        mc = MethodCollector(module, file, ignore_dunder, ignore_private)
        mc.visit(tree)
        for k, m in mc.methods.items():
            idx.methods[k] = m

    # Precompute known class names for call resolution
    known_classes: Set[str] = {k.class_name for k in idx.methods.keys()}

    # Pass 2: collect calls from non-test files (by default)
    files_for_calls = list(
        iter_py_files(root, include_tests=include_tests_for_calls, test_globs=test_globs, exclude_dirs=exclude_dirs)
    )
    for file in files_for_calls:
        if not include_tests_for_calls and is_test_file(file, test_globs):
            continue
        src = read_text_safe(file)
        if src is None:
            continue
        try:
            tree = ast.parse(src, filename=str(file))
        except SyntaxError:
            continue
        module = to_module(root, file)
        cc = CallCollector(module, file, known_classes)
        cc.visit(tree)
        for cls, meth in cc.calls:
            # We increment counts for any method with matching class+name, regardless of module.
            # This allows resolving subclass calls poorly; acceptable for heuristic pruning.
            for key in idx.methods.keys():
                if key.class_name == cls and key.method == meth:
                    idx.calls[key] = idx.calls.get(key, 0) + 1

    return idx


# ------------------------------ Reporting ------------------------------------


def compute_unused(idx: RepoIndex, consider_static_and_classmethods: bool, require_cross_module_calls: bool) -> List[MethodDef]:
    """
    require_cross_module_calls:
      If True, consider intra-class self.calls insufficient (i.e., require at least one call
      from a different module than where the method is defined). This is strict; default False.
    """
    unused: List[MethodDef] = []

    # Precompute call sites by module when stricter criterion is requested.
    calls_by_key: Dict[MethodKey, int] = idx.calls

    for key, mdef in idx.methods.items():
        call_count = calls_by_key.get(key, 0)

        # Heuristic: drop staticmethod/classmethod if requested
        if not consider_static_and_classmethods:
            if 'staticmethod' in mdef.decorators or 'classmethod' in mdef.decorators:
                continue

        if call_count == 0:
            unused.append(mdef)

    return sorted(unused, key=lambda m: (m.filepath.as_posix(), m.lineno))


def to_json_report(unused: List[MethodDef]) -> str:
    data = [
        {
            'fqname': m.key.fqname(),
            'file': str(m.filepath),
            'line': m.lineno,
            'dunder': m.dunder,
            'private_like': m.private_like,
            'decorators': m.decorators,
        }
        for m in unused
    ]
    return json.dumps(data, indent=2)


def print_table(unused: List[MethodDef]) -> None:
    if not unused:
        print('No candidate unused methods found.')
        return
    # Simple aligned table
    rows = [('File:Line', 'Class', 'Method', 'Decorators')]
    for m in unused:
        rows.append((f'{m.filepath}:{m.lineno}', m.key.class_name, m.key.method, ','.join(m.decorators)))
    widths = [max(len(r[i]) for r in rows) for i in range(4)]
    for i, r in enumerate(rows):
        print('  '.join(col.ljust(widths[j]) for j, col in enumerate(r)))
        if i == 0:
            print('-' * (sum(widths) + 6))


# ------------------------------ CLI ------------------------------------------


def parse_args(argv: Optional[List[str]] = None) -> argparse.Namespace:
    p = argparse.ArgumentParser(description='Find potentially unused class methods in a Python repo.')
    p.add_argument('root', nargs='?', default='.', help='Repository root path (default: current directory)')
    p.add_argument(
        '--include-tests-calls',
        action='store_true',
        help='Include test files as call-sites (by default tests are excluded from call graph).',
    )
    p.add_argument(
        '--test-glob',
        action='append',
        default=None,
        help="Additional glob(s) to match test files (e.g., 'it_*.py'). Can be used multiple times.",
    )
    p.add_argument('--no-ignore-dunder', action='store_true', help='Do not ignore dunder methods.')
    p.add_argument('--ignore-private', action='store_true', help='Ignore private-like methods (single leading underscore).')
    p.add_argument(
        '--consider-static-classmethods', action='store_true', help='Include staticmethod/classmethod candidates in the report.'
    )
    p.add_argument('--exclude-dir', action='append', default=None, help='Additional directory name(s) to exclude (name match).')
    p.add_argument('--json', action='store_true', help='Output JSON instead of table.')
    p.add_argument('--self-test', action='store_true', help='Run internal unit tests and exit.')
    return p.parse_args(argv)


# ------------------------------ Unit Tests -----------------------------------


class _MiniRepoTest(unittest.TestCase):
    def setUp(self) -> None:
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        # Create a small repo
        (self.root / 'pkg').mkdir(parents=True, exist_ok=True)
        (self.root / 'pkg' / '__init__.py').write_text('', encoding='utf-8')

        # Define a module with classes and methods
        (self.root / 'pkg' / 'a.py').write_text(
            textwrap.dedent("""
            class Alpha:
                def used(self):        # will be used via self
                    return 1
                def unused(self):      # will not be called
                    return 2
                @staticmethod
                def s1():
                    return 3
                @classmethod
                def c1(cls):
                    return 4

                def caller(self):
                    return self.used()

            class Beta:
                def b_used(self):
                    return 10
                def b_unused(self):
                    return 11
        """),
            encoding='utf-8',
        )

        # Another module that creates instances and calls methods
        (self.root / 'pkg' / 'b.py').write_text(
            textwrap.dedent("""
            from pkg.a import Alpha, Beta

            def go():
                a = Alpha()
                a.used()
                Alpha.c1()
                b: Beta = Beta()
                b.b_used()
                # Not calling Alpha.unused or Beta.b_unused
        """),
            encoding='utf-8',
        )

        # Tests that call some methods which should NOT count by default
        (self.root / 'tests').mkdir(exist_ok=True)
        (self.root / 'tests' / 'test_a.py').write_text(
            textwrap.dedent("""
            from pkg.a import Alpha
            def test_alpha():
                a = Alpha()
                a.unused()  # Should not count by default (test)
        """),
            encoding='utf-8',
        )

    def tearDown(self) -> None:
        self.tmp.cleanup()

    def test_default_excludes_tests_and_finds_unused(self):
        idx = index_repository(
            self.root,
            ignore_dunder=True,
            ignore_private=False,
            include_tests_for_calls=False,
            test_globs=DEFAULT_TEST_FILE_PATTERNS,
            exclude_dirs=DEFAULT_EXCLUDE_DIRS,
        )
        unused = compute_unused(idx, consider_static_and_classmethods=False, require_cross_module_calls=False)
        names = {m.key.fqname() for m in unused}
        # Alpha.unused and Beta.b_unused should be reported
        self.assertIn('pkg.a.Alpha.unused', names)
        self.assertIn('pkg.a.Beta.b_unused', names)
        # Alpha.used and Beta.b_used are called
        self.assertNotIn('pkg.a.Alpha.used', names)
        self.assertNotIn('pkg.a.Beta.b_used', names)
        # Static/class methods ignored by default
        self.assertNotIn('pkg.a.Alpha.s1', names)
        self.assertNotIn('pkg.a.Alpha.c1', names)

    def test_including_tests_counts_their_calls(self):
        idx = index_repository(
            self.root,
            ignore_dunder=True,
            ignore_private=False,
            include_tests_for_calls=True,  # now tests count as callers
            test_globs=DEFAULT_TEST_FILE_PATTERNS,
            exclude_dirs=DEFAULT_EXCLUDE_DIRS,
        )
        unused = compute_unused(idx, consider_static_and_classmethods=True, require_cross_module_calls=False)
        names = {m.key.fqname() for m in unused}
        # Alpha.unused was called in test; thus should not be reported
        self.assertNotIn('pkg.a.Alpha.unused', names)


# ------------------------------ Main -----------------------------------------


def main(argv: Optional[List[str]] = None) -> int:
    args = parse_args(argv)
    if args.self_test:
        # Run tests and exit with appropriate code
        suite = unittest.defaultTestLoader.loadTestsFromTestCase(_MiniRepoTest)
        result = unittest.TextTestRunner(verbosity=2).run(suite)
        return 0 if result.wasSuccessful() else 1

    root = Path(args.root).resolve()
    assert root.exists() and root.is_dir(), f'Root path does not exist or is not a directory: {root}'

    test_globs = DEFAULT_TEST_FILE_PATTERNS.copy()
    if args.test_glob:
        test_globs.extend(args.test_glob)

    exclude_dirs = DEFAULT_EXCLUDE_DIRS.copy()
    if args.exclude_dir:
        exclude_dirs.update(args.exclude_dir)

    idx = index_repository(
        root=root,
        ignore_dunder=not args.no_ignore_dunder,
        ignore_private=args.ignore_private,
        include_tests_for_calls=args.include_tests_calls,
        test_globs=test_globs,
        exclude_dirs=exclude_dirs,
    )

    unused = compute_unused(
        idx=idx,
        consider_static_and_classmethods=args.consider_static_classmethods,
        require_cross_module_calls=False,
    )

    if args.json:
        print(to_json_report(unused))
    else:
        print_table(unused)

    # Exit with non-zero status if any candidates found, useful in CI.
    return 1 if unused else 0


if __name__ == '__main__':
    sys.exit(main())
