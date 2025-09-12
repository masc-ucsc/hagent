#!/usr/bin/env python3
"""
Checks for code complexity issues that indicate spaghetti code:

- Functions longer than 60 lines of code (excluding comments and blank lines).
- Large classes with too many lines of code.
- Python files with multiple complex classes (suggesting need for splitting).

Reports issues ranked by severity (line count) to help identify refactoring candidates.
"""

from __future__ import annotations
import argparse
import ast
import fnmatch
import os
import sys
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, Iterable, List, Optional, Set, Tuple


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

# Configuration thresholds
FUNCTION_LOC_THRESHOLD = 100
CLASS_LOC_THRESHOLD = 400
FILE_MULTIPLE_CLASSES_THRESHOLD = 2  # files with 2+ non-trivial classes


def is_test_file(path: Path, test_globs: List[str]) -> bool:
    """Check if a file is a test file based on name patterns and directory."""
    name = path.name
    # Check if any part of the path contains test directory names
    if any(part.lower() in {'tests', 'test'} for part in path.parts):
        return True
    # Check filename patterns
    for pat in test_globs:
        if fnmatch.fnmatch(name, pat):
            return True
    return False


def iter_py_files(root: Path, include_tests: bool, test_globs: List[str], exclude_dirs: Set[str]) -> Iterable[Path]:
    """Iterate over Python files in the directory tree."""
    for dirpath, dirnames, filenames in os.walk(root):
        # Remove excluded directories
        dirnames[:] = [d for d in dirnames if d not in exclude_dirs]
        for f in filenames:
            if not f.endswith('.py'):
                continue
            p = Path(dirpath) / f
            if not include_tests and is_test_file(p, test_globs):
                continue
            yield p


def count_significant_lines(source_lines: List[str], start_line: int, end_line: int) -> int:
    """
    Count lines of code excluding comments and blank lines.
    
    Args:
        source_lines: List of source code lines (0-indexed)
        start_line: Start line number (1-indexed, inclusive)
        end_line: End line number (1-indexed, inclusive)
        
    Returns:
        Number of significant lines of code
    """
    count = 0
    for i in range(start_line - 1, min(end_line, len(source_lines))):
        line = source_lines[i].strip()
        # Skip blank lines
        if not line:
            continue
        # Skip comment-only lines
        if line.startswith('#'):
            continue
        # Skip docstring-only lines (simple heuristic)
        if line.startswith('"""') or line.startswith("'''"):
            continue
        count += 1
    return count


@dataclass(frozen=True)
class FunctionInfo:
    file: Path
    name: str
    start_line: int
    end_line: int
    loc: int
    class_name: Optional[str] = None  # None for module-level functions


@dataclass(frozen=True)
class ClassInfo:
    file: Path
    name: str
    start_line: int
    end_line: int
    loc: int
    method_count: int
    is_trivial: bool


@dataclass(frozen=True)
class FileComplexityInfo:
    file: Path
    total_loc: int
    class_count: int
    non_trivial_class_count: int
    classes: List[ClassInfo]


class CodeComplexityVisitor(ast.NodeVisitor):
    """AST visitor to collect complexity information."""
    
    def __init__(self, file: Path, source_lines: List[str]):
        self.file = file
        self.source_lines = source_lines
        self.functions: List[FunctionInfo] = []
        self.classes: List[ClassInfo] = []
        self.class_stack: List[str] = []
        
    def _get_node_end_line(self, node: ast.AST) -> int:
        """Get the end line of an AST node."""
        if hasattr(node, 'end_lineno') and node.end_lineno is not None:
            return node.end_lineno
        
        # Fallback: find the maximum line number in the subtree
        max_lineno = getattr(node, 'lineno', 1)
        for child in ast.walk(node):
            if hasattr(child, 'lineno') and child.lineno is not None:
                max_lineno = max(max_lineno, child.lineno)
            if hasattr(child, 'end_lineno') and child.end_lineno is not None:
                max_lineno = max(max_lineno, child.end_lineno)
        return max_lineno
        
    def visit_FunctionDef(self, node: ast.FunctionDef) -> None:
        self._visit_function(node)
        
    def visit_AsyncFunctionDef(self, node: ast.AsyncFunctionDef) -> None:
        self._visit_function(node)
        
    def _visit_function(self, node) -> None:
        """Handle both sync and async function definitions."""
        start_line = node.lineno
        end_line = self._get_node_end_line(node)
        loc = count_significant_lines(self.source_lines, start_line, end_line)
        
        class_name = self.class_stack[-1] if self.class_stack else None
        
        self.functions.append(FunctionInfo(
            file=self.file,
            name=node.name,
            start_line=start_line,
            end_line=end_line,
            loc=loc,
            class_name=class_name
        ))
        
        self.generic_visit(node)
        
    def visit_ClassDef(self, node: ast.ClassDef) -> None:
        self.class_stack.append(node.name)
        
        start_line = node.lineno
        end_line = self._get_node_end_line(node)
        loc = count_significant_lines(self.source_lines, start_line, end_line)
        
        # Count methods in this class
        method_count = 0
        for child in node.body:
            if isinstance(child, (ast.FunctionDef, ast.AsyncFunctionDef)):
                method_count += 1
                
        # Simple heuristic for trivial classes
        # A class is trivial if it has few methods and few lines
        is_trivial = method_count <= 2 and loc <= 20
        
        self.classes.append(ClassInfo(
            file=self.file,
            name=node.name,
            start_line=start_line,
            end_line=end_line,
            loc=loc,
            method_count=method_count,
            is_trivial=is_trivial
        ))
        
        self.generic_visit(node)
        self.class_stack.pop()


def analyze_file(file_path: Path) -> Tuple[List[FunctionInfo], List[ClassInfo], FileComplexityInfo]:
    """Analyze a single Python file for complexity issues."""
    try:
        source = file_path.read_text(encoding='utf-8')
        source_lines = source.splitlines()
    except Exception:
        return [], [], FileComplexityInfo(file_path, 0, 0, 0, [])
    
    try:
        tree = ast.parse(source, filename=str(file_path))
    except SyntaxError:
        return [], [], FileComplexityInfo(file_path, 0, 0, 0, [])
    
    visitor = CodeComplexityVisitor(file_path, source_lines)
    visitor.visit(tree)
    
    # Calculate file-level metrics
    total_loc = count_significant_lines(source_lines, 1, len(source_lines))
    non_trivial_classes = [c for c in visitor.classes if not c.is_trivial]
    
    file_info = FileComplexityInfo(
        file=file_path,
        total_loc=total_loc,
        class_count=len(visitor.classes),
        non_trivial_class_count=len(non_trivial_classes),
        classes=visitor.classes
    )
    
    return visitor.functions, visitor.classes, file_info


def parse_arguments(argv: Optional[List[str]] = None) -> argparse.Namespace:
    """Parse command-line arguments."""
    parser = argparse.ArgumentParser(
        description="Check for code complexity issues (spaghetti code detection)",
        formatter_class=argparse.ArgumentDefaultsHelpFormatter
    )
    parser.add_argument(
        'directory',
        nargs='?',
        default='.',
        help='Directory to analyze (default: current directory)'
    )
    parser.add_argument(
        '--function-threshold',
        type=int,
        default=FUNCTION_LOC_THRESHOLD,
        help='Threshold for long function detection (lines of code)'
    )
    parser.add_argument(
        '--class-threshold',
        type=int,
        default=CLASS_LOC_THRESHOLD,
        help='Threshold for large class detection (lines of code)'
    )
    parser.add_argument(
        '--multi-class-threshold',
        type=int,
        default=FILE_MULTIPLE_CLASSES_THRESHOLD,
        help='Threshold for files with multiple classes'
    )
    
    return parser.parse_args(argv)


def main(argv: Optional[List[str]] = None) -> int:
    """Main entry point for the complexity checker."""
    args = parse_arguments(argv)
    root = Path(args.directory).resolve()
    test_globs = list(DEFAULT_TEST_FILE_PATTERNS)
    
    # Use configured thresholds
    function_threshold = args.function_threshold
    class_threshold = args.class_threshold
    multi_class_threshold = args.multi_class_threshold
    
    all_functions: List[FunctionInfo] = []
    all_classes: List[ClassInfo] = []
    all_file_infos: List[FileComplexityInfo] = []
    
    # Collect data from all Python files
    files = list(iter_py_files(root, include_tests=False, test_globs=test_globs, exclude_dirs=DEFAULT_EXCLUDE_DIRS))
    for file_path in files:
        functions, classes, file_info = analyze_file(file_path)
        all_functions.extend(functions)
        all_classes.extend(classes)
        all_file_infos.append(file_info)
    
    issues: List[str] = []
    
    # 1. Long functions (over threshold)
    long_functions = [f for f in all_functions if f.loc > function_threshold]
    long_functions.sort(key=lambda f: f.loc, reverse=True)  # Sort by length, longest first
    
    for func in long_functions:
        location = f"{func.class_name}.{func.name}" if func.class_name else func.name
        issues.append(
            f"LONG_FUNCTION: {func.file}:{func.start_line} {location} has {func.loc} lines "
            f"(threshold: {function_threshold}). Hint: Consider breaking into smaller functions."
        )
    
    # 2. Large classes (over threshold)
    large_classes = [c for c in all_classes if c.loc > class_threshold and not c.is_trivial]
    large_classes.sort(key=lambda c: c.loc, reverse=True)  # Sort by length, longest first
    
    for cls in large_classes:
        issues.append(
            f"LARGE_CLASS: {cls.file}:{cls.start_line} {cls.name} has {cls.loc} lines "
            f"(threshold: {class_threshold}). Hint: Consider splitting into multiple classes or modules."
        )
    
    # 3. Files with multiple complex classes
    complex_files = [f for f in all_file_infos if f.non_trivial_class_count >= multi_class_threshold]
    complex_files.sort(key=lambda f: f.non_trivial_class_count, reverse=True)
    
    for file_info in complex_files:
        class_names = [c.name for c in file_info.classes if not c.is_trivial]
        issues.append(
            f"MULTI_CLASS_FILE: {file_info.file} has {file_info.non_trivial_class_count} complex classes: "
            f"{', '.join(class_names)}. Hint: Consider splitting into separate modules."
        )
    
    # Emit issues
    for issue in issues:
        print(issue)
    
    return 1 if issues else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv[1:]))
