#!/usr/bin/env python3
"""
Scan coverage.xml and report public class methods (no leading underscore)
that appear unexecuted (0 hits) in coverage. Test files are ignored.

Outputs single-line HINTs and exits non-zero when any are found.
"""

from __future__ import annotations

import sys
from pathlib import Path
import xml.etree.ElementTree as ET
import fnmatch

TEST_DIR_NAMES = {'tests', 'test'}
TEST_FILE_PATTERNS = ['test_*.py', '*_test.py', 'tests.py']


def is_test_path(path: Path) -> bool:
    if any(part in TEST_DIR_NAMES for part in path.parts):
        return True
    name = path.name
    for pat in TEST_FILE_PATTERNS:
        if fnmatch.fnmatch(name, pat):
            return True
    return False


def main(argv: list[str]) -> int:
    # Args: optional coverage xml path (default: ./coverage.xml)
    cov_path = Path(argv[1]).resolve() if len(argv) > 1 else Path('coverage.xml').resolve()
    if not cov_path.exists():
        # Nothing to do; succeed silently
        return 0

    try:
        tree = ET.parse(str(cov_path))
    except Exception as e:
        print(f'COVERAGE: Failed to parse {cov_path}: {e}')
        return 1
    root = tree.getroot()

    public_issues: list[str] = []
    private_hints: list[str] = []

    # Cobertura schema: packages/package/classes/class/methods/method/lines/line
    for cls in root.findall('.//class'):
        filename = cls.get('filename') or ''
        if not filename.endswith('.py'):
            continue
        file_path = Path(filename)
        if is_test_path(file_path):
            continue
        methods = cls.find('methods')
        if methods is None:
            continue
        for m in methods.findall('method'):
            name = m.get('name') or ''
            if not name:
                continue
            # classify
            is_dunder = name.startswith('__')
            is_private = name.startswith('_') and not is_dunder
            is_public = not name.startswith('_')
            if is_dunder:
                continue
            # Compute hits across method's lines
            lines = m.find('lines')
            if lines is None:
                continue
            hit_counts = [int(ln.get('hits', '0')) for ln in lines.findall('line')]
            if not hit_counts:
                continue
            total_hits = sum(hit_counts)
            if total_hits == 0:
                # Get an example line number for pointer
                nums = [int(ln.get('number', '0')) for ln in lines.findall('line') if ln.get('number')]
                lineno = min(nums) if nums else 0
                if is_public:
                    hint = (
                        f"COVERAGE: {file_path.as_posix()}:{lineno}: public method '{name}' has 0 hits in coverage. "
                        f"Hint: Add a test or mark it internal with a leading '_' if not public API."
                    )
                    public_issues.append(hint)
                elif is_private:
                    hint = (
                        f"COVERAGE-PRIVATE: {file_path.as_posix()}:{lineno}: private method '{name}' has 0 hits in coverage. "
                        f'Hint: Optional — add a test if valuable; otherwise ignore if intentionally internal.'
                    )
                    private_hints.append(hint)

    for line in public_issues + private_hints:
        print(line)

    return 1 if public_issues else 0


if __name__ == '__main__':
    sys.exit(main(sys.argv))
