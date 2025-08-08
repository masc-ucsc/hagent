#!/usr/bin/env python3
"""
Output directory management utility for hagent.

This module provides a centralized way to determine where output files
should be written, supporting the HAGENT_OUTPUT environment variable
with a default fallback to 'output'.
"""

import os
import sys
from pathlib import Path


def get_output_dir() -> str:
    """
    Get the output directory path.

    Returns the directory specified by HAGENT_OUTPUT environment variable,
    or 'output' as the default if not set.

    The directory will be created if it doesn't exist.

    Returns:
        str: Path to the output directory
    """
    output_dir = os.environ.get('HAGENT_OUTPUT', 'output')

    # Create the directory if it doesn't exist
    Path(output_dir).mkdir(parents=True, exist_ok=True)

    return output_dir


def get_output_path(filename: str) -> str:
    """
    Get the full path for an output file.

    Args:
        filename: The name of the output file (must be a relative path)

    Returns:
        str: Full path to the output file in the output directory

    Raises:
        SystemExit: If filename is an absolute path
    """
    # Check for absolute paths (including edge cases)
    is_absolute = (
        os.path.isabs(filename)  # Standard absolute path check
        or filename.startswith('~')  # Home directory expansion
        or (len(filename) >= 3 and filename[1:3] == ':\\')  # Windows drive letter (C:\)
    )

    if is_absolute:
        print(f"ERROR: get_output_path() called with absolute path: '{filename}'", file=sys.stderr)
        print('', file=sys.stderr)
        print('API CONSTRAINT VIOLATION:', file=sys.stderr)
        print('get_output_path() only accepts relative paths (filenames or relative paths).', file=sys.stderr)
        print('', file=sys.stderr)
        print('Examples of correct usage:', file=sys.stderr)
        print("  get_output_path('my_file.log')           # ✓ filename only", file=sys.stderr)
        print("  get_output_path('subdir/my_file.txt')    # ✓ relative path", file=sys.stderr)
        print('', file=sys.stderr)
        print('Examples of incorrect usage:', file=sys.stderr)
        print("  get_output_path('/tmp/my_file.log')      # ✗ absolute path", file=sys.stderr)
        print("  get_output_path('/Users/name/file.txt')  # ✗ absolute path", file=sys.stderr)
        print('', file=sys.stderr)
        print('If you need to write to an absolute path, use that path directly', file=sys.stderr)
        print('instead of get_output_path().', file=sys.stderr)
        sys.exit(1)

    return os.path.join(get_output_dir(), filename)
