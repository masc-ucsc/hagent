#!/usr/bin/env python3
"""
Output directory management utility for hagent.

This module provides a centralized way to determine where output files
should be written (logs, test results, etc.). Uses HAGENT_OUTPUT_DIR
when set, otherwise falls back to HAGENT_CACHE_DIR/inou/logs/ structure.
"""

import os
import sys
from pathlib import Path

from .path_manager import PathManager
from .container_manager import is_docker_mode


def get_output_dir() -> str:
    """
    Get the output directory path.

    Uses HAGENT_OUTPUT_DIR if set, otherwise uses PathManager to get
    HAGENT_CACHE_DIR/inou/logs/ for logs and output files.

    The directory will be created if it doesn't exist.

    Returns:
        str: Path to the output directory
    """
    # First priority: HAGENT_OUTPUT_DIR if explicitly set
    if os.environ.get('HAGENT_OUTPUT_DIR'):
        output_dir = Path(os.environ['HAGENT_OUTPUT_DIR']).resolve()
        output_dir.mkdir(parents=True, exist_ok=True)
        return str(output_dir)

    # Second priority: Use PathManager for structured logs directory
    try:
        log_dir = PathManager().get_log_dir()

        # In Docker mode, use local output directory for host-side file operations
        if is_docker_mode():
            print(f'🔍 DEBUG: Docker mode - using local output dir instead of container path: {log_dir}')
            output_dir = Path.cwd() / 'output'
            output_dir.mkdir(parents=True, exist_ok=True)
            return str(output_dir.resolve())

        # Native mode - use PathManager directory
        output_dir = Path(log_dir)
        output_dir.mkdir(parents=True, exist_ok=True)
        return str(output_dir.resolve())
    except (SystemExit, Exception):
        # Fall back to legacy behavior if PathManager fails
        pass

    output_dir = Path.cwd() / 'output'
    output_dir.mkdir(parents=True, exist_ok=True)
    return str(output_dir.resolve())


def get_output_path(filename: str) -> str:
    """
    Get the full path for an output file.

    Uses HAGENT_OUTPUT_DIR if set, otherwise uses PathManager to route files
    to HAGENT_CACHE_DIR/inou/logs/ structure.

    Args:
        filename: The name of the output file (must be a relative path within output directory)

    Returns:
        str: Full path to the output file in the output directory

    Raises:
        SystemExit: If filename is an absolute path or tries to escape the output directory
    """
    # Validate filename first (same validation logic as before)
    is_absolute = (
        os.path.isabs(filename)  # Standard absolute path check
        or filename.startswith('~')  # Home directory expansion
        or (len(filename) >= 3 and filename[1:3] == ':\\')  # Windows drive letter (C:\)
        or filename.startswith('../')  # Relative path trying to escape output directory
        or filename == '..'  # Just parent directory reference
    )

    if is_absolute:
        print(f"ERROR: get_output_path() called with invalid path: '{filename}'", file=sys.stderr)
        print('', file=sys.stderr)
        print('API CONSTRAINT VIOLATION:', file=sys.stderr)
        print('get_output_path() only accepts relative paths within the output directory.', file=sys.stderr)
        print('', file=sys.stderr)
        print('Examples of correct usage:', file=sys.stderr)
        print("  get_output_path('my_file.log')           # ✓ filename only", file=sys.stderr)
        print("  get_output_path('subdir/my_file.txt')    # ✓ relative path", file=sys.stderr)
        print('', file=sys.stderr)
        print('Examples of incorrect usage:', file=sys.stderr)
        print("  get_output_path('/tmp/my_file.log')      # ✗ absolute path", file=sys.stderr)
        print("  get_output_path('/Users/name/file.txt')  # ✗ absolute path", file=sys.stderr)
        print("  get_output_path('../escape/file.txt')    # ✗ escapes output directory", file=sys.stderr)
        print("  get_output_path('..')                    # ✗ parent directory reference", file=sys.stderr)
        print('', file=sys.stderr)
        print('If you need to write to an absolute path, use that path directly', file=sys.stderr)
        print('instead of get_output_path().', file=sys.stderr)
        sys.exit(1)

    return str((Path(get_output_dir()) / filename).resolve())
