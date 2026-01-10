"""
Bug Injector for Integration Tests

Provides utilities for modifying source code to introduce bugs for testing.
"""

from pathlib import Path
from typing import Dict


def inject_bug(file_path: Path, bug_pattern: Dict[str, str]) -> str:
    """
    Modify source file to introduce a bug.

    Args:
        file_path: Path to source file to modify
        bug_pattern: Dict with 'find' and 'replace' keys
                     Example: {"find": "result_o <= ", "replace": "result_o <= ~"}

    Returns:
        Original file content (for undo)

    Raises:
        FileNotFoundError: If file doesn't exist
        ValueError: If find pattern not found in file
    """
    file_path = Path(file_path)

    if not file_path.exists():
        raise FileNotFoundError(f'File not found: {file_path}')

    # Read original content
    with open(file_path) as f:
        original_content = f.read()

    # Check if pattern exists
    if bug_pattern['find'] not in original_content:
        raise ValueError(f"Pattern '{bug_pattern['find']}' not found in {file_path.name}")

    # Apply bug (replace first occurrence only)
    modified_content = original_content.replace(
        bug_pattern['find'],
        bug_pattern['replace'],
        1,  # Replace only first occurrence
    )

    # Write modified content
    with open(file_path, 'w') as f:
        f.write(modified_content)

    return original_content


def undo_bug(file_path: Path, bug_pattern: Dict[str, str]) -> None:
    """
    Revert bug modification by undoing the replacement.

    Args:
        file_path: Path to source file to revert
        bug_pattern: Same pattern used in inject_bug

    Raises:
        FileNotFoundError: If file doesn't exist
        ValueError: If replace pattern not found (bug not injected)
    """
    file_path = Path(file_path)

    if not file_path.exists():
        raise FileNotFoundError(f'File not found: {file_path}')

    # Read current content
    with open(file_path) as f:
        content = f.read()

    # Check if bug is present
    if bug_pattern['replace'] not in content:
        raise ValueError(f"Bug pattern '{bug_pattern['replace']}' not found in {file_path.name}. Was bug already undone?")

    # Undo bug (reverse the replacement)
    reverted_content = content.replace(
        bug_pattern['replace'],
        bug_pattern['find'],
        1,  # Revert only first occurrence
    )

    # Write reverted content
    with open(file_path, 'w') as f:
        f.write(reverted_content)


def restore_file(file_path: Path, original_content: str) -> None:
    """
    Restore file to original content.

    Args:
        file_path: Path to file to restore
        original_content: Original file content from inject_bug()
    """
    file_path = Path(file_path)

    with open(file_path, 'w') as f:
        f.write(original_content)
