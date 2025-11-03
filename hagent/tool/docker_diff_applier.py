#!/usr/bin/env python3
# hagent/tool/docker_diff_applier.py
# See LICENSE file for details

import os
from typing import List, Optional
from .chisel_diff_applier import ChiselDiffApplier
from hagent.inou.builder import Builder


class DockerDiffApplier:
    """
    Applies unified diffs to Chisel files located in Docker containers.

    This tool combines the ChiselDiffApplier with Docker file operations to:
    1. Find target files in Docker containers
    2. Apply diffs using the existing ChiselDiffApplier
    3. Write the changes back to the container
    """

    def __init__(self, builder: Builder):
        self.builder = builder
        self.applier = ChiselDiffApplier()

    def fix_file_permissions(self, file_path: str) -> bool:
        """Fix file permissions to ensure readability"""
        try:
            # Try to fix permissions as root first, then as user
            exit_code, _, _ = self.builder.run_cmd(f'chmod 644 {file_path}')
            if exit_code != 0:
                return False
            exit_code, _, _ = self.builder.run_cmd(f'chown user:guser {file_path}')
            return exit_code == 0
        except Exception:
            return False

    def find_file_in_container(self, filename: str, base_path: str = '/code') -> List[str]:
        """Find all occurrences of a file in the Docker container"""
        try:
            exit_code, stdout, stderr = self.builder.run_cmd(f'find {base_path} -name {filename} -type f')
            if exit_code != 0:
                print(f'❌ Error searching for file in Docker: {stderr}')
                return []
            paths = [p.strip() for p in stdout.strip().split('\n') if p.strip()]
            return paths
        except Exception as e:
            print(f'❌ Error searching for file in Docker: {e}')
            return []

    def read_file_from_container(self, file_path: str) -> Optional[str]:
        """Read file content from Docker container"""
        try:
            # Use Builder's filesystem read method
            content = self.builder.filesystem.read_text(file_path)
            return content
        except Exception as e:
            print('❌ Permission error reading file. Attempting to fix permissions...')
            # Try to fix permissions and retry
            if self.fix_file_permissions(file_path):
                try:
                    content = self.builder.filesystem.read_text(file_path)
                    print('✅ Successfully read file after permission fix')
                    return content
                except Exception:
                    pass
            print(f'❌ Error reading file from Docker: {e}')
            return None

    def write_file_to_container(self, file_path: str, content: str) -> bool:
        """Write file content to Docker container"""
        try:
            # Use Builder's filesystem write method
            self.builder.filesystem.write_text(file_path, content)

            # Try to fix permissions
            self.fix_file_permissions(file_path)

            return True
        except Exception as e:
            print(f'❌ Error writing file to Docker: {e}')
            return False

    def parse_diff_file_path(self, diff_content: str) -> Optional[str]:
        """Extract the target file path from unified diff header"""
        lines = diff_content.strip().split('\n')
        for line in lines:
            if line.startswith('--- a/'):
                return line[6:]  # Remove '--- a/'
            elif line.startswith('+++ b/'):
                return line[6:]  # Remove '+++ b/'
        return None

    def apply_diff_to_container(self, diff_content: str, target_file_path: str = None, dry_run: bool = False) -> bool:
        """
        Apply a unified diff to files in the Docker container

        Args:
            diff_content: The unified diff as a string
            target_file_path: Optional - exact file path to apply diff to (from hints)
            dry_run: If True, only show what would be changed without applying

        Returns:
            True if successful, False otherwise
        """
        # Parse multi-file diff into separate sections
        file_sections = self._parse_multi_file_diff(diff_content)

        if not file_sections:
            print('❌ Could not parse any file sections from diff')
            return False

        print(f'📋 Found {len(file_sections)} file section(s) in diff')

        all_success = True

        # Apply each file section separately
        for i, (file_path, section_diff) in enumerate(file_sections, 1):
            print(f'\n🔧 [{i}/{len(file_sections)}] Applying diff to: {file_path}')
            success = self._apply_single_file_diff(file_path, section_diff, target_file_path, dry_run)
            if not success:
                print(f'❌ Failed to apply diff to {file_path}')
                all_success = False
            else:
                print(f'✅ Successfully applied diff to {file_path}')

        return all_success

    def _parse_multi_file_diff(self, diff_content: str) -> List[tuple]:
        """
        Parse a multi-file diff into separate sections

        Returns:
            List of tuples (file_path, section_diff)
        """
        lines = diff_content.strip().split('\n')
        sections = []
        current_section = []
        current_file = None

        i = 0
        while i < len(lines):
            line = lines[i]

            # Look for diff headers
            if line.startswith('--- a/'):
                # If we have a current section, save it
                if current_file and current_section:
                    section_diff = '\n'.join(current_section)
                    sections.append((current_file, section_diff))

                # Start new section
                current_file = line[6:]  # Remove '--- a/'
                current_section = [line]

                # Look for the corresponding '+++ b/' line
                if i + 1 < len(lines) and lines[i + 1].startswith('+++ b/'):
                    current_section.append(lines[i + 1])
                    i += 1
            else:
                # Add line to current section if we have one
                if current_file:
                    current_section.append(line)

            i += 1

        # Don't forget the last section
        if current_file and current_section:
            section_diff = '\n'.join(current_section)
            sections.append((current_file, section_diff))

        return sections

    def _apply_single_file_diff(
        self, file_path: str, section_diff: str, hint_file_path: str = None, dry_run: bool = False
    ) -> bool:
        """Apply a single-file diff section

        Args:
            file_path: File path from diff header (e.g., src/main/scala/components/alu.scala)
            section_diff: The diff content
            hint_file_path: Optional - exact file path from hints (e.g., /code/workspace/repo/src/main/scala/components/alu.scala)
            dry_run: Whether to just preview changes

        Returns:
            True if successful
        """
        filename = os.path.basename(file_path)
        print(f'Applier target: {file_path}')

        # If we have a hint file path (from module finder), use it directly!
        if hint_file_path and os.path.isabs(hint_file_path):
            print(f'🎯 [APPLIER] Using file path from hints: {hint_file_path}')
            target_path = hint_file_path
        else:
            # Fallback: search for file (old behavior)
            found_paths = self.find_file_in_container(filename)
            if not found_paths:
                print(f"❌ File '{filename}' not found in container")
                return False

            print(f'Found {len(found_paths)} potential file(s):')
            for path in found_paths:
                print(f'  - {path}')

            # Use the first match or find best match
            target_path = self._select_best_match(found_paths, file_path)
            print(f'Selected: {target_path}')

        # Read current file content
        original_content = self.read_file_from_container(target_path)
        if original_content is None:
            return False

        # Pre-verify the target line exists (skip for Scala/Chisel - let applier handle it)
        # Only do strict verification for Verilog files
        if file_path.endswith('.sv') or file_path.endswith('.v'):
            if not self._verify_target_line_exists(section_diff, original_content):
                print('❌ Target line for diff not found in Verilog file - diff cannot be applied')
                return False
        else:
            # For Scala/Chisel files, just warn but let the diff applier try
            if not self._verify_target_line_exists(section_diff, original_content):
                print('⚠️  Pre-verification warning: Some lines may not match exactly')
                print('    Attempting to apply diff anyway (letting patch handle fuzzy matching)...')

        # Apply the diff
        try:
            modified_content = self.applier.apply_diff(section_diff, original_content)

            # Post-verify the change was applied (strict for Verilog, lenient for Scala)
            if not self._verify_diff_applied(section_diff, modified_content):
                if file_path.endswith('.sv') or file_path.endswith('.v'):
                    print('❌ Diff was not correctly applied - verification failed')
                    return False
                else:
                    print('⚠️  Post-verification: Could not verify all changes, but proceeding...')
                    # For Scala, proceed anyway - compilation will catch any issues

            if dry_run:
                print('🔍 DRY RUN - Changes that would be applied:')
                print('=' * 60)
                self._show_diff_preview(original_content, modified_content)
                print('=' * 60)
                return True

            # Write back to container
            if self.write_file_to_container(target_path, modified_content):
                print(f'✅ Successfully wrote changes to {target_path}')
                return True
            else:
                print(f'❌ Failed to write changes to {target_path}')
                return False

        except RuntimeError as e:
            print(f'❌ Error applying diff: {e}')
            return False

    def _select_best_match(self, found_paths: List[str], target_path: str) -> str:
        """Select the best matching file from found paths"""
        if len(found_paths) == 1:
            return found_paths[0]

        # Priority prefixes (prefer /code/workspace/repo/ over other paths)
        priority_prefixes = [
            '/code/workspace/repo/',  # Primary codebase
            '/code/workspace/',  # Workspace files
            '/code/',  # Any code directory
        ]

        # First, try exact path match WITH priority
        exact_matches = [p for p in found_paths if p.endswith(target_path)]
        if exact_matches:
            # Apply priority to exact matches
            for prefix in priority_prefixes:
                for path in exact_matches:
                    if path.startswith(prefix):
                        return path
            # If no priority match, return first exact match
            return exact_matches[0]

        # If no exact path match, use priority-based selection
        for prefix in priority_prefixes:
            for path in found_paths:
                if path.startswith(prefix):
                    return path

        # Fallback to first match (if no priority match found)
        return found_paths[0]

    def _show_diff_preview(self, original: str, modified: str):
        """Show a preview of changes"""
        import difflib

        original_lines = original.splitlines(keepends=True)
        modified_lines = modified.splitlines(keepends=True)

        diff = difflib.unified_diff(original_lines, modified_lines, fromfile='original', tofile='modified', lineterm='')

        for line in diff:
            print(line.rstrip())

    def _verify_target_line_exists(self, diff_content: str, file_content: str) -> bool:
        """Verify that the line to be removed exists in the file (with flexible matching for Verilog)"""
        lines = diff_content.strip().split('\n')
        removal_lines = []

        for line in lines:
            if line.startswith('-') and not line.startswith('---'):  # Exclude diff headers
                removal_line = line[1:].strip()  # Remove '-' and strip whitespace
                if removal_line:  # Skip empty lines
                    removal_lines.append(removal_line)

        if not removal_lines:
            return True  # No removals to verify

        file_lines = file_content.splitlines()

        print(f'🔍 [VERIFY] Looking for {len(removal_lines)} removal line(s) in file...')

        for removal_line in removal_lines:
            found = False
            for i, file_line in enumerate(file_lines):
                # Flexible matching for Verilog: normalize whitespace around key patterns
                normalized_file_line = self._normalize_verilog_line(file_line.strip())
                normalized_removal_line = self._normalize_verilog_line(removal_line)

                if normalized_file_line == normalized_removal_line:
                    print(f'     ✅ Found removal line at line {i + 1}: {file_line.strip()}')
                    found = True
                    break

            if not found:
                print(f'     ❌ Removal line NOT found: {removal_line}')
                print('     🔍 Looking for lines containing key parts...')
                # Try to find lines with key parts of the removal line
                key_parts = removal_line.split()
                for i, file_line in enumerate(file_lines):
                    if all(part in file_line for part in key_parts if len(part) > 2):
                        print(f'         Line {i + 1}: {file_line.strip()}')
                return False

        return True

    def _verify_diff_applied(self, diff_content: str, modified_content: str) -> bool:
        """Verify that the diff was correctly applied by checking for addition lines"""
        lines = diff_content.strip().split('\n')
        addition_lines = []

        for line in lines:
            if line.startswith('+') and not line.startswith('+++'):  # Exclude diff headers
                addition_line = line[1:].strip()  # Remove '+' and strip whitespace
                if addition_line:  # Skip empty lines
                    addition_lines.append(addition_line)

        if not addition_lines:
            return True  # No additions to verify

        file_lines = modified_content.splitlines()

        print(f'🔍 [VERIFY] Checking that {len(addition_lines)} addition line(s) are present...')

        for addition_line in addition_lines:
            found = False
            for i, file_line in enumerate(file_lines):
                # Flexible matching for Verilog: normalize whitespace around key patterns
                normalized_file_line = self._normalize_verilog_line(file_line.strip())
                normalized_addition_line = self._normalize_verilog_line(addition_line)

                if normalized_file_line == normalized_addition_line:
                    print(f'     ✅ Found addition line at line {i + 1}: {file_line.strip()}')
                    found = True
                    break

            if not found:
                print(f'     ❌ Addition line NOT found: {addition_line}')
                return False

        return True

    def _normalize_verilog_line(self, line: str) -> str:
        """Normalize a Verilog line for flexible matching"""
        import re

        # Remove extra whitespace around operators and normalize spacing
        line = re.sub(r'\s*=\s*', ' = ', line)  # Normalize around '='
        line = re.sub(r'\s*==\s*', ' == ', line)  # Normalize around '=='
        line = re.sub(r'\s+', ' ', line)  # Collapse multiple spaces
        line = line.strip()
        return line


def main():
    """CLI interface for the Docker diff applier"""
    import argparse

    parser = argparse.ArgumentParser(description='Apply unified diffs to Chisel files in Docker containers')
    parser.add_argument('diff_file', help='File containing the unified diff')
    parser.add_argument('--dry-run', action='store_true', help='Show what would be changed without applying')

    args = parser.parse_args()

    # Read diff content
    try:
        with open(args.diff_file, 'r') as f:
            diff_content = f.read()
    except FileNotFoundError:
        print(f'❌ Diff file not found: {args.diff_file}')
        return 1

    # Create builder
    builder = Builder()
    if not builder.setup():
        print(f'❌ Builder setup failed: {builder.get_error()}')
        return 1

    # Apply the diff
    applier = DockerDiffApplier(builder)
    success = applier.apply_diff_to_container(diff_content, args.dry_run)
    return 0 if success else 1


if __name__ == '__main__':
    import sys

    sys.exit(main())
