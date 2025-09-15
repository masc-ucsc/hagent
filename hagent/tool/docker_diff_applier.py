#!/usr/bin/env python3
# hagent/tool/docker_diff_applier.py
# See LICENSE file for details

import tempfile
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
            content = self.builder.filesystem.read_file(file_path)
            return content
        except Exception as e:
            print('❌ Permission error reading file. Attempting to fix permissions...')
            # Try to fix permissions and retry
            if self.fix_file_permissions(file_path):
                try:
                    content = self.builder.filesystem.read_file(file_path)
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
            self.builder.filesystem.write_file(file_path, content)
            
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

    def apply_diff_to_container(self, diff_content: str, dry_run: bool = False) -> bool:
        """
        Apply a unified diff to files in the Docker container

        Args:
            diff_content: The unified diff as a string
            dry_run: If True, only show what would be changed without applying

        Returns:
            True if successful, False otherwise
        """
        # print(f"🐳 Applying diff to Docker container: {self.container_name}")

        # Parse file path from diff
        file_path = self.parse_diff_file_path(diff_content)
        if not file_path:
            print('❌ Could not extract file path from diff')
            return False

        filename = os.path.basename(file_path)
        print(f'Applier target: {file_path}')

        # Find the file in container
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

        # print(f"📖 Read {len(original_content.splitlines())} lines from {target_path}")

        # Apply the diff
        try:
            modified_content = self.applier.apply_diff(diff_content, original_content)
            # print("✅ Diff applied successfully")

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

        # Prefer exact path match
        for path in found_paths:
            if path.endswith(target_path):
                return path

        # Fallback to first match
        return found_paths[0]

    def _show_diff_preview(self, original: str, modified: str):
        """Show a preview of changes"""
        import difflib

        original_lines = original.splitlines(keepends=True)
        modified_lines = modified.splitlines(keepends=True)

        diff = difflib.unified_diff(original_lines, modified_lines, fromfile='original', tofile='modified', lineterm='')

        for line in diff:
            print(line.rstrip())


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
