#!/usr/bin/env python3
# hagent/tool/docker_diff_applier.py
# See LICENSE file for details

import subprocess
import tempfile
import os
import re
from typing import List, Optional, Tuple
from .chisel_diff_applier import ChiselDiffApplier


class DockerDiffApplier:
    """
    Applies unified diffs to Chisel files located in Docker containers.
    
    This tool combines the ChiselDiffApplier with Docker file operations to:
    1. Find target files in Docker containers
    2. Apply diffs using the existing ChiselDiffApplier
    3. Write the changes back to the container
    """
    
    def __init__(self, container_name: str):
        self.container_name = container_name
        self.applier = ChiselDiffApplier()
    
    def fix_file_permissions(self, file_path: str) -> bool:
        """Fix file permissions to ensure readability"""
        try:
            # Try to fix permissions as root first, then as user
            subprocess.run(['docker', 'exec', self.container_name, 'chmod', '644', file_path], 
                         capture_output=True, check=True)
            subprocess.run(['docker', 'exec', self.container_name, 'chown', 'user:guser', file_path], 
                         capture_output=True, check=True)
            return True
        except subprocess.CalledProcessError:
            # If that fails, try as root
            try:
                subprocess.run(['docker', 'exec', '-u', 'root', self.container_name, 'chmod', '644', file_path], 
                             capture_output=True, check=True)
                subprocess.run(['docker', 'exec', '-u', 'root', self.container_name, 'chown', 'user:guser', file_path], 
                             capture_output=True, check=True)
                return True
            except subprocess.CalledProcessError:
                return False
    
    def find_file_in_container(self, filename: str, base_path: str = "/code") -> List[str]:
        """Find all occurrences of a file in the Docker container"""
        try:
            cmd = ['docker', 'exec', '-u', 'user', self.container_name, 'find', base_path, '-name', filename, '-type', 'f']
            result = subprocess.run(cmd, capture_output=True, text=True, check=True)
            paths = [p.strip() for p in result.stdout.strip().split('\n') if p.strip()]
            return paths
        except subprocess.CalledProcessError as e:
            print(f"❌ Error searching for file in Docker: {e}")
            return []
    
    def read_file_from_container(self, file_path: str) -> Optional[str]:
        """Read file content from Docker container"""
        try:
            cmd = ['docker', 'exec', '-u', 'user', self.container_name, 'cat', file_path]
            result = subprocess.run(cmd, capture_output=True, text=True, check=True)
            return result.stdout
        except subprocess.CalledProcessError as e:
            print(f"❌ Permission error reading file. Attempting to fix permissions...")
            # Try to fix permissions and retry
            if self.fix_file_permissions(file_path):
                try:
                    cmd = ['docker', 'exec', '-u', 'user', self.container_name, 'cat', file_path]
                    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
                    print(f"✅ Successfully read file after permission fix")
                    return result.stdout
                except subprocess.CalledProcessError:
                    pass
            print(f"❌ Error reading file from Docker: {e}")
            return None
    
    def write_file_to_container(self, file_path: str, content: str) -> bool:
        """Write file content to Docker container"""
        try:
            # Create temporary file
            with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.scala') as tmp_file:
                tmp_file.write(content)
                tmp_path = tmp_file.name
            
            # Use docker cp to write directly to target location
            subprocess.run(['docker', 'cp', tmp_path, f"{self.container_name}:{file_path}"], check=True)
            
            # Try to fix permissions as user first, then as root if needed
            try:
                subprocess.run(['docker', 'exec', '-u', 'user', self.container_name, 'chmod', '644', file_path], 
                             capture_output=True, check=True)
                subprocess.run(['docker', 'exec', '-u', 'user', self.container_name, 'chown', 'user:guser', file_path], 
                             capture_output=True, check=True)
            except subprocess.CalledProcessError:
                print("⚠️ Permission fix as user failed, trying as root...")
                try:
                    subprocess.run(['docker', 'exec', '-u', 'root', self.container_name, 'chmod', '644', file_path], 
                                 capture_output=True, check=True)
                    subprocess.run(['docker', 'exec', '-u', 'root', self.container_name, 'chown', 'user:guser', file_path], 
                                 capture_output=True, check=True)
                    print("✅ Fixed permissions as root")
                except subprocess.CalledProcessError:
                    print("⚠️ Permission fix failed, but file was written successfully")
                    # Don't fail the operation - file was written successfully
            
            # Clean up local temp file
            os.unlink(tmp_path)
            return True
        except subprocess.CalledProcessError as e:
            print(f"❌ Error writing file to Docker: {e}")
            return False
        except Exception as e:
            print(f"❌ Unexpected error writing file: {e}")
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
            print("❌ Could not extract file path from diff")
            return False
        
        filename = os.path.basename(file_path)
        print(f"Applier target: {file_path}")
        
        # Find the file in container
        found_paths = self.find_file_in_container(filename)
        if not found_paths:
            print(f"❌ File '{filename}' not found in container")
            return False
        
        print(f"Found {len(found_paths)} potential file(s):")
        for path in found_paths:
            print(f"  - {path}")
        
        # Use the first match or find best match
        target_path = self._select_best_match(found_paths, file_path)
        print(f"Selected: {target_path}")
        
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
                print("🔍 DRY RUN - Changes that would be applied:")
                print("=" * 60)
                self._show_diff_preview(original_content, modified_content)
                print("=" * 60)
                return True
            
            # Write back to container
            if self.write_file_to_container(target_path, modified_content):
                print(f"✅ Successfully wrote changes to {target_path}")
                return True
            else:
                print(f"❌ Failed to write changes to {target_path}")
                return False
                
        except RuntimeError as e:
            print(f"❌ Error applying diff: {e}")
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
        
        diff = difflib.unified_diff(
            original_lines, 
            modified_lines,
            fromfile="original",
            tofile="modified",
            lineterm=""
        )
        
        for line in diff:
            print(line.rstrip())


def main():
    """CLI interface for the Docker diff applier"""
    import argparse
    
    parser = argparse.ArgumentParser(description='Apply unified diffs to Chisel files in Docker containers')
    parser.add_argument('container', help='Docker container name')
    parser.add_argument('diff_file', help='File containing the unified diff')
    parser.add_argument('--dry-run', action='store_true', help='Show what would be changed without applying')
    
    args = parser.parse_args()
    
    # Read diff content
    try:
        with open(args.diff_file, 'r') as f:
            diff_content = f.read()
    except FileNotFoundError:
        print(f"❌ Diff file not found: {args.diff_file}")
        return 1
    
    # Apply the diff
    applier = DockerDiffApplier(args.container)
    success = applier.apply_diff_to_container(diff_content, args.dry_run)
    return 0 if success else 1


if __name__ == '__main__':
    import sys
    sys.exit(main())