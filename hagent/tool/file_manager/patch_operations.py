import os
import difflib
from datetime import datetime
from typing import Dict, Any

from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString


def process_multiline_strings(obj):
    """
    Recursively converts strings containing newlines into a LiteralScalarString
    so that ruamel.yaml outputs them in literal block style.
    """
    if isinstance(obj, dict):
        return {k: process_multiline_strings(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [process_multiline_strings(item) for item in obj]
    elif isinstance(obj, str) and '\n' in obj and obj.strip():
        return LiteralScalarString(obj)
    return obj


class PatchOperations:
    """Handles all patch and diff operations including generation, application, and YAML export."""

    def __init__(self, file_manager):
        """Initialize with reference to main File_manager instance."""
        self.fm = file_manager

    def get_diff(self, filename: str) -> str:
        """Return the unified diff (as text) for a single tracked file."""
        original_content_str = ''

        # Resolve filename to absolute path for consistent lookups
        absolute_filename = self.fm._files._resolve_container_path(filename)

        # Check if file was tracked via track_file or is in a tracked directory
        # Get original content from reference container
        reference_container = self.fm._docker.get_reference_container()
        print("HERE1")
        if not reference_container:
            return ''
        print(f"HERE2 path:{absolute_filename}")
        original_content_str = self.fm._files.get_file_content(absolute_filename, container=reference_container)
        print(f"HERE3 txt:{original_content_str}")
        if not original_content_str and self.fm.error_message:
            return ''
        print("HERE4")

        # Get modified content from main container
        modified_content_str = self.fm._files.get_file_content(absolute_filename)

        diff_lines = difflib.unified_diff(
            original_content_str.splitlines(keepends=True),
            modified_content_str.splitlines(keepends=True),
            fromfile=f'a/{filename}',
            tofile=f'b/{filename}',
        )
        return ''.join(diff_lines)

    def get_patch_dict(self) -> Dict[str, Any]:
        """Generate a dictionary of new files and patched files."""
        if self.fm._state != 'CONFIGURED':
            self.fm.error_message = 'get_patch_dict must be called after setup().'
            return {}

        patches = {'full': [], 'patch': []}

        # Collect all tracked files from different sources
        all_tracked_files = set()

        # Add files from _tracked_individual_files (track_file approach) - already absolute paths
        all_tracked_files.update(self.fm._files._tracked_individual_files)

        # Add files from tracked directories (track_dir approach) - discover dynamically
        for dir_entry in self.fm._files._tracked_dirs:
            dir_path = dir_entry['path']
            ext_filter = dir_entry['ext']

            # Find files in this tracked directory
            exit_code, out, stderr = self.fm._docker.run(f'find "{dir_path}" -type f', quiet=True)
            if exit_code != 0:
                # Directory might not exist anymore, skip it
                continue

            files = [f.strip() for f in out.strip().split('\n') if f.strip()]
            for file_path in files:
                # Apply extension filter if specified
                if ext_filter and not file_path.endswith(ext_filter):
                    continue
                # Normalize path to remove redundant "./"
                normalized_path = os.path.normpath(file_path)
                all_tracked_files.add(normalized_path)

        for absolute_file_path in all_tracked_files:
            modified_content_str = self.fm._files.get_file_content(absolute_file_path)
            if not modified_content_str and self.fm.error_message:  # Likely binary file
                patches['full'].append({'filename': absolute_file_path, 'contents': '[Binary File]'})
                self.fm.error_message = ''  # Clear error for next iteration
                continue

            # Check if file is tracked via track_file (these have original content)
            is_explicitly_tracked = absolute_file_path in self.fm._files._tracked_individual_files

            # Check if file is in a tracked directory
            is_in_tracked_dir = self.fm._files._is_file_in_tracked_dir(absolute_file_path)

            if is_explicitly_tracked or is_in_tracked_dir:
                # File is tracked, try to create a diff
                if is_in_tracked_dir and not is_explicitly_tracked:
                    # File is in tracked directory - check if it exists in reference container first
                    reference_container = self.fm._docker.get_reference_container()
                    if reference_container:
                        ref_content = self.fm._files.get_file_content(absolute_file_path, container=reference_container)
                        if not ref_content and self.fm.error_message:
                            # File doesn't exist in reference, treat as new file
                            patches['full'].append({'filename': absolute_file_path, 'contents': modified_content_str})
                            self.fm.error_message = ''  # Clear error
                            continue
                    else:
                        # No reference container, treat as new file
                        patches['full'].append({'filename': absolute_file_path, 'contents': modified_content_str})
                        continue

                # Create diff for tracked file
                diff = self.get_diff(absolute_file_path)
                if not diff:  # No changes detected
                    continue

                # Get original file size for comparison
                original_len = 0
                if absolute_file_path in self.fm._files._tracked_individual_files or self.fm._files._is_file_in_tracked_dir(
                    absolute_file_path
                ):
                    # Get size from reference container
                    reference_container = self.fm._docker.get_reference_container()
                    if reference_container:
                        original_content = self.fm._files.get_file_content(absolute_file_path, container=reference_container)
                        original_len = len(original_content.encode('utf-8')) if original_content else 0

                # Add as full if diff is large or file is small
                if original_len == 0 or (len(diff) / original_len > 0.25):
                    patches['full'].append({'filename': absolute_file_path, 'contents': modified_content_str})
                else:
                    patches['patch'].append({'filename': absolute_file_path, 'diff': diff})
            else:
                # This is a completely new file not in any tracked location
                patches['full'].append({'filename': absolute_file_path, 'contents': modified_content_str})

        return patches

    def patch_file(self, container_path: str, patch_content: str) -> bool:
        """Apply a unified diff patch to a file in the container."""
        if self.fm._state != 'CONFIGURED':
            self.fm.error_message = 'patch_file must be called after setup().'
            return False

        try:
            # Create a temporary patch file in the container
            temp_patch_path = (
                f'/tmp/patch_{len(self.fm._files._tracked_individual_files) + len(self.fm._files._tracked_dirs)}.patch'
            )

            # Write patch content to temporary file using echo and redirection

            # Write patch to temp file
            exit_code, stdout, stderr = self.fm._docker.run(f"cat > {temp_patch_path} << 'EOF'\n{patch_content}\nEOF")
            if exit_code != 0:
                self.fm.error_message = f'Failed to create patch file: {stderr}'
                return False

            # Apply the patch
            exit_code, stdout, stderr = self.fm._docker.run(f'patch -p1 < {temp_patch_path}', container_path='.')

            # Clean up temporary patch file
            self.fm._docker.run(f'rm -f {temp_patch_path}')

            if exit_code != 0:
                self.fm.error_message = f'Failed to apply patch: {stderr}'
                return False

            print(f"Successfully applied patch to '{container_path}'")
            return True

        except Exception as e:
            self.fm.error_message = f'Failed to patch file {container_path}: {e}'
            return False

    def apply_line_patch(self, container_path: str, line_number: int, old_line: str, new_line: str) -> bool:
        """Apply a simple line replacement patch to a file in the container."""
        if self.fm._state != 'CONFIGURED':
            self.fm.error_message = 'apply_line_patch must be called after setup().'
            return False

        # Check if file exists
        if not self.fm._files._check_file_exists(container_path):
            self.fm.error_message = f'File not found: {container_path}'
            return False

        try:
            # Get current file content
            current_content = self.fm._files.get_file_content(container_path)
            if not current_content and self.fm.error_message:
                return False

            lines = current_content.splitlines()

            # Validate line number
            if line_number < 1 or line_number > len(lines):
                self.fm.error_message = f'Line number {line_number} is out of range (file has {len(lines)} lines)'
                return False

            # Check if the old line matches (with stripped whitespace comparison)
            actual_line = lines[line_number - 1]
            if old_line.strip() != actual_line.strip():
                self.fm.error_message = f'Line {line_number} does not match expected content.\nExpected: "{old_line.strip()}"\nActual: "{actual_line.strip()}"'
                return False

            # Replace the line
            lines[line_number - 1] = new_line
            modified_content = '\n'.join(lines)

            # Write the modified content back to the file
            temp_file_path = f'/tmp/modified_{os.path.basename(container_path)}'

            # Write content to temp file with proper escaping
            exit_code, stdout, stderr = self.fm._docker.run(f"cat > {temp_file_path} << 'EOF'\n{modified_content}\nEOF")
            if exit_code != 0:
                self.fm.error_message = f'Failed to create temporary file: {stderr}'
                return False

            # Move temp file to target location
            full_container_path = self.fm._files._resolve_container_path(container_path)
            exit_code, stdout, stderr = self.fm._docker.run(f'mv {temp_file_path} {full_container_path}')
            if exit_code != 0:
                self.fm.error_message = f'Failed to replace file: {stderr}'
                return False

            print(f"Successfully patched line {line_number} in '{container_path}'")
            return True

        except Exception as e:
            self.fm.error_message = f'Failed to apply line patch to {container_path}: {e}'
            return False

    def save_patches(self, host_path: str, name: str) -> bool:
        """Dump current patch-dict to YAML at host_path."""
        patch_dict = self.get_patch_dict()
        if not patch_dict:
            return False

        try:
            yaml = YAML()
            data = {}
            if os.path.exists(host_path):
                with open(host_path, 'r') as f:
                    data = yaml.load(f) or {}

            # Add metadata and process for literal block style
            patch_with_meta = {
                'metadata': {'timestamp': datetime.utcnow().isoformat(), 'image': self.fm.image},
                'patches': process_multiline_strings(patch_dict),
            }
            data[name] = patch_with_meta

            with open(host_path, 'w') as f:
                yaml.dump(data, f)
            return True
        except Exception as e:
            self.fm.error_message = f'Failed to save patches to YAML: {e}'
            return False

    def load_patches(self, host_path: str) -> bool:
        """(Not Implemented) Reads a patch YAML and applies it."""
        self.fm.error_message = 'load_patches is not yet implemented.'
        return False
