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




