#!/usr/bin/env python3
"""
HintsGenerator class for finding Chisel code hints for bug fixing.

This class encapsulates the complex logic for generating hints about relevant
Chisel code that needs modification, using both module_finder and fallback approaches.
"""

import os
import tempfile
import subprocess
import re
from typing import List, Dict, Any


class HintsGenerator:
    """
    Generates hints about relevant Chisel code for bug fixing.

    This class manages the complex process of:
    1. Using module_finder to locate relevant Chisel modules
    2. Handling Docker vs local file access
    3. Managing temporary files for Docker content
    4. Providing metadata fallback when module_finder fails
    5. Extracting actual code content from hits
    """

    def __init__(self, module_finder, builder=None, debug: bool = True):
        """
        Initialize HintsGenerator.

        Args:
            module_finder: Module_finder instance for finding relevant modules
            builder: Builder instance for Docker operations
            debug: Enable debug output
        """
        self.module_finder = module_finder
        self.builder = builder
        self.debug = debug

        # State for temporary file management
        self.temp_files = []
        self.temp_to_original = {}

    def find_hints(self, bug_info, all_files: List[str], docker_container: str) -> Dict[str, Any]:
        """
        Find hints for a specific bug using module_finder and fallbacks.

        Args:
            bug_info: BugInfo object containing bug details
            all_files: List of all available Chisel files (local + docker)
            docker_container: Docker container name for file access

        Returns:
            Dict with 'hints', 'source', and 'success' keys
        """
        try:
            # Step 1: Prepare files for module_finder (handle Docker files)
            prepared_files = self._prepare_files_for_module_finder(all_files)

            if self.debug:
                print(f'✅ Prepared {len(prepared_files)} files for module_finder')

            # Step 2: Try module_finder first
            module_finder_result = self._try_module_finder(prepared_files, bug_info.module_name, bug_info.unified_diff)

            if module_finder_result['success']:
                # Extract actual code content from hits
                code_hints = self._extract_code_from_hits(module_finder_result['hits'], docker_container)

                final_hints = f'// Module finder results for {bug_info.module_name}\n\n{code_hints}'

                return {'hints': final_hints, 'source': 'module_finder', 'success': True, 'hits': module_finder_result['hits']}

            # Step 3: Try metadata fallback if module_finder failed
            if self.debug:
                print('🔄 Module_finder failed or found no good hits - trying metadata fallback...')

            fallback_hints = self._get_metadata_fallback_hints(docker_container, bug_info.file_name, bug_info.unified_diff)

            if fallback_hints.strip():
                return {'hints': fallback_hints, 'source': 'metadata_fallback', 'success': True, 'hits': []}

            # Step 4: No hints available
            return {
                'hints': f'// No hints found for {bug_info.module_name} via module_finder or metadata fallback',
                'source': 'none',
                'success': False,
                'hits': [],
            }

        except Exception as e:
            print(f'❌ HintsGenerator failed: {e}')
            return {'hints': f'// HintsGenerator error: {str(e)}', 'source': 'error', 'success': False, 'hits': []}
        finally:
            # Always clean up temp files
            self.cleanup_temp_files()

    def _try_module_finder(self, prepared_files: List[str], module_name: str, verilog_diff: str) -> Dict[str, Any]:
        """Try to find modules using module_finder."""
        try:
            hits = self.module_finder.find_modules(
                scala_files=prepared_files, verilog_module=module_name, verilog_diff=verilog_diff
            )

            if self.debug:
                print(f'✅ Module_finder returned {len(hits)} hits')

            # Map temp file paths back to original Docker paths
            mapped_hits = []
            for hit in hits:
                original_path = self.temp_to_original.get(hit.file_name, hit.file_name)
                # Create new hit with original path
                mapped_hit = type(hit)(
                    file_name=original_path,
                    module_name=hit.module_name,
                    start_line=hit.start_line,
                    end_line=hit.end_line,
                    confidence=hit.confidence,
                )
                mapped_hits.append(mapped_hit)

            # Check if we have good quality hits
            if mapped_hits and max(hit.confidence for hit in mapped_hits) >= 0.5:
                return {'success': True, 'hits': mapped_hits}
            else:
                return {'success': False, 'hits': mapped_hits}

        except Exception as e:
            print(f'❌ Module_finder failed: {e}')
            return {'success': False, 'hits': []}

    def _prepare_files_for_module_finder(self, chisel_files: List[str]) -> List[str]:
        """Prepare file list for module_finder (handle Docker files)"""
        prepared_files = []
        self.temp_files = []  # Reset for new operation
        self.temp_to_original = {}  # Reset mappings

        for file_path in chisel_files:
            if file_path.startswith('docker:'):
                try:
                    # Read content from Docker
                    content = self._read_docker_file(file_path)

                    # Create temp file
                    temp_fd, temp_path = tempfile.mkstemp(suffix='.scala', prefix='docker_')
                    with os.fdopen(temp_fd, 'w') as f:
                        f.write(content)

                    self.temp_files.append(temp_path)
                    prepared_files.append(temp_path)

                    # Map temp path back to original for reporting
                    self.temp_to_original[temp_path] = file_path

                except Exception as e:
                    if self.debug:
                        print(f'     ⚠️  Failed to read Docker file {file_path}: {e}')
                    continue
            else:
                # Local file - use as is
                prepared_files.append(file_path)

        return prepared_files

    def _read_docker_file(self, docker_path: str) -> str:
        """Read a file from Docker container using Builder API."""
        # Parse docker path: docker:container_name:file_path
        parts = docker_path.split(':', 2)
        if len(parts) != 3:
            raise ValueError(f'Invalid docker path format: {docker_path}')

        container_name = parts[1]
        file_path = parts[2]

        if self.builder:
            # Use Builder's filesystem to read the file
            return self.builder.filesystem.read_file(file_path)
        else:
            # Fallback to subprocess if no builder available
            cmd = ['docker', 'exec', container_name, 'cat', file_path]
            result = subprocess.run(cmd, capture_output=True, text=True, check=True)
            return result.stdout

    def cleanup_temp_files(self):
        """Clean up temporary files created for Docker content"""
        if hasattr(self, 'temp_files'):
            for temp_file in self.temp_files:
                try:
                    os.unlink(temp_file)
                except OSError:
                    pass
            self.temp_files = []

        # Clear mappings
        self.temp_to_original = {}

    def _extract_code_from_hits(self, hits: List, docker_container: str) -> str:
        """Extract actual Chisel code content from module_finder hits"""
        all_code_hints = []

        for i, hit in enumerate(hits[:5]):  # Top 5 hits to avoid too much context
            try:
                file_path = hit.file_name

                # Handle Docker vs local paths
                if file_path.startswith('docker:'):
                    # Parse docker path: docker:container_name:file_path
                    parts = file_path.split(':', 2)
                    actual_file_path = parts[2]

                    # Read from Docker container using Builder API
                    if self.builder:
                        try:
                            full_content = self.builder.filesystem.read_file(actual_file_path)
                            lines = full_content.split('\n')
                            # Extract specific lines (1-indexed)
                            start_idx = max(0, hit.start_line - 1)
                            end_idx = min(len(lines), hit.end_line)
                            selected_lines = lines[start_idx:end_idx]
                            code_content = '\n'.join(selected_lines).strip()
                        except Exception as e:
                            raise Exception(f'Failed to read file {actual_file_path}: {e}')
                    else:
                        # Fallback to subprocess
                        cmd = ['docker', 'exec', docker_container, 'sed', '-n', f'{hit.start_line},{hit.end_line}p', actual_file_path]
                        result = subprocess.run(cmd, capture_output=True, text=True, check=True)
                        code_content = result.stdout.strip()
                else:
                    # Local file - read directly
                    actual_file_path = file_path
                    try:
                        with open(file_path, 'r') as f:
                            lines = f.readlines()
                            # Extract specific lines (1-indexed)
                            start_idx = max(0, hit.start_line - 1)
                            end_idx = min(len(lines), hit.end_line)
                            selected_lines = lines[start_idx:end_idx]
                            code_content = ''.join(selected_lines).strip()
                    except Exception as local_error:
                        print(f'     ❌ Failed to read local file {file_path}: {local_error}')
                        continue

                if code_content:
                    # Convert Docker absolute path to repository-relative path
                    if file_path.startswith('docker:') and actual_file_path.startswith('/code/workspace/repo/'):
                        relative_path = actual_file_path[len('/code/workspace/repo/') :]
                    else:
                        relative_path = actual_file_path

                    hint_block = f"""
// ========== HIT {i + 1}: {hit.module_name} (confidence: {hit.confidence:.2f}) ==========
// File: {relative_path}
// Lines: {hit.start_line}-{hit.end_line}
{code_content}
// ========== END HIT {i + 1} ==========
"""
                    all_code_hints.append(hint_block)

            except Exception as e:
                if self.debug:
                    print(f'     ❌ Failed to extract code from hit {i + 1}: {e}')
                continue

        return '\n'.join(all_code_hints)

    def _get_metadata_fallback_hints(self, docker_container: str, verilog_file: str, verilog_diff: str) -> str:
        """Get hints using metadata fallback approach"""
        if self.debug:
            print(f'🔄 [METADATA FALLBACK] Starting for {verilog_file}')

        # Parse metadata from RTL
        metadata_result = self._parse_metadata_from_rtl(docker_container, verilog_file, verilog_diff)

        if not metadata_result['success']:
            if self.debug:
                print(f'     ❌ Metadata parsing failed: {metadata_result.get("error", "Unknown error")}')
            return ''

        # Extract hints from mappings
        hints = self._extract_hints_from_metadata(docker_container, metadata_result['file_mappings'])

        if hints.strip():
            if self.debug:
                print('     ✅ [METADATA FALLBACK] Generated hints successfully')
            return hints
        else:
            if self.debug:
                print('     ❌ [METADATA FALLBACK] No hints generated')
            return ''

    def _parse_metadata_from_rtl(self, docker_container: str, verilog_file: str, verilog_diff: str) -> Dict[str, Any]:
        """Parse metadata from RTL files to extract Chisel file:line mappings - copied from original"""
        # Find the RTL file in build_debug
        rtl_path = f'/code/workspace/build/build_dbg/rtl/{verilog_file}'

        try:
            # Check if RTL file exists
            check_cmd = ['docker', 'exec', docker_container, 'test', '-f', rtl_path]
            result = subprocess.run(check_cmd, capture_output=True)
            if result.returncode != 0:
                return {'success': False, 'error': f'RTL file not found: {rtl_path}'}

            # Read RTL content
            read_cmd = ['docker', 'exec', docker_container, 'cat', rtl_path]
            result = subprocess.run(read_cmd, capture_output=True, text=True, check=True)
            rtl_content = result.stdout

            # Parse metadata comments to find file mappings
            file_mappings = {}
            metadata_matches = re.findall(r'(?://|/\*)\s*@\[([^:]+):(\d+):(\d+)\]', rtl_content)

            for file_path, line_num, col_num in metadata_matches:
                if file_path not in file_mappings:
                    file_mappings[file_path] = []
                file_mappings[file_path].append(int(line_num))

            if not file_mappings:
                return {'success': False, 'error': 'No metadata found in RTL file'}

            return {'success': True, 'file_mappings': file_mappings}

        except subprocess.CalledProcessError as e:
            return {'success': False, 'error': f'Command failed: {e}'}
        except Exception as e:
            return {'success': False, 'error': f'Unexpected error: {e}'}

    def _extract_hints_from_metadata(self, docker_container: str, file_mappings: Dict[str, List[int]]) -> str:
        """Extract hints from metadata file mappings - copied from original"""
        all_hints = []

        for file_path, line_numbers in file_mappings.items():
            if not line_numbers:
                continue

            try:
                # Get unique line numbers with context
                unique_lines = sorted(set(line_numbers))
                context_lines = set()

                # Add context around each line
                for line_num in unique_lines:
                    for offset in range(-2, 3):  # ±2 lines of context
                        context_lines.add(max(1, line_num + offset))

                # Read file content with context using Builder API
                if self.builder:
                    try:
                        full_content = self.builder.filesystem.read_file(file_path)
                        file_lines = full_content.split('\n')
                        
                        # Extract context lines
                        extracted_lines = []
                        for line_num in sorted(context_lines):
                            if 1 <= line_num <= len(file_lines):
                                extracted_lines.append(f'{line_num:4}: {file_lines[line_num-1]}')
                        
                        result_stdout = '\n'.join(extracted_lines)
                    except Exception as e:
                        print(f'     ❌ Failed to read file {file_path} with Builder API: {e}')
                        continue
                else:
                    # Fallback to subprocess
                    lines_spec = ','.join(str(line_num) for line_num in sorted(context_lines))
                    cmd = ['docker', 'exec', docker_container, 'sed', '-n', f'{lines_spec}p', file_path]
                    result = subprocess.run(cmd, capture_output=True, text=True, check=True)
                    result_stdout = result.stdout

                if result_stdout.strip():
                    hint_block = f"""
// ========== METADATA HINT: {file_path} ==========
// Referenced lines: {', '.join(map(str, unique_lines))}
{result_stdout.strip()}
// ========== END METADATA HINT ==========
"""
                    all_hints.append(hint_block)

            except Exception as e:
                if self.debug:
                    print(f'     ❌ Failed to extract hints from {file_path}: {e}')
                continue

        return '\n'.join(all_hints)
