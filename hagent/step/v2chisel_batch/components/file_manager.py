"""
FileManager component for v2chisel_batch refactoring.

This component handles all file finding, reading, and temporary file management
operations for both local and Docker-based file systems.
"""

from typing import Dict
import glob
import tempfile
import os


class FileManager:
    """
    Handles file finding, reading, and temporary file management.

    This component is responsible for:
    1. Finding Chisel files in Docker containers with filtering
    2. Finding Verilog files in Docker containers
    3. Reading file content from Docker containers
    4. Preparing files for module finder with temp file management
    5. Cleaning up temporary files
    """

    def __init__(self, builder, debug: bool = True):
        """
        Initialize FileManager.

        Args:
            builder: Builder instance for Docker/local operations
            debug: Enable debug output
        """
        self.builder = builder
        self.debug = debug
        self.temp_files = []
        self.temp_to_original = {}

    def find_chisel_files_docker_filtered(self, container_name: str, docker_patterns: list, module_name: str = None) -> list:
        """
        Find Chisel files inside Docker container with smart filtering.

        Args:
            container_name: Docker container name
            docker_patterns: List of search patterns
            module_name: Optional module name for filtering

        Returns:
            List of found Chisel file paths
        """
        if self.debug:
            print(f'[DEBUG] Searching for Chisel files for module: {module_name}')

        docker_files = []

        for pattern in docker_patterns:
            if self.debug:
                print(f'  🐳 Docker pattern: {pattern}')

            try:
                # OPTIMIZATION: Search for files containing the module name first
                if module_name:
                    if self.debug:
                        print(f'  🔍 Pre-filtering for module: {module_name}')

                    # Use builder.run_cmd instead of subprocess
                    find_cmd = f"find {pattern} -name '*.scala' -type f -exec grep -il 'class.*{module_name}\\|object.*{module_name}' {{}} \\;"
                    exit_code, stdout, stderr = self.builder.run_cmd(find_cmd)

                    if exit_code == 0:
                        files = [f.strip() for f in stdout.split('\n') if f.strip()]
                        if self.debug:
                            print(f'     ✅ Found {len(files)} files matching "{module_name}"')

                        for file_path in files:
                            docker_path = f'docker:{container_name}:{file_path}'
                            if docker_path not in docker_files:
                                docker_files.append(docker_path)
                    else:
                        if self.debug:
                            print(f'     ⚠️  Module-specific search failed: {stderr}')

                # Fallback: Find all Scala files if module search fails or no module specified
                if not module_name or exit_code != 0:
                    find_cmd = f"find {pattern} -name '*.scala' -type f"
                    exit_code, stdout, stderr = self.builder.run_cmd(find_cmd)

                    if exit_code == 0:
                        files = [f.strip() for f in stdout.split('\n') if f.strip()]
                        if self.debug:
                            print(f'     ✅ Found {len(files)} Scala files')

                        for file_path in files:
                            docker_path = f'docker:{container_name}:{file_path}'
                            if docker_path not in docker_files:
                                docker_files.append(docker_path)
                    else:
                        if self.debug:
                            print(f'     ❌ Find command failed: {stderr}')

            except Exception as e:
                if self.debug:
                    print(f'     ❌ Error searching pattern {pattern}: {str(e)}')

        if self.debug:
            print(f'🐳 Found {len(docker_files)} total Chisel files in Docker')

        return docker_files

    def find_chisel_files_docker(self, container_name: str, docker_patterns: list) -> list:
        """
        Legacy method - use filtered version instead.

        Args:
            container_name: Docker container name
            docker_patterns: List of search patterns

        Returns:
            List of found Chisel file paths
        """
        return self.find_chisel_files_docker_filtered(container_name, docker_patterns)

    def find_verilog_files_in_docker(self, container_name: str, module_name: str) -> str:
        """
        Find actual Verilog files in Docker container to provide better module context.

        Args:
            container_name: Docker container name
            module_name: Module name to search for

        Returns:
            String containing Verilog file information
        """
        try:
            # Use builder.run_cmd instead of subprocess for Docker operations
            exit_code, stdout, stderr = self.builder.run_cmd('find /code/workspace/build -name "*.sv" -type f')
            if exit_code != 0:
                if self.debug:
                    print(f'❌ Failed to find Verilog files: {stderr}')
                return ''

            verilog_files = [f.strip() for f in stdout.strip().split('\n') if f.strip()]

            if not verilog_files:
                if self.debug:
                    print('⚠️  No Verilog files found in Docker container')
                return ''

            # Read content of first few files to provide context
            context_info = []
            for verilog_file in verilog_files[:3]:  # Limit to first 3 files
                try:
                    # Read first 10 lines of each file
                    head_exit_code, head_stdout, head_stderr = self.builder.run_cmd(f'head -10 {verilog_file}')
                    if head_exit_code == 0:
                        context_info.append(f'\n=== {verilog_file} ===\n{head_stdout}')
                    else:
                        if self.debug:
                            print(f'⚠️  Could not read {verilog_file}: {head_stderr}')
                except Exception as e:
                    if self.debug:
                        print(f'⚠️  Error reading {verilog_file}: {str(e)}')

            result = f'Found {len(verilog_files)} Verilog files in Docker:\n'
            result += '\n'.join(verilog_files)
            if context_info:
                result += '\n\nSample content:'
                result += '\n'.join(context_info)

            return result

        except Exception as e:
            if self.debug:
                print(f'❌ Error finding Verilog files in Docker: {str(e)}')
            return ''

    def find_chisel_files(self, patterns=None, input_data=None, chisel_source_pattern=None) -> list:
        """
        Find Chisel source files using glob patterns (supports multiple patterns and Docker).

        Args:
            patterns: List of patterns to search (optional)
            input_data: Input data containing Docker configuration
            chisel_source_pattern: Default Chisel source pattern

        Returns:
            List of found Chisel file paths
        """
        if patterns is None:
            patterns = [chisel_source_pattern] if chisel_source_pattern else []
        elif isinstance(patterns, str):
            patterns = [patterns]

        all_chisel_files = []

        # Check if Docker container specified
        if input_data:
            docker_container = input_data.get('docker_container', 'hagent')
            docker_patterns = input_data.get('docker_patterns', ['/code/workspace/repo'])

            # Search in Docker first
            if docker_container:
                docker_files = self.find_chisel_files_docker(docker_container, docker_patterns)
                all_chisel_files.extend(docker_files)

        # Then search local patterns
        for pattern in patterns:
            if pattern.startswith('docker:'):
                # Skip Docker patterns - already handled above
                continue

            try:
                matching_files = glob.glob(pattern, recursive=True)
                if self.debug and matching_files:
                    print(f'  📁 Pattern "{pattern}" found {len(matching_files)} file(s)')
                all_chisel_files.extend(matching_files)
            except Exception as e:
                if self.debug:
                    print(f'  ❌ Error with pattern "{pattern}": {str(e)}')

        # Remove duplicates while preserving order
        unique_files = []
        seen = set()
        for file_path in all_chisel_files:
            if file_path not in seen:
                unique_files.append(file_path)
                seen.add(file_path)

        if self.debug:
            print(f'📁 Total unique Chisel files found: {len(unique_files)}')

        return unique_files

    def read_docker_file(self, docker_path: str) -> str:
        """
        Read file content from Docker container using Builder API.

        Args:
            docker_path: Docker path in format 'docker:container_name:file_path'

        Returns:
            File content as string

        Raises:
            ValueError: If docker_path format is invalid
        """
        # Parse docker path: docker:container_name:file_path
        parts = docker_path.split(':', 2)
        if len(parts) != 3 or parts[0] != 'docker':
            raise ValueError(f'Invalid docker path format: {docker_path}')

        # parts[1] is container name - ignored since we use Builder API
        file_path = parts[2]

        try:
            # Use builder.run_cmd instead of subprocess
            exit_code, stdout, stderr = self.builder.run_cmd(f'cat {file_path}')
            if exit_code == 0:
                if self.debug:
                    print(f'[DEBUG] Successfully read Docker file: {file_path}')
                return stdout
            else:
                error_msg = f'Failed to read Docker file {file_path}: {stderr}'
                if self.debug:
                    print(f'❌ {error_msg}')
                raise Exception(error_msg)
        except Exception as e:
            error_msg = f'Error reading Docker file {docker_path}: {str(e)}'
            if self.debug:
                print(f'❌ {error_msg}')
            raise Exception(error_msg)

    def prepare_files_for_module_finder(self, chisel_files: list) -> list:
        """
        Prepare file list for module_finder (handle Docker files).

        Args:
            chisel_files: List of Chisel file paths (may include Docker paths)

        Returns:
            List of prepared file paths (local temp files for Docker content)
        """
        prepared_files = []
        self.temp_files = []  # Keep track for cleanup

        for file_path in chisel_files:
            if file_path.startswith('docker:'):
                try:
                    # Read content from Docker
                    content = self.read_docker_file(file_path)

                    # Create temp file
                    temp_fd, temp_path = tempfile.mkstemp(suffix='.scala', prefix='docker_')
                    with os.fdopen(temp_fd, 'w') as f:
                        f.write(content)

                    self.temp_files.append(temp_path)
                    prepared_files.append(temp_path)

                    # Map temp path back to original for reporting
                    if not hasattr(self, 'temp_to_original'):
                        self.temp_to_original = {}
                    self.temp_to_original[temp_path] = file_path

                    if self.debug:
                        print(f'📄 Created temp file for Docker content: {temp_path} -> {file_path}')

                except Exception as e:
                    if self.debug:
                        print(f'❌ Failed to prepare Docker file {file_path}: {str(e)}')
                    # Skip this file but continue with others
                    continue
            else:
                # Regular local file
                prepared_files.append(file_path)

        if self.debug:
            print(f'📋 Prepared {len(prepared_files)} files for module finder ({len(self.temp_files)} temp files created)')

        return prepared_files

    def cleanup_temp_files(self):
        """Clean up temporary files created for Docker content."""
        if hasattr(self, 'temp_files'):
            cleaned_count = 0
            for temp_file in self.temp_files:
                try:
                    os.unlink(temp_file)
                    cleaned_count += 1
                except OSError as e:
                    if self.debug:
                        print(f'⚠️  Failed to clean up temp file {temp_file}: {str(e)}')

            if self.debug and cleaned_count > 0:
                print(f'🧹 Cleaned up {cleaned_count} temporary files')

            self.temp_files = []

        # Also clear the mapping
        if hasattr(self, 'temp_to_original'):
            self.temp_to_original = {}

    def get_original_path(self, temp_path: str) -> str:
        """
        Get the original Docker path for a temporary file.

        Args:
            temp_path: Temporary file path

        Returns:
            Original Docker path or temp_path if not found
        """
        if hasattr(self, 'temp_to_original'):
            return self.temp_to_original.get(temp_path, temp_path)
        return temp_path

    def is_docker_path(self, file_path: str) -> bool:
        """
        Check if a file path is a Docker path.

        Args:
            file_path: File path to check

        Returns:
            True if it's a Docker path
        """
        return file_path.startswith('docker:')

    def parse_docker_path(self, docker_path: str) -> Dict[str, str]:
        """
        Parse a Docker path into its components.

        Args:
            docker_path: Docker path in format 'docker:container_name:file_path'

        Returns:
            Dict with 'container', 'file_path' keys

        Raises:
            ValueError: If docker_path format is invalid
        """
        parts = docker_path.split(':', 2)
        if len(parts) != 3 or parts[0] != 'docker':
            raise ValueError(f'Invalid docker path format: {docker_path}')

        return {'container': parts[1], 'file_path': parts[2]}

    def get_temp_file_count(self) -> int:
        """
        Get the number of currently managed temporary files.

        Returns:
            Number of temporary files
        """
        return len(getattr(self, 'temp_files', []))
