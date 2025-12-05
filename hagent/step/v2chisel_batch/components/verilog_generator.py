"""
VerilogGenerator component for v2chisel_batch refactoring.

This component handles compilation of Chisel code and generation of Verilog files
using the MCP profile system. It replaces hardcoded SBT commands with
clean MCP profile-based compilation and Verilog generation.
"""

from typing import Dict, List, Optional, Any


class VerilogGenerator:
    """
    Handles Chisel compilation and Verilog generation using MCP profiles.

    This component is responsible for:
    1. Compiling Chisel code using MCP profile system
    2. Generating Verilog from Chisel in a single step (MCP compile API does both)
    3. Providing a clean, reusable interface for Verilog generation throughout the pipeline
    4. Finding and backing up generated Verilog files
    5. Verifying Verilog output exists in expected locations

    The MCP 'compile' API runs the full 'runMain' command which both compiles
    Chisel code AND generates Verilog in a single operation.
    """

    def __init__(self, builder, debug: bool = True):
        """
        Initialize VerilogGenerator.

        Args:
            builder: Builder instance for Docker/local operations
            debug: Enable debug output
        """
        self.builder = builder
        self.debug = debug

    def generate_verilog(self, cpu_profile: str) -> Dict[str, Any]:
        """
        Compile Chisel code AND generate Verilog using MCP profile system.

        This method replaces both traditional 'sbt compile' and 'sbt runMain' steps.
        The MCP compile API handles both compilation and Verilog generation in one call.

        Args:
            cpu_profile: MCP profile name (e.g., 'singlecyclecpu_d', 'pipelined_d', 'dualissue_d')

        Returns:
            Dict with:
                - success: bool indicating if compilation succeeded
                - output: stdout from compilation
                - error: error message if failed
                - compilation_method: method used for compilation
                - profile: profile name used

        Examples:
            >>> verilog_gen = VerilogGenerator(builder)
            >>> result = verilog_gen.generate_verilog('pipelined_d')
            >>> if result['success']:
            >>>     print('Compilation and Verilog generation successful!')
        """
        if self.debug:
            print(f'🏗️  [VERILOG_GEN] Compiling Chisel and generating Verilog using MCP profile: {cpu_profile}')

        try:
            # Use MCP profile system - this handles BOTH compilation AND Verilog generation!
            exit_code, stdout, stderr = self.builder.run_api(exact_name=cpu_profile, command_name='compile')

            if exit_code == 0:
                if self.debug:
                    print('✅ [VERILOG_GEN] Successfully compiled Chisel and generated Verilog')
                return {
                    'success': True,
                    'output': stdout,
                    'compilation_method': f'mcp_profile_{cpu_profile}',
                    'profile': cpu_profile,
                }
            else:
                error_msg = f'MCP compile failed for {cpu_profile}: {stderr}'
                if self.debug:
                    print(f'❌ [VERILOG_GEN] {error_msg}')
                return {
                    'success': False,
                    'error': error_msg,
                    'compilation_method': f'mcp_profile_{cpu_profile}_failed',
                    'stderr': stderr,
                }

        except Exception as e:
            error_msg = f'MCP compilation exception: {str(e)}'
            if self.debug:
                print(f'❌ [VERILOG_GEN] {error_msg}')
            return {'success': False, 'error': error_msg, 'compilation_method': 'mcp_exception'}

    def verify_verilog_output(self, cpu_profile: str) -> Dict[str, Any]:
        """
        Verify that Verilog output files exist in the expected build directory.

        Args:
            cpu_profile: MCP profile name used for compilation

        Returns:
            Dict with verification results including file count and paths
        """
        try:
            # Map profile to build directory
            profile_to_build_dir = {
                'singlecyclecpu_d': 'build_singlecyclecpu_d',
                'pipelined_d': 'build_pipelined_d',
                'dualissue_d': 'build_dualissue_d',
            }

            build_dir = profile_to_build_dir.get(cpu_profile, 'build_singlecyclecpu_d')
            build_path = f'/code/workspace/build/{build_dir}'

            if self.debug:
                print(f'🔍 [VERILOG_GEN] Verifying Verilog output in {build_path}')

            # Check if build directory exists and has .sv files
            exit_code, stdout, stderr = self.builder.run_cmd(f'find {build_path} -name "*.sv" -type f')

            if exit_code == 0 and stdout.strip():
                verilog_files = stdout.strip().split('\n')
                if self.debug:
                    print(f'✅ [VERILOG_GEN] Found {len(verilog_files)} Verilog files in {build_path}')

                return {'success': True, 'file_count': len(verilog_files), 'files': verilog_files, 'build_dir': build_path}
            else:
                if self.debug:
                    print(f'⚠️  [VERILOG_GEN] No Verilog files found in {build_path}')
                return {'success': False, 'error': 'No Verilog files found', 'build_dir': build_path}

        except Exception as e:
            error_msg = f'Verification failed: {str(e)}'
            if self.debug:
                print(f'❌ [VERILOG_GEN] {error_msg}')
            return {'success': False, 'error': error_msg}

    def generate_fresh_baseline_verilog(self, docker_container: Optional[str] = None) -> Dict[str, Any]:
        """
        Generate fresh baseline Verilog from pristine Chisel code.

        Args:
            docker_container: Docker container name (optional, Builder handles this)

        Returns:
            Dict with generation results and status
        """
        if self.debug:
            print('🏭 [VERILOG_GEN] Generating fresh baseline Verilog from pristine Chisel...')

        # Use Builder API - no need for container name since Builder handles this
        if docker_container is None:
            docker_container = 'hagent'  # Default fallback, but Builder API will handle this

        try:
            # Generate ONLY SingleCycleCPU to match what the gate design will be
            if self.debug:
                print('🔧 [VERILOG_GEN] Running: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')

            exit_code, stdout, stderr = self.builder.run_cmd(
                'bash -l -c \'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUNoDebug"\''
            )

            if exit_code == 0:
                if self.debug:
                    print('✅ [VERILOG_GEN] Fresh baseline Verilog generated successfully')
                    print('     Command used: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')

                # Copy generated files from build_singlecyclecpu_d to build_singlecyclecpu_nd
                # so they're available in the location the backup method expects
                copy_result = self._copy_baseline_files()

                if copy_result['success']:
                    if self.debug:
                        print('✅ [VERILOG_GEN] Copied baseline files to expected location')

                    return {
                        'success': True,
                        'command_used': 'sbt "runMain dinocpu.SingleCycleCPUNoDebug"',
                        'stdout': stdout,
                        'stderr': stderr,
                        'copy_result': copy_result,
                    }
                else:
                    if self.debug:
                        print(f'⚠️  [VERILOG_GEN] File copy failed: {copy_result.get("error", "Unknown error")}')
                    return {
                        'success': False,
                        'error': f'Baseline file copy failed: {copy_result.get("error", "Unknown")}',
                        'generation_success': True,
                        'copy_success': False,
                    }
            else:
                error_msg = f'Fresh baseline Verilog generation failed: {stderr}'
                if self.debug:
                    print(f'❌ [VERILOG_GEN] {error_msg}')
                return {'success': False, 'error': error_msg, 'stderr': stderr}

        except Exception as e:
            error_msg = f'Fresh baseline generation failed: {str(e)}'
            if self.debug:
                print(f'❌ [VERILOG_GEN] {error_msg}')
            return {'success': False, 'error': error_msg}

    def generate_verilog_from_chisel(self, docker_container: str, module_name: str) -> Dict[str, Any]:
        """
        Generate Verilog from Chisel code with permission fixes and multiple command fallbacks.

        Args:
            docker_container: Docker container name
            module_name: Module name to generate

        Returns:
            Dict with generation results and status
        """
        if self.debug:
            print('🔧 [VERILOG_GEN] Generating Verilog with permission fixes...')

        try:
            # Step 1: Fix permissions on the repo directory
            if self.debug:
                print('🔧 [VERILOG_GEN] Fixing file permissions in container...')

            exit_code, stdout, stderr = self.builder.run_cmd('chown -R root:root /code/workspace/repo')
            if exit_code == 0:
                if self.debug:
                    print('✅ [VERILOG_GEN] Fixed repository permissions')
            else:
                if self.debug:
                    print(f'⚠️  [VERILOG_GEN] Permission fix warning: {stderr}')

            # Step 2: Clean target directories and create fresh build dirs
            self.builder.run_cmd('rm -rf /code/workspace/repo/target /code/workspace/repo/project/target || true')
            self.builder.run_cmd('mkdir -p /code/workspace/build/build_singlecyclecpu_nd')
            if self.debug:
                print('🗑️ [VERILOG_GEN] Cleaned target directories and prepared build dirs')

            # Step 3: Try Verilog generation commands with fallbacks
            generation_commands = self._get_generation_commands()

            for cmd_info in generation_commands:
                if self.debug:
                    print(f'🔧 [VERILOG_GEN] Trying: {cmd_info["name"]}')

                exit_code, stdout, stderr = self.builder.run_cmd(f"bash -l -c '{cmd_info['cmd']}'")

                if exit_code == 0:
                    if self.debug:
                        print(f'✅ [VERILOG_GEN] Success with: {cmd_info["name"]}')
                        print(f'     Command: {cmd_info["cmd"]}')

                    # Find generated Verilog files
                    verilog_files = self._find_generated_verilog_files(docker_container)

                    return {
                        'success': True,
                        'command_used': cmd_info['cmd'],
                        'method_name': cmd_info['name'],
                        'output': stdout,
                        'stderr': stderr,
                        'files': verilog_files,
                    }
                else:
                    if self.debug:
                        print(f'❌ [VERILOG_GEN] Failed with: {cmd_info["name"]} - {stderr}')

            # If all commands failed
            error_msg = 'All Verilog generation commands failed'
            if self.debug:
                print(f'❌ [VERILOG_GEN] {error_msg}')
            return {'success': False, 'error': error_msg}

        except Exception as e:
            error_msg = f'Verilog generation failed: {str(e)}'
            if self.debug:
                print(f'❌ [VERILOG_GEN] {error_msg}')
            return {'success': False, 'error': error_msg}

    def generate_baseline_verilog(self, docker_container: str, backup_id: str) -> Dict[str, Any]:
        """
        Generate baseline Verilog from original (unmodified) Chisel code for LEC golden design.

        Args:
            docker_container: Docker container name
            backup_id: Backup identifier for file management

        Returns:
            Dict with generation results and file information
        """
        try:
            if self.debug:
                print('⚡ [VERILOG_GEN] Generating baseline Verilog from pristine Chisel code...')

            # Use same generation logic as generate_verilog_from_chisel but for baseline
            # We assume the Chisel code is currently in its original state (before any diff application)
            result = self.generate_verilog_from_chisel(docker_container, 'dinocpu')

            if not result['success']:
                if self.debug:
                    print(f'⚠️  [VERILOG_GEN] Failed to generate baseline Verilog: {result.get("error", "Unknown error")}')
                    print('     LEC will be skipped due to baseline generation failure')
                return {'success': False, 'error': f'Baseline generation failed: {result.get("error", "Unknown")}'}

            if self.debug:
                print('✅ [VERILOG_GEN] Baseline Verilog generated successfully')

            # Find all generated Verilog files in the container
            if self.debug:
                print('📁 [VERILOG_GEN] Finding and backing up generated Verilog files...')

            verilog_files = self.find_and_backup_verilog_files(docker_container, backup_id)

            if verilog_files:
                if self.debug:
                    print(f'✅ [VERILOG_GEN] Backed up {len(verilog_files)} baseline Verilog files')
                return {
                    'success': True,
                    'files': verilog_files,
                    'generation_output': result.get('output', ''),
                    'command_used': result.get('command_used', ''),
                }
            else:
                if self.debug:
                    print('⚠️  [VERILOG_GEN] No Verilog files found after generation')
                return {'success': False, 'error': 'No Verilog files found after baseline generation'}

        except Exception as e:
            error_msg = f'Baseline Verilog generation failed: {str(e)}'
            if self.debug:
                print(f'❌ [VERILOG_GEN] {error_msg}')
            return {'success': False, 'error': error_msg}

    def backup_existing_original_verilog(self, docker_container: str, backup_id: str) -> Dict[str, Any]:
        """
        Create backup of existing original Verilog files.

        Args:
            docker_container: Docker container name
            backup_id: Backup identifier

        Returns:
            Dict with backup results and file information
        """
        try:
            if self.debug:
                print(f'💾 [VERILOG_GEN] Creating backup of existing original Verilog files (ID: {backup_id})')

            # Find existing original Verilog files
            verilog_files = self._find_original_verilog_files(docker_container)

            if not verilog_files:
                if self.debug:
                    print('⚠️  [VERILOG_GEN] No original Verilog files found to backup')
                return {'success': True, 'message': 'No original Verilog files to backup', 'files': {}}

            # Create backup directory
            backup_dir = f'/tmp/original_verilog_{backup_id}'
            exit_code, _, stderr = self.builder.run_cmd(f'mkdir -p {backup_dir}')

            if exit_code != 0:
                return {'success': False, 'error': f'Failed to create backup directory: {stderr}'}

            # Copy each file to backup directory
            backed_up_files = {}
            for file_path in verilog_files:
                filename = file_path.split('/')[-1]
                backup_path = f'{backup_dir}/{filename}'

                cp_exit_code, _, cp_stderr = self.builder.run_cmd(f'cp {file_path} {backup_path}')

                if cp_exit_code == 0:
                    backed_up_files[file_path] = backup_path
                    if self.debug:
                        print(f'     ✅ Backed up original Verilog: {filename}')
                else:
                    if self.debug:
                        print(f'     ⚠️  Failed to backup {filename}: {cp_stderr}')

            if self.debug:
                print(f'✅ [VERILOG_GEN] Successfully backed up {len(backed_up_files)} original Verilog files')

            return {'success': True, 'backup_dir': backup_dir, 'files': backed_up_files, 'file_count': len(backed_up_files)}

        except Exception as e:
            error_msg = f'Original Verilog backup failed: {str(e)}'
            if self.debug:
                print(f'❌ [VERILOG_GEN] {error_msg}')
            return {'success': False, 'error': error_msg}

    def find_and_backup_verilog_files(self, docker_container: str, backup_id: str) -> Dict[str, str]:
        """
        Find generated Verilog files and back them up for later use in golden design creation.

        Args:
            docker_container: Docker container name
            backup_id: Backup identifier

        Returns:
            Dict mapping original paths to backup paths
        """
        try:
            # Search for .sv files in common generation locations
            search_paths = ['/code/workspace/repo', '/code/workspace/build', '/code/workspace']

            found_files = {}
            backup_dir = f'/tmp/baseline_verilog_{backup_id}'

            # Create backup directory for baseline Verilog
            exit_code, _, stderr = self.builder.run_cmd(f'mkdir -p {backup_dir}')
            if exit_code != 0:
                if self.debug:
                    print(f'❌ [VERILOG_GEN] Failed to create backup directory: {stderr}')
                return {}

            for search_path in search_paths:
                try:
                    # Find .sv files
                    exit_code, stdout, stderr = self.builder.run_cmd(f'find {search_path} -name "*.sv" -type f')

                    if exit_code == 0 and stdout.strip():
                        verilog_files = [f.strip() for f in stdout.strip().split('\n') if f.strip()]

                        for verilog_file in verilog_files:
                            # Extract filename for backup
                            filename = verilog_file.split('/')[-1]
                            backup_path = f'{backup_dir}/{filename}'

                            # Copy to backup location
                            cp_exit_code, _, cp_stderr = self.builder.run_cmd(f'cp {verilog_file} {backup_path}')

                            if cp_exit_code == 0:
                                found_files[verilog_file] = backup_path
                                if self.debug:
                                    print(f'     ✅ Backed up baseline Verilog: {filename}')
                            else:
                                if self.debug:
                                    print(f'     ⚠️  Failed to backup {filename}: {cp_stderr}')

                except Exception as e:
                    if self.debug:
                        print(f'⚠️  [VERILOG_GEN] Error searching in {search_path}: {str(e)}')
                    continue

            if self.debug:
                print(f'📁 [VERILOG_GEN] Found and backed up {len(found_files)} Verilog files')

            return found_files

        except Exception as e:
            if self.debug:
                print(f'❌ [VERILOG_GEN] Error finding and backing up Verilog files: {str(e)}')
            return {}

    def _copy_baseline_files(self) -> Dict[str, Any]:
        """
        Copy generated baseline files to expected location.

        Returns:
            Dict with copy operation results
        """
        try:
            # Create target directory
            mkdir_exit_code, _, mkdir_stderr = self.builder.run_cmd('mkdir -p /code/workspace/build/build_singlecyclecpu_nd')

            if mkdir_exit_code != 0:
                return {'success': False, 'error': f'Failed to create target directory: {mkdir_stderr}'}

            # Copy files from build_singlecyclecpu_d to build_singlecyclecpu_nd
            copy_exit_code, copy_stdout, copy_stderr = self.builder.run_cmd(
                'cp -r /code/workspace/build/build_singlecyclecpu_d/* /code/workspace/build/build_singlecyclecpu_nd/ 2>/dev/null || true'
            )

            if copy_exit_code == 0:
                if self.debug:
                    print('✅ [VERILOG_GEN] Copied baseline files to expected location')
                return {'success': True, 'copied_files': True}
            else:
                if self.debug:
                    print(f'⚠️  [VERILOG_GEN] Copy had issues: {copy_stderr}')
                # Don't fail for copy issues, as some may be expected
                return {'success': True, 'copied_files': True, 'warning': copy_stderr}

        except Exception as e:
            return {'success': False, 'error': f'Copy operation failed: {str(e)}'}

    def _get_generation_commands(self) -> List[Dict[str, str]]:
        """
        Get ordered list of Verilog generation commands to try.

        Returns:
            List of command dictionaries with 'cmd' and 'name' keys
        """
        return [
            # DINO-specific SBT commands (HIGHEST PRIORITY - these work for DINO)
            {
                'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUNoDebug"',
                'name': 'SingleCycleCPUNoDebug',
            },
            {
                'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.Main"',
                'name': 'Main',
            },
            {
                'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.pipelined.PipelinedDualIssueNoDebug"',
                'name': 'PipelinedDualIssueNoDebug',
            },
            {
                'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.PipelinedDualIssueNoDebug"',
                'name': 'PipelinedDualIssueNoDebug_alt',
            },
            {
                'cmd': 'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUDebug"',
                'name': 'SingleCycleCPUDebug',
            },
            # Generic fallback commands
            {
                'cmd': 'cd /code/workspace/repo && sbt "runMain Main"',
                'name': 'Generic_Main',
            },
            {
                'cmd': 'cd /code/workspace/repo && sbt run',
                'name': 'SBT_Run',
            },
        ]

    def _find_generated_verilog_files(self, docker_container: str) -> List[str]:
        """
        Find Verilog files generated by the current build.

        Args:
            docker_container: Docker container name

        Returns:
            List of generated Verilog file paths
        """
        try:
            search_paths = ['/code/workspace/repo', '/code/workspace/build']
            found_files = []

            for search_path in search_paths:
                exit_code, stdout, stderr = self.builder.run_cmd(f'find {search_path} -name "*.sv" -type f')

                if exit_code == 0 and stdout.strip():
                    files = [f.strip() for f in stdout.strip().split('\n') if f.strip()]
                    found_files.extend(files)

            # Remove duplicates while preserving order
            unique_files = []
            seen = set()
            for file_path in found_files:
                if file_path not in seen:
                    unique_files.append(file_path)
                    seen.add(file_path)

            if self.debug:
                print(f'📁 [VERILOG_GEN] Found {len(unique_files)} generated Verilog files')

            return unique_files

        except Exception as e:
            if self.debug:
                print(f'⚠️  [VERILOG_GEN] Error finding generated files: {str(e)}')
            return []

    def _find_original_verilog_files(self, docker_container: str) -> List[str]:
        """
        Find existing original Verilog files that might need backup.

        Args:
            docker_container: Docker container name

        Returns:
            List of original Verilog file paths
        """
        try:
            # Look in typical locations for existing Verilog
            search_paths = ['/code/workspace/build/build_singlecyclecpu_nd']
            found_files = []

            for search_path in search_paths:
                exit_code, stdout, stderr = self.builder.run_cmd(f'find {search_path} -name "*.sv" -type f 2>/dev/null || true')

                if exit_code == 0 and stdout.strip():
                    files = [f.strip() for f in stdout.strip().split('\n') if f.strip()]
                    found_files.extend(files)

            if self.debug:
                print(f'📁 [VERILOG_GEN] Found {len(found_files)} existing original Verilog files')

            return found_files

        except Exception as e:
            if self.debug:
                print(f'⚠️  [VERILOG_GEN] Error finding original files: {str(e)}')
            return []

    def verify_verilog_generation(self, expected_files: Optional[List[str]] = None) -> Dict[str, Any]:
        """
        Verify that Verilog generation completed successfully.

        Args:
            expected_files: Optional list of expected file names

        Returns:
            Dict with verification results
        """
        try:
            # Find all generated .sv files
            generated_files = self._find_generated_verilog_files('')

            if not generated_files:
                return {'success': False, 'error': 'No Verilog files found after generation'}

            # Check file accessibility
            accessible_files = []
            for file_path in generated_files:
                exit_code, stdout, stderr = self.builder.run_cmd(f'head -1 {file_path}')
                if exit_code == 0:
                    accessible_files.append(file_path)
                else:
                    if self.debug:
                        print(f'⚠️  [VERILOG_GEN] File not accessible: {file_path}')

            if accessible_files:
                if self.debug:
                    print(f'✅ [VERILOG_GEN] Verified {len(accessible_files)} accessible Verilog files')

                return {
                    'success': True,
                    'files': accessible_files,
                    'file_count': len(accessible_files),
                    'total_found': len(generated_files),
                }
            else:
                return {'success': False, 'error': 'No accessible Verilog files found'}

        except Exception as e:
            error_msg = f'Verilog verification failed: {str(e)}'
            if self.debug:
                print(f'❌ [VERILOG_GEN] {error_msg}')
            return {'success': False, 'error': error_msg}
