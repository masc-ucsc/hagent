"""
BaselineVerilogGenerator component for v2chisel_batch refactoring.

This component handles generation of baseline Verilog files from pristine Chisel code,
which are used as the reference for golden design creation and LEC verification.
"""

from typing import Dict, Optional, Any
import os


class BaselineVerilogGenerator:
    """
    Handles baseline Verilog generation from pristine Chisel code.

    This component is responsible for:
    1. Generating fresh baseline Verilog from unmodified Chisel code
    2. Managing baseline file locations and backup integration
    3. Ensuring proper file tracking for golden design creation
    """

    def __init__(self, builder, debug: bool = True):
        """
        Initialize BaselineVerilogGenerator.

        Args:
            builder: Builder instance for Docker/local operations
            debug: Enable debug output
        """
        self.builder = builder
        self.debug = debug

    def _get_profile_name(self, verilog_file: str) -> str:
        """
        Map verilog filename to hagent.yaml DEBUG profile name.

        Args:
            verilog_file: Verilog filename (e.g., 'PipelinedCPU.sv')

        Returns:
            Profile name from hagent.yaml (e.g., 'pipelined_d')

        Examples:
            'SingleCycleCPU.sv' -> 'singlecyclecpu_d'
            'PipelinedCPU.sv' -> 'pipelined_d'
            'PipelinedDualIssueCPU.sv' -> 'dualissue_d'
        """
        verilog_lower = verilog_file.lower()

        if 'pipelined' in verilog_lower and 'dual' in verilog_lower:
            return 'dualissue_d'
        elif 'pipelined' in verilog_lower:
            return 'pipelined_d'
        else:
            return 'singlecyclecpu_d'

    def _get_build_dir_for_profile(self, profile_name: str) -> str:
        """
        Get build directory name for a DEBUG profile.

        Args:
            profile_name: Profile name from hagent.yaml (e.g., 'pipelined_d')

        Returns:
            Build directory name (e.g., 'build_pipelined_d')

        Examples:
            'pipelined_d' -> 'build_pipelined_d'
            'singlecyclecpu_d' -> 'build_singlecyclecpu_d'
            'dualissue_d' -> 'build_dualissue_d'
        """
        BUILD_DIR_MAP = {
            'singlecyclecpu_d': 'build_singlecyclecpu_d',
            'pipelined_d': 'build_pipelined_d',
            'dualissue_d': 'build_dualissue_d',
        }
        return BUILD_DIR_MAP.get(profile_name, 'build_singlecyclecpu_d')

    def _determine_required_profiles(self, verilog_files: Optional[list]) -> set:
        """
        Determine which MCP profiles are needed based on verilog filenames.

        Args:
            verilog_files: List of verilog filenames (e.g., ['PipelinedCPU.sv', 'ALU.sv'])

        Returns:
            Set of profile names needed (e.g., {'pipelined_d', 'singlecyclecpu_d'})

        Examples:
            ['PipelinedCPU.sv', 'ALU.sv'] -> {'pipelined_d'}
            ['SingleCycleCPU.sv'] -> {'singlecyclecpu_d'}
            ['PipelinedDualIssueCPU.sv'] -> {'dualissue_d'}
            None or [] -> {'singlecyclecpu_d'} (default fallback)
        """
        if not verilog_files:
            # Default to single-cycle if no files specified
            return {'singlecyclecpu_d'}

        profiles = set()
        for verilog_file in verilog_files:
            profile_name = self._get_profile_name(verilog_file)
            profiles.add(profile_name)

        return profiles

    def generate_fresh_baseline(
        self, docker_container: Optional[str] = None, verilog_files: Optional[list] = None
    ) -> Dict[str, Any]:
        """
        Generate fresh baseline Verilog from pristine Chisel code using MCP profiles.

        Args:
            docker_container: Container name (optional, Builder handles this)
            verilog_files: List of verilog filenames to determine CPU type

        Returns:
            Dict with success status, files info, and any errors
        """
        if self.debug:
            print('🏭 [BASELINE] Generating fresh baseline Verilog using MCP profiles...')

        try:
            # Determine CPU profile needed
            cpu_profiles = self._determine_required_profiles(verilog_files)
            profile_name = list(cpu_profiles)[0]  # Use first profile

            if self.debug:
                print(f'🔧 [BASELINE] Using MCP profile: {profile_name}')

            # Generate Verilog using MCP profile system
            exit_code, stdout, stderr = self.builder.run_api(exact_name=profile_name, command_name='compile')

            if exit_code != 0:
                error_msg = f'MCP compile failed for {profile_name}: {stderr}'
                if self.debug:
                    print(f'❌ [BASELINE] {error_msg}')
                return {'success': False, 'error': error_msg}

            if self.debug:
                print(f'✅ [BASELINE] Successfully generated Verilog using {profile_name}')

            # Find all generated .sv files
            verilog_files = self._find_baseline_verilog_files()

            if self.debug:
                print(f'📁 [BASELINE] Found {len(verilog_files)} baseline Verilog files')

            return {'success': True, 'profile': profile_name, 'files': verilog_files, 'stdout': stdout}

        except Exception as e:
            error_msg = f'Baseline generation failed: {str(e)}'
            if self.debug:
                print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}

    def _copy_baseline_files_for_profile(self, profile_name: str) -> Dict[str, Any]:
        """
        Copy generated baseline files for a specific profile to _nd (no-debug) directory.

        Args:
            profile_name: Profile name (e.g., 'pipelined_d', 'singlecyclecpu_d')

        Returns:
            Dict with success status and copy information
        """
        try:
            # Get source and target build directories
            source_dir = self._get_build_dir_for_profile(profile_name)
            # Convert _d to _nd for no-debug version
            target_dir = source_dir.replace('_d', '_nd')

            # Create target directory
            mkdir_exit_code, _, mkdir_stderr = self.builder.run_cmd(f'mkdir -p /code/workspace/build/{target_dir}')

            if mkdir_exit_code != 0:
                return {'success': False, 'error': f'Failed to create target directory: {mkdir_stderr}', 'profile': profile_name}

            # Copy files from _d to _nd directory
            cp_exit_code, cp_stdout, cp_stderr = self.builder.run_cmd(
                f'cp -r /code/workspace/build/{source_dir}/* /code/workspace/build/{target_dir}/'
            )

            if cp_exit_code == 0:
                if self.debug:
                    print(f'✅ [BASELINE] Copied {profile_name} files: {source_dir} → {target_dir}')
                return {'success': True, 'profile': profile_name, 'source': source_dir, 'target': target_dir}
            else:
                return {'success': False, 'error': f'File copy failed: {cp_stderr}', 'profile': profile_name}

        except Exception as e:
            return {'success': False, 'error': f'Copy operation failed: {str(e)}', 'profile': profile_name}

    def _copy_baseline_files(self) -> Dict[str, Any]:
        """
        Copy generated baseline files to expected location (legacy single-cycle only).
        This is kept for backward compatibility but will be deprecated.

        Returns:
            Dict with success status and copy information
        """
        return self._copy_baseline_files_for_profile('singlecyclecpu_d')

    def _find_baseline_verilog_files(self) -> Dict[str, str]:
        """
        Find and catalog baseline Verilog files from all _nd directories.

        Returns:
            Dict mapping relative paths to absolute paths of Verilog files
        """
        try:
            # Find all .sv files in ALL _nd baseline directories
            # This searches build_singlecyclecpu_nd, build_pipelined_nd, build_dualissue_nd
            exit_code, stdout, stderr = self.builder.run_cmd(
                'find /code/workspace/build -type d -name "*_nd" -exec find {} -name "*.sv" -type f \\;'
            )

            verilog_files = {}
            if exit_code == 0 and stdout.strip():
                files = stdout.strip().split('\n')
                for file_path in files:
                    if file_path.strip():
                        # Get just the filename for the key
                        filename = os.path.basename(file_path.strip())
                        verilog_files[filename] = file_path.strip()

                if self.debug:
                    print(f'📁 [BASELINE] Found {len(verilog_files)} baseline Verilog files:')
                    for filename, path in verilog_files.items():
                        print(f'     - {filename}: {path}')
            else:
                if self.debug:
                    print('⚠️  [BASELINE] No Verilog files found in baseline directories')

            return verilog_files

        except Exception as e:
            if self.debug:
                print(f'⚠️  [BASELINE] Error finding baseline files: {str(e)}')
            return {}

    def backup_baseline_verilog(self, backup_id: str) -> Dict[str, Any]:
        """
        Create backup of baseline Verilog files for later use.

        Args:
            backup_id: Unique identifier for this backup

        Returns:
            Dict with backup success status and file information
        """
        try:
            if self.debug:
                print(f'💾 [BASELINE] Creating backup of baseline Verilog files (ID: {backup_id})')

            # Find baseline files
            verilog_files = self._find_baseline_verilog_files()

            if not verilog_files:
                return {'success': False, 'error': 'No baseline Verilog files found to backup'}

            # Create backup directory
            backup_dir = f'/tmp/baseline_verilog_{backup_id}'
            mkdir_exit_code, _, mkdir_stderr = self.builder.run_cmd(f'mkdir -p {backup_dir}')

            if mkdir_exit_code != 0:
                return {'success': False, 'error': f'Failed to create backup directory: {mkdir_stderr}'}

            # Copy each file to backup directory
            backed_up_files = {}
            for filename, source_path in verilog_files.items():
                backup_path = f'{backup_dir}/{filename}'

                cp_exit_code, _, cp_stderr = self.builder.run_cmd(f'cp {source_path} {backup_path}')

                if cp_exit_code == 0:
                    backed_up_files[source_path] = backup_path
                    if self.debug:
                        print(f'     ✅ Backed up baseline Verilog: {filename}')
                else:
                    if self.debug:
                        print(f'     ⚠️  Failed to backup {filename}: {cp_stderr}')

            if backed_up_files:
                if self.debug:
                    print(f'✅ [BASELINE] Successfully backed up {len(backed_up_files)} baseline Verilog files')

                return {'success': True, 'backup_dir': backup_dir, 'files': backed_up_files, 'file_count': len(backed_up_files)}
            else:
                return {'success': False, 'error': 'No files were successfully backed up'}

        except Exception as e:
            error_msg = f'Baseline backup failed: {str(e)}'
            if self.debug:
                print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}

    def verify_baseline_files_exist(self) -> Dict[str, Any]:
        """
        Verify that baseline Verilog files exist and are accessible.

        Returns:
            Dict with verification results
        """
        try:
            verilog_files = self._find_baseline_verilog_files()

            if not verilog_files:
                return {'success': False, 'error': 'No baseline Verilog files found', 'file_count': 0}

            # Verify each file is actually readable
            accessible_files = {}
            for filename, path in verilog_files.items():
                # Try to read first few lines to verify accessibility
                exit_code, stdout, stderr = self.builder.run_cmd(f'head -5 {path}')

                if exit_code == 0:
                    accessible_files[filename] = path
                else:
                    if self.debug:
                        print(f'⚠️  [BASELINE] File not accessible: {filename} at {path}')

            if accessible_files:
                if self.debug:
                    print(f'✅ [BASELINE] Verified {len(accessible_files)} baseline Verilog files are accessible')

                return {'success': True, 'files': accessible_files, 'file_count': len(accessible_files)}
            else:
                return {'success': False, 'error': 'No baseline Verilog files are accessible', 'file_count': 0}

        except Exception as e:
            error_msg = f'Baseline verification failed: {str(e)}'
            if self.debug:
                print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}
