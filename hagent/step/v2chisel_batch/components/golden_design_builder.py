#!/usr/bin/env python3
"""
GoldenDesignBuilder class for creating golden design files for LEC verification.

This class encapsulates the complex logic for creating golden design by:
1. Backing up existing original Verilog files
2. Creating golden directory structure  
3. Copying baseline files to golden directory
4. Applying Verilog diff to create the golden design
5. Managing file operations across Docker containers

The golden design is used as the reference for Logic Equivalence Check (LEC)
against the gate design generated from modified Chisel code.
"""

import os
import subprocess
from typing import Dict, List, Any, Optional


class GoldenDesignBuilder:
    """
    Handles creation of golden design files for LEC verification.
    
    The golden design builder creates a reference design by:
    1. Taking baseline/original Verilog files
    2. Applying the target Verilog diff to them
    3. Creating a golden design directory with the modified files
    4. Ensuring the golden design can be used for LEC comparison
    """
    
    def __init__(self, builder, debug: bool = True):
        """
        Initialize GoldenDesignBuilder.
        
        Args:
            builder: Builder instance for Docker operations
            debug: Enable debug output
        """
        self.builder = builder
        self.debug = debug
        
        # Golden design configuration
        self.golden_dir = '/code/workspace/repo/lec_golden'
        self.baseline_paths = [
            '/code/workspace/build/build_singlecyclecpu_nd',
            '/code/workspace/build/build_singlecyclecpu_d', 
            '/code/workspace/repo/generated',
            '/code/workspace/repo'
        ]
    
    def create_golden_design(self, verilog_diff: str, master_backup: Dict[str, Any], docker_container: str) -> Dict[str, Any]:
        """
        Create golden design by applying verilog_diff to baseline Verilog files.
        
        Args:
            verilog_diff: The unified diff to apply to baseline files
            master_backup: Backup information containing original Verilog files
            docker_container: Docker container name for operations
            
        Returns:
            Dict with success status, golden files list, and error details
        """
        try:
            if self.debug:
                print('🎯 [GOLDEN] Creating golden design from baseline + verilog_diff...')
                print('🔍 [DEBUG] Master backup contents:')
                print(f'     Keys: {list(master_backup.keys())}')
                print(f'     baseline_verilog_success: {master_backup.get("baseline_verilog_success", False)}')
                print(f'     original_verilog_files: {len(master_backup.get("original_verilog_files", {}))} files')
                
            # Step 1: Validate we have baseline Verilog files
            baseline_result = self._validate_baseline_files(master_backup)
            if not baseline_result['success']:
                return baseline_result
                
            baseline_verilog = baseline_result['files']
            
            # Step 2: Create golden directory structure
            dir_result = self._create_golden_directory(docker_container)
            if not dir_result['success']:
                return dir_result
            
            # Step 3: Copy baseline files to golden directory
            copy_result = self._copy_baseline_to_golden(baseline_verilog, docker_container)
            if not copy_result['success']:
                return copy_result
                
            copied_files = copy_result['copied_files']
            
            # Step 4: Apply verilog_diff to golden files
            diff_result = self._apply_diff_to_golden_files(verilog_diff, docker_container)
            if not diff_result['success']:
                return diff_result
            
            # Step 5: Success - return golden design info
            if self.debug:
                print('✅ Golden design generation: SUCCESS')
                
            return {
                'success': True,
                'golden_files': copied_files,
                'diff_applied': True, 
                'golden_directory': self.golden_dir,
                'files_modified': diff_result.get('files_modified', []),
                'applier_output': diff_result.get('output', 'Diff applied successfully')
            }
            
        except Exception as e:
            error_msg = f'Golden design creation failed: {str(e)}'
            if self.debug:
                print(f'❌ [GOLDEN] {error_msg}')
            return {'success': False, 'error': error_msg}
    
    def backup_existing_original_verilog(self, docker_container: str, backup_id: str) -> Dict[str, Any]:
        """
        Backup existing original Verilog files for later use in golden design creation.
        
        Args:
            docker_container: Docker container name
            backup_id: Unique backup identifier
            
        Returns:
            Dict with success status and backed up file mappings
        """
        try:
            if self.debug:
                print('📁 [ORIGINAL_VERILOG] Finding existing original Verilog files...')
            
            # Search for .sv files in all baseline paths
            all_verilog_files = {}
            
            for search_path in self.baseline_paths:
                files_found = self._find_verilog_files_in_path(docker_container, search_path)
                if files_found:
                    all_verilog_files.update(files_found)
                    if self.debug:
                        print(f'     📂 Found {len(files_found)} files in {search_path}')
            
            if not all_verilog_files:
                return {
                    'success': False, 
                    'error': 'No original Verilog files found in expected locations',
                    'files': {}
                }
            
            # Create backup directory
            backup_dir = f'/code/workspace/cache/backups/{backup_id}/original_verilog'
            mkdir_result = self._create_backup_directory(docker_container, backup_dir)
            if not mkdir_result['success']:
                return mkdir_result
            
            # Backup files
            backed_up_files = {}
            for file_path in all_verilog_files.keys():
                backup_result = self._backup_single_file(docker_container, file_path, backup_dir)
                if backup_result['success']:
                    backed_up_files[file_path] = backup_result['backup_path']
                elif self.debug:
                    print(f'     ⚠️  Failed to backup {file_path}: {backup_result.get("error", "Unknown")}')
            
            if self.debug:
                print(f'✅ [ORIGINAL_VERILOG] Successfully backed up {len(backed_up_files)} original Verilog files')
                
            return {
                'success': True,
                'files': backed_up_files,
                'backup_dir': backup_dir,
                'total_files': len(backed_up_files)
            }
            
        except Exception as e:
            error_msg = f'Original Verilog backup failed: {str(e)}'
            if self.debug:
                print(f'❌ [ORIGINAL_VERILOG] {error_msg}')
            return {'success': False, 'error': error_msg, 'files': {}}
    
    def generate_baseline_verilog(self, docker_container: str, backup_id: str) -> Dict[str, Any]:
        """
        Generate baseline Verilog from original (unmodified) Chisel code for LEC golden design.
        
        Args:
            docker_container: Docker container name
            backup_id: Backup identifier for storing baseline files
            
        Returns:
            Dict with success status and baseline generation results
        """
        try:
            if self.debug:
                print('⚡ [BASELINE] Generating baseline Verilog from pristine Chisel code...')
            
            # Step 1: Clean build directories
            clean_result = self._clean_build_directories(docker_container)
            if not clean_result['success']:
                return clean_result
            
            # Step 2: Generate Verilog using SBT
            generation_result = self._generate_verilog_with_sbt(docker_container)
            if not generation_result['success']:
                return generation_result
            
            # Step 3: Copy generated files to expected location
            copy_result = self._copy_generated_files(docker_container)
            if not copy_result['success']:
                return copy_result
                
            # Step 4: Backup the generated baseline files
            backup_result = self.backup_existing_original_verilog(docker_container, backup_id)
            
            if self.debug:
                if backup_result['success']:
                    print('✅ [BASELINE] Baseline Verilog generation and backup completed successfully')
                else:
                    print(f'⚠️  [BASELINE] Generation succeeded but backup failed: {backup_result.get("error", "Unknown")}')
            
            return {
                'success': backup_result['success'],
                'generation_success': generation_result['success'],
                'backup_result': backup_result,
                'files_generated': generation_result.get('files', []),
                'files_backed_up': backup_result.get('files', {})
            }
            
        except Exception as e:
            error_msg = f'Baseline Verilog generation failed: {str(e)}'
            if self.debug:
                print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}
    
    def _validate_baseline_files(self, master_backup: Dict[str, Any]) -> Dict[str, Any]:
        """Validate that we have the necessary baseline files for golden design creation."""
        baseline_verilog = master_backup.get('original_verilog_files', {})
        if not baseline_verilog:
            return {'success': False, 'error': 'No baseline Verilog files available in master backup'}
            
        baseline_success = master_backup.get('baseline_verilog_success', False)
        if not baseline_success:
            return {'success': False, 'error': 'Baseline Verilog generation was not successful'}
        
        if self.debug:
            print(f'📁 [GOLDEN] Found {len(baseline_verilog)} baseline Verilog files to process')
            for orig_path, backup_path in baseline_verilog.items():
                print(f'       - {orig_path} -> {backup_path}')
        
        return {'success': True, 'files': baseline_verilog}
    
    def _create_golden_directory(self, docker_container: str) -> Dict[str, Any]:
        """Create the golden design directory in the Docker container."""
        try:
            # Remove existing golden directory
            rm_cmd = ['docker', 'exec', docker_container, 'rm', '-rf', self.golden_dir]
            subprocess.run(rm_cmd, capture_output=True, text=True)
            
            # Create fresh golden directory
            mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', self.golden_dir]
            mkdir_result = subprocess.run(mkdir_cmd, capture_output=True, text=True)
            
            if mkdir_result.returncode != 0:
                return {'success': False, 'error': f'Failed to create golden directory: {mkdir_result.stderr}'}
            
            if self.debug:
                print(f'✅ [GOLDEN] Created golden design directory: {self.golden_dir}')
            
            return {'success': True, 'directory': self.golden_dir}
            
        except Exception as e:
            return {'success': False, 'error': f'Directory creation failed: {str(e)}'}
    
    def _copy_baseline_to_golden(self, baseline_verilog: Dict[str, str], docker_container: str) -> Dict[str, Any]:
        """Copy baseline Verilog files to the golden design directory."""
        copied_files = []
        failed_copies = []
        
        for container_path, backup_path in baseline_verilog.items():
            filename = container_path.split('/')[-1]
            golden_path = f'{self.golden_dir}/{filename}'
            
            # Copy from backup to golden directory (intra-container copy)
            copy_cmd = ['docker', 'exec', docker_container, 'cp', backup_path, golden_path]
            copy_result = subprocess.run(copy_cmd, capture_output=True, text=True)
            
            if copy_result.returncode == 0:
                copied_files.append(golden_path)
                if self.debug:
                    print(f'     ✅ Copied baseline to golden: {filename}')
            else:
                failed_copies.append(filename)
                if self.debug:
                    print(f'     ⚠️  Failed to copy {filename}: {copy_result.stderr}')
        
        if not copied_files:
            return {'success': False, 'error': 'No baseline files were copied to golden directory'}
        
        if self.debug:
            print(f'📁 [GOLDEN] Copied {len(copied_files)} files to golden directory')
            if failed_copies:
                print(f'     ⚠️  {len(failed_copies)} files failed to copy: {failed_copies}')
        
        return {
            'success': True, 
            'copied_files': copied_files,
            'failed_copies': failed_copies,
            'total_copied': len(copied_files)
        }
    
    def _apply_diff_to_golden_files(self, verilog_diff: str, docker_container: str) -> Dict[str, Any]:
        """Apply the verilog_diff to files in the golden directory."""
        try:
            if self.debug:
                print('🔧 [GOLDEN] Applying verilog_diff to golden design files...')
            
            # Import DockerDiffApplier
            try:
                from hagent.tool.docker_diff_applier import DockerDiffApplier
            except ImportError as e:
                return {'success': False, 'error': f'Could not import DockerDiffApplier: {str(e)}'}
            
            # Create applier configured for golden directory
            applier = DockerDiffApplier(docker_container)
            
            # Override file search to target golden directory only
            original_find_method = applier.find_file_in_container
            
            def golden_find_file(filename, base_path=self.golden_dir):
                """Find files only in the golden directory"""
                return original_find_method(filename, base_path)
            
            applier.find_file_in_container = golden_find_file
            
            # Fix filename case in verilog_diff to match actual files
            corrected_verilog_diff = self._fix_diff_filename_case(verilog_diff)
            
            # Apply the diff
            diff_success = applier.apply_diff_to_container(corrected_verilog_diff, dry_run=False)
            
            if diff_success:
                if self.debug:
                    print('✅ [GOLDEN] Diff applied successfully to golden design')
                return {
                    'success': True,
                    'diff_applied': True,
                    'output': 'Diff applied successfully to golden design files',
                    'files_modified': []  # DockerDiffApplier doesn't return file list
                }
            else:
                return {
                    'success': False,
                    'error': 'Diff application failed - check docker_diff_applier output'
                }
                
        except Exception as e:
            return {'success': False, 'error': f'Diff application error: {str(e)}'}
    
    def _find_verilog_files_in_path(self, docker_container: str, search_path: str) -> Dict[str, str]:
        """Find .sv files in a specific path within the Docker container."""
        try:
            find_cmd = ['docker', 'exec', docker_container, 'find', search_path, '-name', '*.sv', '-type', 'f']
            result = subprocess.run(find_cmd, capture_output=True, text=True, timeout=30)
            
            if result.returncode == 0 and result.stdout.strip():
                files = {}
                for file_path in result.stdout.strip().split('\n'):
                    file_path = file_path.strip()
                    if file_path:
                        files[file_path] = file_path  # Map path to itself for now
                return files
            else:
                return {}
                
        except Exception:
            return {}
    
    def _create_backup_directory(self, docker_container: str, backup_dir: str) -> Dict[str, Any]:
        """Create backup directory in Docker container."""
        try:
            mkdir_cmd = ['docker', 'exec', docker_container, 'mkdir', '-p', backup_dir]
            result = subprocess.run(mkdir_cmd, capture_output=True, text=True)
            
            if result.returncode == 0:
                return {'success': True, 'directory': backup_dir}
            else:
                return {'success': False, 'error': f'Failed to create backup directory: {result.stderr}'}
                
        except Exception as e:
            return {'success': False, 'error': f'Directory creation error: {str(e)}'}
    
    def _backup_single_file(self, docker_container: str, file_path: str, backup_dir: str) -> Dict[str, Any]:
        """Backup a single file to the backup directory."""
        try:
            filename = os.path.basename(file_path)
            backup_path = f'{backup_dir}/{filename}'
            
            cp_cmd = ['docker', 'exec', docker_container, 'cp', file_path, backup_path]
            result = subprocess.run(cp_cmd, capture_output=True, text=True)
            
            if result.returncode == 0:
                return {'success': True, 'backup_path': backup_path}
            else:
                return {'success': False, 'error': f'Copy failed: {result.stderr}'}
                
        except Exception as e:
            return {'success': False, 'error': f'Backup error: {str(e)}'}
    
    def _clean_build_directories(self, docker_container: str) -> Dict[str, Any]:
        """Clean build directories before baseline generation."""
        try:
            clean_cmd = ['docker', 'exec', docker_container, 'bash', '-c', 
                        'cd /code/workspace && rm -rf build/* || true']
            result = subprocess.run(clean_cmd, capture_output=True, text=True)
            
            if self.debug:
                print('✅ [BASELINE] Cleaned build directories for fresh generation')
                
            return {'success': True, 'cleaned': True}
            
        except Exception as e:
            return {'success': False, 'error': f'Build directory cleanup failed: {str(e)}'}
    
    def _generate_verilog_with_sbt(self, docker_container: str) -> Dict[str, Any]:
        """Generate Verilog using SBT build system."""
        try:
            # Generate SingleCycleCPU Verilog (no debug)
            exit_code, stdout, stderr = self.builder.run(
                'sbt "runMain dinocpu.SingleCycleCPUNoDebug"',
                cwd='/code/workspace'
            )
            
            if exit_code == 0:
                if self.debug:
                    print('✅ [BASELINE] Fresh baseline Verilog generated successfully')
                    print('     Command used: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')
                return {
                    'success': True,
                    'command': 'sbt "runMain dinocpu.SingleCycleCPUNoDebug"',
                    'files': []  # SBT doesn't return file list
                }
            else:
                error_msg = f'SBT generation failed: {stderr[-500:] if stderr else "No stderr"}'
                if self.debug:
                    print(f'❌ [BASELINE] {error_msg}')
                return {'success': False, 'error': error_msg}
                
        except Exception as e:
            return {'success': False, 'error': f'SBT generation error: {str(e)}'}
    
    def _copy_generated_files(self, docker_container: str) -> Dict[str, Any]:
        """Copy generated files from build_singlecyclecpu_d to build_singlecyclecpu_nd."""
        try:
            copy_exit_code, copy_stdout, copy_stderr = self.builder.run(
                'cp -r build/build_singlecyclecpu_d/* build/build_singlecyclecpu_nd/ 2>/dev/null || true',
                cwd='/code/workspace'
            )
            
            if copy_exit_code == 0:
                if self.debug:
                    print('✅ [BASELINE] Copied baseline files to expected location')
            else:
                if self.debug:
                    print(f'⚠️  [BASELINE] Copy had issues: {copy_stderr}')
                    
            return {'success': True, 'copy_exit_code': copy_exit_code}
            
        except Exception as e:
            return {'success': False, 'error': f'File copy error: {str(e)}'}
    
    def _fix_diff_filename_case(self, verilog_diff: str) -> str:
        """Fix filename case in diff to match actual files in container."""
        # This is a simplified version - the original has more complex logic
        # You might need to implement more sophisticated case fixing based on your needs
        return verilog_diff