"""
BaselineVerilogGenerator component for v2chisel_batch refactoring.

This component handles generation of baseline Verilog files from pristine Chisel code,
which are used as the reference for golden design creation and LEC verification.
"""

from typing import Dict, Optional, List, Any
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
        
    def generate_fresh_baseline(self, docker_container: Optional[str] = None) -> Dict[str, Any]:
        """
        Generate fresh baseline Verilog from pristine Chisel code.
        
        This method:
        1. Compiles pristine Chisel code to generate Verilog
        2. Copies generated files to expected baseline location
        3. Returns success status and file information
        
        Args:
            docker_container: Container name (optional, Builder handles this)
            
        Returns:
            Dict with success status, files info, and any errors
        """
        if self.debug:
            print('🏭 [BASELINE] Generating fresh baseline Verilog from pristine Chisel...')
        
        try:
            # Generate Verilog using the DINO SingleCycleCPU command
            if self.debug:
                print('🔧 [BASELINE] Running: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')
            
            exit_code, stdout, stderr = self.builder.run_cmd(
                'bash -l -c \'cd /code/workspace/repo && sbt "runMain dinocpu.SingleCycleCPUNoDebug"\''
            )
            
            if exit_code == 0:
                if self.debug:
                    print('✅ [BASELINE] Fresh baseline Verilog generated successfully')
                    print('     Command used: sbt "runMain dinocpu.SingleCycleCPUNoDebug"')
                
                # Copy generated files from build_singlecyclecpu_d to build_singlecyclecpu_nd
                copy_result = self._copy_baseline_files()
                
                if copy_result['success']:
                    if self.debug:
                        print('✅ [BASELINE] Copied baseline files to expected location')
                    
                    # Find and catalog the generated files
                    verilog_files = self._find_baseline_verilog_files()
                    
                    return {
                        'success': True,
                        'command_used': 'sbt "runMain dinocpu.SingleCycleCPUNoDebug"',
                        'files': verilog_files,
                        'stdout': stdout,
                        'copy_result': copy_result
                    }
                else:
                    if self.debug:
                        print(f'⚠️  [BASELINE] File copy failed: {copy_result.get("error", "Unknown error")}')
                    return {
                        'success': False,
                        'error': f'Baseline file copy failed: {copy_result.get("error", "Unknown")}',
                        'generation_success': True,
                        'copy_success': False
                    }
            else:
                error_msg = f'Fresh baseline Verilog generation failed: {stderr}'
                if self.debug:
                    print(f'❌ [BASELINE] {error_msg}')
                return {'success': False, 'error': error_msg}
                
        except Exception as e:
            error_msg = f'Fresh baseline generation failed: {str(e)}'
            if self.debug:
                print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}
    
    def _copy_baseline_files(self) -> Dict[str, Any]:
        """
        Copy generated baseline files to expected location.
        
        Returns:
            Dict with success status and copy information
        """
        try:
            # Create target directory
            mkdir_exit_code, _, mkdir_stderr = self.builder.run_cmd(
                'mkdir -p /code/workspace/build/build_singlecyclecpu_nd'
            )
            
            if mkdir_exit_code != 0:
                return {'success': False, 'error': f'Failed to create target directory: {mkdir_stderr}'}
            
            # Copy files from build_singlecyclecpu_d to build_singlecyclecpu_nd
            cp_exit_code, cp_stdout, cp_stderr = self.builder.run_cmd(
                'cp -r /code/workspace/build/build_singlecyclecpu_d/* /code/workspace/build/build_singlecyclecpu_nd/'
            )
            
            if cp_exit_code == 0:
                if self.debug:
                    print('✅ [BASELINE] Copied generated files to baseline location')
                return {'success': True, 'copied_files': True}
            else:
                return {'success': False, 'error': f'File copy failed: {cp_stderr}'}
                
        except Exception as e:
            return {'success': False, 'error': f'Copy operation failed: {str(e)}'}
    
    def _find_baseline_verilog_files(self) -> Dict[str, str]:
        """
        Find and catalog baseline Verilog files.
        
        Returns:
            Dict mapping relative paths to absolute paths of Verilog files
        """
        try:
            # Find all .sv files in the baseline directory
            exit_code, stdout, stderr = self.builder.run_cmd(
                'find /code/workspace/build/build_singlecyclecpu_nd -name "*.sv" -type f'
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
                    print('⚠️  [BASELINE] No Verilog files found in baseline directory')
            
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
                
                return {
                    'success': True,
                    'backup_dir': backup_dir,
                    'files': backed_up_files,
                    'file_count': len(backed_up_files)
                }
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
                return {
                    'success': False,
                    'error': 'No baseline Verilog files found',
                    'file_count': 0
                }
            
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
                
                return {
                    'success': True,
                    'files': accessible_files,
                    'file_count': len(accessible_files)
                }
            else:
                return {
                    'success': False,
                    'error': 'No baseline Verilog files are accessible',
                    'file_count': 0
                }
                
        except Exception as e:
            error_msg = f'Baseline verification failed: {str(e)}'
            if self.debug:
                print(f'❌ [BASELINE] {error_msg}')
            return {'success': False, 'error': error_msg}