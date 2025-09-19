"""
BackupManager component for v2chisel_batch refactoring.

This component handles all backup and restore operations for Chisel files
during the bug fixing process, including master backups and incremental backups.
"""

from typing import Dict, List, Any
import time
import re


class BackupManager:
    """
    Handles backup and restore operations for Chisel files.

    This component is responsible for:
    1. Creating master backups at the start of bug processing
    2. Creating incremental file backups during iteration
    3. Restoring files to original or backup states
    4. Tracking files for restoration
    5. Cleanup of backup directories
    """

    def __init__(self, builder, debug: bool = True):
        """
        Initialize BackupManager.

        Args:
            builder: Builder instance for Docker/local operations
            debug: Enable debug output
        """
        self.builder = builder
        self.debug = debug
        self.files_to_restore = []

    def track_file_for_restoration(self, file_path: str) -> None:
        """
        Track a file that needs to be restored after the test.

        Args:
            file_path: Path to the file to track for restoration
        """
        if file_path not in self.files_to_restore:
            self.files_to_restore.append(file_path)
            if self.debug:
                print(f'📝 [TRACK] Will restore: {file_path}')

    def restore_all_tracked_files(self) -> Dict[str, Any]:
        """
        Restore all files that were modified during the test.

        Returns:
            Dict with restoration results and status
        """
        if self.debug:
            print(f'🔄 [RESTORE] Restoring {len(self.files_to_restore)} modified files and cleaning Docker state...')

        try:
            restored_files = []
            failed_files = []

            # Step 1: Restore all tracked files using git checkout
            if self.files_to_restore:
                for file_path in self.files_to_restore:
                    # Convert Docker path to git-relative path
                    if file_path.startswith('/code/workspace/repo/'):
                        git_path = file_path.replace('/code/workspace/repo/', '')

                        # Use git checkout to restore the file
                        exit_code, stdout, stderr = self.builder.run_cmd(f'git checkout -- {git_path}')

                        if exit_code == 0:
                            restored_files.append(git_path)
                            if self.debug:
                                print(f'     ✅ Restored: {git_path}')
                        else:
                            failed_files.append(git_path)
                            if self.debug:
                                print(f'     ❌ Failed to restore: {git_path} - {stderr}')

            # Clear the tracking list
            self.files_to_restore.clear()

            if self.debug:
                print(f'🔄 [RESTORE] Completed restoration: {len(restored_files)} success, {len(failed_files)} failed')

            return {
                'success': len(failed_files) == 0,
                'restored_files': restored_files,
                'failed_files': failed_files,
                'total_processed': len(restored_files) + len(failed_files),
            }

        except Exception as e:
            error_msg = f'Tracked file restoration failed: {str(e)}'
            if self.debug:
                print(f'❌ [RESTORE] {error_msg}')
            return {'success': False, 'error': error_msg}

    def create_master_backup(self, docker_container: str, chisel_diff: str) -> Dict[str, Any]:
        """
        Create MASTER backup of original files at the start of bug processing.

        Args:
            docker_container: Docker container name
            chisel_diff: The diff containing files to be modified

        Returns:
            Dict with backup results and information
        """
        if self.debug:
            print('💾 [MASTER_BACKUP] Creating master backup of original files...')

        try:
            # Parse the diff to find files that will be modified throughout ALL iterations
            files_to_backup = set()
            diff_lines = chisel_diff.split('\n')

            for line in diff_lines:
                # Look for unified diff file headers: --- a/path/file.scala or +++ b/path/file.scala
                if line.startswith('---') or line.startswith('+++'):
                    # Extract file path
                    match = re.search(r'[ab]/(.*\.scala)', line)
                    if match:
                        file_path = match.group(1)
                        # Convert relative path to absolute path in container
                        if not file_path.startswith('/code/workspace/repo/'):
                            file_path = f'/code/workspace/repo/{file_path}'
                        files_to_backup.add(file_path)

            # Create MASTER backup directory (this will persist for the entire bug processing)
            backup_id = f'master_backup_{int(time.time())}'
            backup_dir = f'/tmp/chisel_master_backup_{backup_id}'

            # Create backup directory in container
            exit_code, _, stderr = self.builder.run_cmd(f'mkdir -p {backup_dir}')
            if exit_code != 0:
                raise Exception(f'Failed to create backup directory {backup_dir}: {stderr}')

            backed_up_files = []

            if not files_to_backup:
                if self.debug:
                    print('     ⚠️  No Scala files found in diff - will create backup for original Verilog only')

            for file_path in files_to_backup:
                # Check if file exists before backing up
                check_exit_code, _, _ = self.builder.run_cmd(f'test -f {file_path}')

                if check_exit_code == 0:
                    # Create backup filename that preserves directory structure
                    backup_filename = file_path.replace('/', '_').replace('_code_workspace_repo_', '')
                    backup_path = f'{backup_dir}/{backup_filename}'

                    # Copy file to backup directory
                    cp_exit_code, _, cp_stderr = self.builder.run_cmd(f'cp {file_path} {backup_path}')

                    if cp_exit_code == 0:
                        backed_up_files.append(
                            {'original_path': file_path, 'backup_path': backup_path, 'backup_filename': backup_filename}
                        )
                        if self.debug:
                            print(f'     ✅ Master backup created: {file_path}')
                    else:
                        if self.debug:
                            print(f'     ❌ Failed to backup {file_path}: {cp_stderr}')
                else:
                    if self.debug:
                        print(f'     ⚠️  File does not exist, skipping: {file_path}')

            if backed_up_files:
                if self.debug:
                    print(f'✅ [MASTER_BACKUP] Successfully created master backup with {len(backed_up_files)} files')
                    print(f'     Backup ID: {backup_id}')
                    print(f'     Backup directory: {backup_dir}')

                return {
                    'success': True,
                    'backup_id': backup_id,
                    'backup_dir': backup_dir,
                    'files_backed_up': backed_up_files,
                    'file_count': len(backed_up_files),
                }
            else:
                if self.debug:
                    print('⚠️  [MASTER_BACKUP] No files were successfully backed up')
                return {
                    'success': True,  # Not an error if no files to backup
                    'backup_id': backup_id,
                    'backup_dir': backup_dir,
                    'files_backed_up': [],
                    'file_count': 0,
                    'message': 'No files required backup',
                }

        except Exception as e:
            error_msg = f'Master backup creation failed: {str(e)}'
            if self.debug:
                print(f'❌ [MASTER_BACKUP] {error_msg}')
            return {'success': False, 'error': error_msg}

    def create_file_backup(self, docker_container: str, chisel_diff: str) -> Dict[str, Any]:
        """
        Create incremental backup for a specific iteration.

        Args:
            docker_container: Docker container name
            chisel_diff: The diff containing files to be modified

        Returns:
            Dict with backup results and information
        """
        if self.debug:
            print('💾 [FILE_BACKUP] Creating incremental backup...')

        try:
            # Parse diff to find files to backup
            files_to_backup = set()
            diff_lines = chisel_diff.split('\n')

            for line in diff_lines:
                if line.startswith('---') or line.startswith('+++'):
                    match = re.search(r'[ab]/(.*\.scala)', line)
                    if match:
                        file_path = match.group(1)
                        if not file_path.startswith('/code/workspace/repo/'):
                            file_path = f'/code/workspace/repo/{file_path}'
                        files_to_backup.add(file_path)

            # Create incremental backup directory
            backup_id = f'iter_backup_{int(time.time())}'
            backup_dir = f'/tmp/chisel_iter_backup_{backup_id}'

            exit_code, _, stderr = self.builder.run_cmd(f'mkdir -p {backup_dir}')
            if exit_code != 0:
                raise Exception(f'Failed to create backup directory {backup_dir}: {stderr}')

            backed_up_files = []

            for file_path in files_to_backup:
                check_exit_code, _, _ = self.builder.run_cmd(f'test -f {file_path}')

                if check_exit_code == 0:
                    backup_filename = file_path.replace('/', '_').replace('_code_workspace_repo_', '')
                    backup_path = f'{backup_dir}/{backup_filename}'

                    cp_exit_code, _, cp_stderr = self.builder.run_cmd(f'cp {file_path} {backup_path}')

                    if cp_exit_code == 0:
                        backed_up_files.append(
                            {'original_path': file_path, 'backup_path': backup_path, 'backup_filename': backup_filename}
                        )
                        if self.debug:
                            print(f'     ✅ Incremental backup: {file_path}')
                    else:
                        if self.debug:
                            print(f'     ❌ Failed to backup {file_path}: {cp_stderr}')

            if self.debug:
                print(f'✅ [FILE_BACKUP] Created incremental backup with {len(backed_up_files)} files (ID: {backup_id})')

            return {
                'success': True,
                'backup_id': backup_id,
                'backup_dir': backup_dir,
                'files_backed_up': backed_up_files,
                'file_count': len(backed_up_files),
            }

        except Exception as e:
            error_msg = f'Incremental backup creation failed: {str(e)}'
            if self.debug:
                print(f'❌ [FILE_BACKUP] {error_msg}')
            return {'success': False, 'error': error_msg}

    def restore_to_original(
        self, docker_container: str, master_backup_info: Dict[str, Any], reason: str = 'failure'
    ) -> Dict[str, Any]:
        """
        Restore files to ORIGINAL pristine state from master backup.

        Args:
            docker_container: Docker container name
            master_backup_info: Master backup information dict
            reason: Reason for restoration

        Returns:
            Dict with restoration results
        """
        if not master_backup_info or not master_backup_info.get('success') or not master_backup_info.get('files_backed_up'):
            return {'success': True, 'message': 'No master backup to restore from'}

        if self.debug:
            print(f'🔄 [RESTORE_TO_ORIGINAL] Restoring to pristine state due to: {reason}')
            print(f'     🔒 Using master backup: {master_backup_info["backup_id"]}')
            print(f'     📁 Files to restore: {len(master_backup_info.get("files_backed_up", []))}')

        try:
            restored_files = []
            failed_files = []

            for file_info in master_backup_info['files_backed_up']:
                original_path = file_info['original_path']
                backup_path = file_info['backup_path']

                # Check if backup file exists
                check_exit_code, _, _ = self.builder.run_cmd(f'test -f {backup_path}')
                if check_exit_code != 0:
                    if self.debug:
                        print(f'     ❌ Backup file does not exist: {backup_path}')
                    failed_files.append(original_path)
                    continue

                # Restore the file from MASTER backup (original state)
                cp_exit_code, _, cp_stderr = self.builder.run_cmd(f'cp {backup_path} {original_path}')

                if cp_exit_code == 0:
                    restored_files.append(original_path)
                    if self.debug:
                        print(f'     ✅ Restored to original: {original_path}')

                        # Verify restoration worked by showing first few lines
                        verify_exit_code, verify_stdout, _ = self.builder.run_cmd(f'head -3 {original_path}')
                        if verify_exit_code == 0 and verify_stdout:
                            first_line = verify_stdout.split('\n')[0]
                            print(f'          First line now: {first_line}')
                else:
                    failed_files.append(original_path)
                    if self.debug:
                        print(f'     ❌ Failed to restore {original_path}: {cp_stderr}')

            if self.debug:
                print(f'🔄 [RESTORE_TO_ORIGINAL] Restored {len(restored_files)} files to pristine state')

            return {
                'success': len(failed_files) == 0,
                'restored_files': restored_files,
                'failed_files': failed_files,
                'restore_reason': reason,
            }

        except Exception as e:
            error_msg = f'Restore to original failed: {str(e)}'
            if self.debug:
                print(f'❌ [RESTORE_TO_ORIGINAL] {error_msg}')
            return {'success': False, 'error': error_msg}

    def restore_from_backup(self, docker_container: str, backup_info: Dict[str, Any]) -> Dict[str, Any]:
        """
        Restore files from an incremental backup.

        Args:
            docker_container: Docker container name
            backup_info: Backup information dict

        Returns:
            Dict with restoration results
        """
        if not backup_info or not backup_info.get('success') or not backup_info.get('files_backed_up'):
            return {'success': True, 'message': 'No backup to restore from'}

        if self.debug:
            print(f'🔄 [RESTORE_FROM_BACKUP] Restoring from incremental backup: {backup_info["backup_id"]}')
            print(f'     📁 Files to restore: {len(backup_info.get("files_backed_up", []))}')

        try:
            restored_files = []
            failed_files = []

            for file_info in backup_info['files_backed_up']:
                original_path = file_info['original_path']
                backup_path = file_info['backup_path']

                # Check if backup file exists
                check_exit_code, _, _ = self.builder.run_cmd(f'test -f {backup_path}')
                if check_exit_code != 0:
                    if self.debug:
                        print(f'     ❌ Backup file does not exist: {backup_path}')
                    failed_files.append(original_path)
                    continue

                # Restore the file from backup
                cp_exit_code, _, cp_stderr = self.builder.run_cmd(f'cp {backup_path} {original_path}')

                if cp_exit_code == 0:
                    restored_files.append(original_path)
                    if self.debug:
                        print(f'     ✅ Restored from backup: {original_path}')
                else:
                    failed_files.append(original_path)
                    if self.debug:
                        print(f'     ❌ Failed to restore {original_path}: {cp_stderr}')

            if self.debug:
                print(f'🔄 [RESTORE_FROM_BACKUP] Restored {len(restored_files)} files from backup')

            return {
                'success': len(failed_files) == 0,
                'restored_files': restored_files,
                'failed_files': failed_files,
                'backup_id': backup_info.get('backup_id'),
            }

        except Exception as e:
            error_msg = f'Restore from backup failed: {str(e)}'
            if self.debug:
                print(f'❌ [RESTORE_FROM_BACKUP] {error_msg}')
            return {'success': False, 'error': error_msg}

    def cleanup_master_backup(self, docker_container: str, master_backup_info: Dict[str, Any]) -> None:
        """
        Clean up master backup directory and files.

        Args:
            docker_container: Docker container name
            master_backup_info: Master backup information dict
        """
        if not master_backup_info or not master_backup_info.get('backup_dir'):
            return

        try:
            backup_dir = master_backup_info['backup_dir']

            if self.debug:
                print(f'🧹 [CLEANUP_MASTER] Removing master backup directory: {backup_dir}')

            exit_code, _, stderr = self.builder.run_cmd(f'rm -rf {backup_dir}')

            if exit_code == 0:
                if self.debug:
                    print('✅ [CLEANUP_MASTER] Successfully removed backup directory')
            else:
                if self.debug:
                    print(f'⚠️  [CLEANUP_MASTER] Failed to remove backup directory: {stderr}')

        except Exception as e:
            if self.debug:
                print(f'⚠️  [CLEANUP_MASTER] Error during cleanup: {str(e)}')

    def cleanup_backup(self, docker_container: str, backup_info: Dict[str, Any]) -> None:
        """
        Clean up incremental backup directory and files.

        Args:
            docker_container: Docker container name
            backup_info: Backup information dict
        """
        if not backup_info or not backup_info.get('backup_dir'):
            return

        try:
            backup_dir = backup_info['backup_dir']

            if self.debug:
                print(f'🧹 [CLEANUP_BACKUP] Removing backup directory: {backup_dir}')

            exit_code, _, stderr = self.builder.run_cmd(f'rm -rf {backup_dir}')

            if exit_code == 0:
                if self.debug:
                    print('✅ [CLEANUP_BACKUP] Successfully removed backup directory')
            else:
                if self.debug:
                    print(f'⚠️  [CLEANUP_BACKUP] Failed to remove backup directory: {stderr}')

        except Exception as e:
            if self.debug:
                print(f'⚠️  [CLEANUP_BACKUP] Error during cleanup: {str(e)}')

    def get_tracked_files(self) -> List[str]:
        """
        Get list of currently tracked files for restoration.

        Returns:
            List of file paths being tracked
        """
        return self.files_to_restore.copy()

    def clear_tracked_files(self) -> None:
        """Clear the list of tracked files."""
        self.files_to_restore.clear()
        if self.debug:
            print('🧹 [TRACK] Cleared tracked files list')
