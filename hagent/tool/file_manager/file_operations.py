import os
import tarfile
import io
from typing import Optional, List, Dict, Set


class FileOperations:
    """Handles all file operations including copying, tracking, and content retrieval."""

    def __init__(self, file_manager):
        """Initialize with reference to main File_manager instance."""
        self.fm = file_manager
        self._tracked_individual_files: Set[str] = set()  # For track_file tracked individual files
        self._tracked_dirs: List[Dict[str, str]] = []  # For track_dir: [{'path': '/abs/path', 'ext': '.scala'}, ...]
        self._temp_dir: Optional[str] = None

    def _resolve_container_path(self, path: str) -> str:
        """Resolve a path relative to _workdir unless it's absolute."""
        if os.path.isabs(path):
            return path
        return os.path.join(self.fm._workdir, path)

    def _check_file_exists(self, container_path: str) -> bool:
        """Check if a file exists in the container."""
        full_path = self._resolve_container_path(container_path)
        try:
            exit_code, _, _ = self.fm._docker.run(f'test -f "{full_path}"', quiet=True)
            return exit_code == 0
        except Exception:
            return False

    def copy_file(self, host_path: str, container_path: Optional[str] = '.') -> bool:
        """Copies a single file from the host into the container's tracked directory."""
        if self.fm._state != 'CONFIGURED':
            self.fm.error_message = f'copy_file must be called after setup(). {self.fm._state}'
            return False

        try:
            # Read the file content from host
            with open(host_path, 'rb') as f:
                file_content = f.read()

            filename = os.path.basename(host_path)

            # Determine the destination path in container
            if container_path == '.':
                # Copy to working directory with same filename
                dest_path = self.fm._workdir
                final_container_path = filename
            elif container_path.endswith('/') or not os.path.splitext(container_path)[1]:
                # container_path is a directory
                dest_path = os.path.join(self.fm._workdir, container_path.rstrip('/'))
                final_container_path = os.path.join(container_path.rstrip('/'), filename)
            else:
                # container_path includes filename
                dest_path = os.path.join(self.fm._workdir, os.path.dirname(container_path))
                final_container_path = container_path
                filename = os.path.basename(container_path)

            # Create tar archive in memory
            tar_stream = io.BytesIO()
            tar = tarfile.open(fileobj=tar_stream, mode='w')

            # Add file to tar with appropriate ownership and permissions
            tarinfo = tarfile.TarInfo(name=filename)
            tarinfo.size = len(file_content)
            tarinfo.mode = 0o666  # Read-write for everyone

            # Get current user info from container to set correct ownership
            try:
                user_info = self.fm._docker.container.exec_run('id -u && id -g && whoami')
                if user_info.exit_code == 0:
                    lines = user_info.output.decode('utf-8').strip().split('\n')
                    if len(lines) >= 3:
                        tarinfo.uid = int(lines[0])  # uid
                        tarinfo.gid = int(lines[1])  # gid
                        tarinfo.uname = lines[2]  # username
                        # Try to get group name (may fail, use gid as fallback)
                        group_info = self.fm._docker.container.exec_run('id -gn')
                        if group_info.exit_code == 0:
                            tarinfo.gname = group_info.output.decode('utf-8').strip()
                        else:
                            tarinfo.gname = str(tarinfo.gid)
                else:
                    # Fallback to safe defaults if user detection fails
                    tarinfo.uid = 0
                    tarinfo.gid = 0
                    tarinfo.uname = 'root'
                    tarinfo.gname = 'root'
            except Exception:
                # Fallback to safe defaults on any error
                tarinfo.uid = 0
                tarinfo.gid = 0
                tarinfo.uname = 'root'
                tarinfo.gname = 'root'

            tar.addfile(tarinfo, io.BytesIO(file_content))
            tar.close()

            # Reset stream position
            tar_stream.seek(0)

            # Ensure the destination directory exists
            if dest_path != self.fm._workdir:
                self.fm._docker._ensure_container_directory(dest_path)

            # Copy to container using put_archive
            success = self.fm._docker.container.put_archive(path=dest_path, data=tar_stream.getvalue())

            if success:
                # No need to fix permissions since we set them in the tar archive

                print(f"Successfully copied '{host_path}' to container path '{final_container_path}'")
                return True
            else:
                self.fm.error_message = f"Failed to copy file '{host_path}' to container"
                return False

        except Exception as e:
            self.fm.error_message = f"Failed to copy file '{host_path}': {e}"
            return False
