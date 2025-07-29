import os
import tarfile
import io
import shutil
import tempfile
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

    def _is_file_in_tracked_dir(self, file_path: str) -> bool:
        """Check if a file is in one of the tracked directories with matching extension."""
        for dir_entry in self._tracked_dirs:
            dir_path = dir_entry['path']
            ext_filter = dir_entry['ext']

            # Check if file is in this directory
            if file_path.startswith(dir_path + '/') or file_path == dir_path:
                # Check extension filter if specified
                if ext_filter is None or file_path.endswith(ext_filter):
                    return True
        return False

    def _ensure_temp_dir(self) -> bool:
        """Ensure temporary directory exists for tracking files."""
        if self._temp_dir is None:
            try:
                self._temp_dir = tempfile.mkdtemp(prefix='file_manager_')
                return True
            except Exception as e:
                self.fm.error_message = f'Failed to create temporary directory: {e}'
                return False
        return True

    def copy_dir(self, host_path: str, container_path: str = '.', ext: Optional[str] = None) -> bool:
        """Copies a host directory into the container. Must be called after setup()."""
        if self.fm._state not in ['CONFIGURED', 'EXECUTED']:
            self.fm.error_message = f'copy_dir must be called after setup(). {self.fm._state}'
            return False
        try:
            for root, _, files in os.walk(host_path):
                for file in files:
                    if ext and not file.endswith(ext):
                        continue

                    local_file_path = os.path.join(root, file)
                    relative_path = os.path.relpath(local_file_path, host_path)
                    dest_path = os.path.join(container_path, relative_path)

                    if not self.copy_file(local_file_path, dest_path):
                        return False
            return True
        except Exception as e:
            self.fm.error_message = f"Failed to copy directory '{host_path}': {e}"
            return False

    def copy_file(self, host_path: str, container_path: Optional[str] = '.') -> bool:
        """Copies a single file from the host into the container's tracked directory."""
        if self.fm._state not in ['CONFIGURED', 'EXECUTED']:
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

            # Add file to tar
            tarinfo = tarfile.TarInfo(name=filename)
            tarinfo.size = len(file_content)
            tarinfo.mode = 0o644
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
                print(f"Successfully copied '{host_path}' to container path '{final_container_path}'")
                return True
            else:
                self.fm.error_message = f"Failed to copy file '{host_path}' to container"
                return False

        except Exception as e:
            self.fm.error_message = f"Failed to copy file '{host_path}': {e}"
            return False

    def install_executable(self, host_path: str, container_path: Optional[str] = '/usr/local/bin') -> bool:
        """Install an executable file from the host into the container with execute permissions.

        Similar to copy_file but sets 755 permissions and defaults to /usr/local/bin for PATH access.

        Args:
            host_path: Path to the executable file on the host
            container_path: Destination directory in the container (default: /usr/local/bin)

        Returns:
            True if successful, False otherwise
        """
        if self.fm._state not in ['CONFIGURED', 'EXECUTED']:
            self.fm.error_message = f'install_executable must be called after setup(). {self.fm._state}'
            return False

        try:
            # Read the file content from host
            with open(host_path, 'rb') as f:
                file_content = f.read()

            filename = os.path.basename(host_path)

            # Determine the destination path in container
            if container_path == '/usr/local/bin' or container_path.endswith('/'):
                # container_path is a directory
                dest_path = container_path.rstrip('/')
                final_container_path = os.path.join(dest_path, filename)
            else:
                # container_path includes filename
                dest_path = os.path.dirname(container_path)
                final_container_path = container_path
                filename = os.path.basename(container_path)

            # Create tar archive in memory
            tar_stream = io.BytesIO()
            tar = tarfile.open(fileobj=tar_stream, mode='w')

            # Add file to tar with executable permissions (755)
            tarinfo = tarfile.TarInfo(name=filename)
            tarinfo.size = len(file_content)
            tarinfo.mode = 0o755  # rwxr-xr-x permissions
            tar.addfile(tarinfo, io.BytesIO(file_content))
            tar.close()

            # Reset stream position
            tar_stream.seek(0)

            # Ensure the destination directory exists
            self.fm._docker._ensure_container_directory(dest_path)

            # Copy to container using put_archive
            success = self.fm._docker.container.put_archive(path=dest_path, data=tar_stream.getvalue())

            if success:
                print(
                    f"Successfully installed executable '{host_path}' to container path '{final_container_path}' with 755 permissions"
                )
                return True
            else:
                self.fm.error_message = f"Failed to install executable '{host_path}' to container"
                return False

        except Exception as e:
            self.fm.error_message = f"Failed to install executable '{host_path}': {e}"
            return False

    def get_file_content(self, container_path: str, container=None) -> str:
        """Return the text content of a file from a container (defaults to main container)."""
        # Allow getting file content in EXECUTED state (and also CONFIGURED for flexibility)
        if self.fm._state not in ['CONFIGURED', 'EXECUTED']:
            self.fm.error_message = 'get_file_content must be called after setup().'
            return ''

        # Use provided container or default to main container
        target_container = container if container else self.fm._docker.container
        if not target_container:
            self.fm.error_message = 'No container available'
            return ''

        try:
            full_path = self._resolve_container_path(container_path)
            bits, stat = target_container.get_archive(full_path)

            with io.BytesIO() as bio:
                for chunk in bits:
                    bio.write(chunk)
                bio.seek(0)
                with tarfile.open(fileobj=bio, mode='r') as tar:
                    member = tar.getmembers()[0]
                    extracted_file = tar.extractfile(member)
                    content = extracted_file.read()

            try:
                return content.decode('utf-8')
            except UnicodeDecodeError:
                self.fm.error_message = f"File '{container_path}' is binary or has non-UTF-8 content."
                return ''
        except Exception as e:
            if 'not found' in str(e).lower():
                self.fm.error_message = f'File not found in container: {container_path}'
            else:
                self.fm.error_message = f'Failed to get file content: {e}'
            return ''

    def track_file(self, container_path: str) -> bool:
        """Track an existing file in the container for change detection."""
        if self.fm._state not in ['CONFIGURED', 'EXECUTED']:
            self.fm.error_message = 'track_file must be called after setup().'
            return False

        # Check if file exists
        if not self._check_file_exists(container_path):
            self.fm.error_message = f'File not found: {container_path}'
            return False

        try:
            # Simply record the path for tracking - use absolute path
            absolute_path = self._resolve_container_path(container_path)
            self._tracked_individual_files.add(absolute_path)
            print(f"Successfully tracking file '{container_path}' in container")
            return True

        except Exception as e:
            self.fm.error_message = f'Failed to track file {container_path}: {e}'
            return False

    def track_dir(self, container_path: str = '.', ext: Optional[str] = None) -> bool:
        """Track a directory for change detection. Files will be discovered dynamically in get_patch_dict."""
        if self.fm._state not in ['CONFIGURED', 'EXECUTED']:
            self.fm.error_message = 'track_dir must be called after setup().'
            return False

        try:
            # Resolve to absolute path
            absolute_path = self._resolve_container_path(container_path)

            # Check if directory exists
            exit_code, _, stderr = self.fm._docker.run(f'test -d "{absolute_path}"', quiet=True)
            if exit_code != 0:
                self.fm.error_message = f'Directory not found: {container_path}'
                return False

            # Store directory path and extension for later file discovery
            dir_entry = {'path': absolute_path, 'ext': ext}
            self._tracked_dirs.append(dir_entry)

            print(f"Successfully tracking directory '{container_path}' with extension filter '{ext}'")
            return True

        except Exception as e:
            self.fm.error_message = f'Failed to track directory {container_path}: {e}'
            return False

    def get_current_tracked_files(self, ext: Optional[str] = None) -> set:
        """Return a set of unique files currently being tracked.

        Args:
            ext: Optional extension filter. If provided, only returns files ending with this extension.

        Returns:
            Set of unique file paths that are currently tracked.
        """
        all_tracked_files = set()

        # Add files from _tracked_individual_files (track_file approach) - already absolute paths
        if ext:
            all_tracked_files.update(f for f in self._tracked_individual_files if f.endswith(ext))
        else:
            all_tracked_files.update(self._tracked_individual_files)

        # Add files from tracked directories (track_dir approach) - discover dynamically
        if self.fm._state in ['CONFIGURED', 'EXECUTED'] and self.fm._docker.container:
            for dir_entry in self._tracked_dirs:
                dir_path = dir_entry['path']
                dir_ext_filter = dir_entry['ext']

                # Skip this directory if both ext and dir_ext_filter are set but incompatible
                # (neither is a suffix of the other)
                if ext and dir_ext_filter:
                    if not (ext.endswith(dir_ext_filter) or dir_ext_filter.endswith(ext)):
                        continue

                # Find files in this tracked directory
                exit_code, out, stderr = self.fm._docker.run(f'find "{dir_path}" -type f', quiet=True)
                if exit_code == 0:
                    files = [f.strip() for f in out.strip().split('\n') if f.strip()]
                    for file_path in files:
                        # Apply directory extension filter if specified
                        if dir_ext_filter and not file_path.endswith(dir_ext_filter):
                            continue
                        # Apply method extension filter before normalization
                        if ext and not file_path.endswith(ext):
                            continue
                        # Normalize path to remove redundant "./"
                        normalized_path = os.path.normpath(file_path)
                        all_tracked_files.add(normalized_path)

        return all_tracked_files

    def _copy_file_from_container(self, container_path: str, temp_file_path: str) -> bool:
        """Copy a file from container to temporary location on host."""
        try:
            full_path = self._resolve_container_path(container_path)
            bits, stat = self.fm._docker.container.get_archive(full_path)

            with io.BytesIO() as bio:
                for chunk in bits:
                    bio.write(chunk)
                bio.seek(0)
                with tarfile.open(fileobj=bio, mode='r') as tar:
                    member = tar.getmembers()[0]
                    extracted_file = tar.extractfile(member)

                    # Write to temporary file
                    with open(temp_file_path, 'wb') as temp_file:
                        shutil.copyfileobj(extracted_file, temp_file)

            return True
        except Exception as e:
            self.fm.error_message = f'Failed to copy file from container: {e}'
            return False
