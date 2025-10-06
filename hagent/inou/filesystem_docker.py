"""
Docker filesystem implementation for HAgent.

Provides filesystem operations that work inside Docker containers
for Docker execution mode.
"""

import io
import posixpath
import tarfile
from typing import List, Dict, Tuple, Optional

from .filesystem_base import FileSystem


class FileSystemDocker(FileSystem):
    """FileSystem implementation for Docker execution."""

    def __init__(self, container_manager):
        """
        Initialize with container manager.

        Args:
            container_manager: ContainerManager instance for Docker operations
        """
        self.container_manager = container_manager

    def exists(self, path: str) -> bool:
        exit_code, _, _ = self.container_manager.run_cmd(f'test -e "{path}"', quiet=True)
        return exit_code == 0

    def read_file(self, path: str, encoding: str) -> str:
        """Read file from Docker container using get_archive API."""
        try:
            # Use Docker's get_archive API to read the file
            # This avoids exec overhead
            container = self.container_manager.container

            # get_archive returns (tar_stream, stat_dict)
            tar_stream, _ = container.get_archive(path)

            # Extract the file content from tar stream
            tar_bytes = b''.join(tar_stream)
            tar_buffer = io.BytesIO(tar_bytes)

            with tarfile.open(fileobj=tar_buffer, mode='r') as tar:
                # Get the first (and only) member
                members = tar.getmembers()
                if not members:
                    raise FileNotFoundError(f'No content in archive for {path}')

                member = members[0]
                file_obj = tar.extractfile(member)
                if file_obj is None:
                    raise FileNotFoundError(f'Cannot extract {path}')

                content_bytes = file_obj.read()

                if encoding is None:
                    # Binary mode - return as string representation of bytes
                    return content_bytes.decode('latin1')
                else:
                    # Text mode - decode with specified encoding
                    return content_bytes.decode(encoding)

        except Exception:
            # Fallback to old method if tar API fails
            if encoding is None:
                # Binary mode - read as base64 to handle binary content safely
                cmd = f"python3 -c \"import base64; print(base64.b64encode(open('{path}', 'rb').read()).decode())\""
                exit_code, content, stderr = self.container_manager.run_cmd(cmd, quiet=True, skip_profile=True)
                if exit_code != 0:
                    raise FileNotFoundError(f'Cannot read {path}: {stderr}')

                import base64

                # Return as string representation of bytes using latin1
                return base64.b64decode(content.strip()).decode('latin1')
            else:
                # Text mode
                exit_code, content, stderr = self.container_manager.run_cmd(f'cat "{path}"', quiet=True, skip_profile=True)
                if exit_code != 0:
                    raise FileNotFoundError(f'Cannot read {path}: {stderr}')
                return content

    def write_file(self, path: str, content: str, encoding: str) -> bool:
        """Write file to Docker container using put_archive API."""
        try:
            container = self.container_manager.container

            # Prepare file content as bytes
            if encoding is None:
                # Binary mode - content is string representation of bytes
                content_bytes = content.encode('latin1')
            else:
                # Text mode
                content_bytes = content.encode(encoding)

            # Create tar archive in memory
            tar_buffer = io.BytesIO()
            with tarfile.open(fileobj=tar_buffer, mode='w') as tar:
                # Create TarInfo for the file
                import time

                tarinfo = tarfile.TarInfo(name=posixpath.basename(path))
                tarinfo.size = len(content_bytes)
                tarinfo.mode = 0o644
                tarinfo.mtime = int(time.time())  # Set modification time to now

                # Add file to tar
                tar.addfile(tarinfo, io.BytesIO(content_bytes))

            tar_buffer.seek(0)
            tar_data = tar_buffer.read()

            # Get parent directory
            # If path is absolute, use its directory; if relative, resolve to absolute
            if posixpath.isabs(path):
                parent_dir = posixpath.dirname(path)
                if not parent_dir:
                    parent_dir = '/'
            else:
                # For relative paths, we need to resolve to absolute path first
                # Get current working directory from container
                exit_code, cwd_output, _ = self.container_manager.run_cmd('pwd', quiet=True, skip_profile=True)
                if exit_code == 0:
                    container_cwd = cwd_output.strip()
                    # Build absolute path
                    abs_path = posixpath.join(container_cwd, path)
                    parent_dir = posixpath.dirname(abs_path)
                    if not parent_dir:
                        parent_dir = container_cwd
                else:
                    # Fallback - use '.' but this might not work
                    parent_dir = posixpath.dirname(path) or '.'

            # Try to write using put_archive
            # put_archive puts files into the specified directory
            try:
                container.put_archive(parent_dir, tar_data)
                return True
            except Exception as put_err:
                # If put_archive fails (e.g., directory doesn't exist), create directory and retry
                if parent_dir and parent_dir not in ('/', '.'):
                    self.container_manager.run_cmd(f'mkdir -p "{parent_dir}"', quiet=True, skip_profile=True)
                    container.put_archive(parent_dir, tar_data)
                    return True
                else:
                    raise put_err

        except Exception:
            # Fallback to old method if tar API fails
            try:
                parent_dir = posixpath.dirname(path)
                if parent_dir:
                    self.container_manager.run_cmd(f'mkdir -p "{parent_dir}"', quiet=True, skip_profile=True)

                if encoding is None:
                    # Binary mode
                    import base64

                    binary_content = content.encode('latin1')
                    encoded_content = base64.b64encode(binary_content).decode('ascii')
                    cmd = f"python3 -c \"import base64; open('{path}', 'wb').write(base64.b64decode('{encoded_content}'))\""
                else:
                    # Text mode
                    import base64

                    encoded_content = base64.b64encode(content.encode(encoding)).decode('ascii')
                    cmd = f"python3 -c \"import base64; open('{path}', 'w', encoding='{encoding}').write(base64.b64decode('{encoded_content}').decode('{encoding}'))\""

                exit_code, _, _ = self.container_manager.run_cmd(cmd, quiet=True, skip_profile=True)
                return exit_code == 0
            except Exception:
                return False

    def list_dir(self, path: str) -> List[str]:
        exit_code, output, _ = self.container_manager.run_cmd(f'ls -1 "{path}" 2>/dev/null || true', quiet=True)
        if exit_code != 0 or not output.strip():
            return []
        return [line.strip() for line in output.strip().split('\n') if line.strip()]

    def makedirs(self, path: str, exist_ok: bool = True) -> bool:
        cmd = f'mkdir -p "{path}"' if exist_ok else f'mkdir "{path}"'
        exit_code, _, _ = self.container_manager.run_cmd(cmd, quiet=True)
        return exit_code == 0

    def remove(self, path: str) -> bool:
        exit_code, _, _ = self.container_manager.run_cmd(f'rm -rf "{path}"', quiet=True)
        return exit_code == 0

    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = True
    ) -> Tuple[int, str, str]:
        """Execute command in Docker container."""
        # Build command with environment variables and working directory
        if env:
            env_vars = ' '.join(f'{k}={repr(v)}' for k, v in env.items())
            command = f'export {env_vars} && {command}'

        if cwd and cwd != '.':
            command = f'cd "{cwd}" && {command}'

        return self.container_manager.run_cmd(command, quiet=quiet)

    def resolve_path(self, path: str) -> str:
        """Resolve to absolute container path."""
        # Use POSIX semantics; do not use host os.path in docker mode
        if posixpath.isabs(path):
            return path

        # For Docker, resolve relative to container working directory
        # This may need adjustment based on container setup
        exit_code, pwd_output, _ = self.container_manager.run_cmd('pwd', quiet=True)
        if exit_code == 0:
            container_cwd = pwd_output.strip()
            return posixpath.join(container_cwd, path)

        # Fallback: return the path unchanged (avoid host-specific resolution)
        return path
