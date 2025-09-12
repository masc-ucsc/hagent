"""
Docker filesystem implementation for HAgent.

Provides filesystem operations that work inside Docker containers
for Docker execution mode.
"""

import posixpath
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

    def read_file(self, path: str, encoding: Optional[str] = 'utf-8') -> str:
        if encoding is None:
            # Binary mode - read as base64 to handle binary content safely
            cmd = f"python3 -c \"import base64; print(base64.b64encode(open('{path}', 'rb').read()).decode())\""
            exit_code, content, stderr = self.container_manager.run_cmd(cmd, quiet=True)
            if exit_code != 0:
                raise FileNotFoundError(f'Cannot read {path}: {stderr}')

            import base64

            # Return as string representation of bytes using latin1
            return base64.b64decode(content.strip()).decode('latin1')
        else:
            # Text mode
            exit_code, content, stderr = self.container_manager.run_cmd(f'cat "{path}"', quiet=True)
            if exit_code != 0:
                raise FileNotFoundError(f'Cannot read {path}: {stderr}')
            return content

    def write_file(self, path: str, content: str, encoding: Optional[str] = 'utf-8') -> bool:
        try:
            # Ensure parent directory exists
            # Use POSIX semantics inside the container
            parent_dir = posixpath.dirname(path)
            if parent_dir:
                self.container_manager.run_cmd(f'mkdir -p "{parent_dir}"', quiet=True)

            if encoding is None:
                # Binary mode - content is string representation of bytes
                import base64

                binary_content = content.encode('latin1')  # Convert back to bytes
                encoded_content = base64.b64encode(binary_content).decode('ascii')
                cmd = f"python3 -c \"import base64; open('{path}', 'wb').write(base64.b64decode('{encoded_content}'))\""
            else:
                # Text mode - use base64 encoding to avoid shell escaping issues
                import base64

                encoded_content = base64.b64encode(content.encode(encoding)).decode('ascii')
                cmd = f"python3 -c \"import base64; open('{path}', 'w', encoding='{encoding}').write(base64.b64decode('{encoded_content}').decode('{encoding}'))\""

            exit_code, _, _ = self.container_manager.run_cmd(cmd, quiet=True)
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

        return self.container_manager.run_cmd(command)

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