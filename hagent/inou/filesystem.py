"""
Unified FileSystem interface for HAgent

Eliminates local/docker branching by providing a single abstraction
that works transparently in both execution modes.
"""

import os
import subprocess
import sys
from abc import ABC, abstractmethod
from pathlib import Path
from typing import List, Dict, Tuple, Optional


class FileSystem(ABC):
    """
    Abstract file system interface that works in both local and Docker modes.

    This eliminates the need for if/else branches based on execution mode
    by providing a unified interface for all file operations.
    """

    @abstractmethod
    def exists(self, path: str) -> bool:
        """Check if file or directory exists."""
        pass

    @abstractmethod
    def read_file(self, path: str, encoding: Optional[str] = 'utf-8') -> str:
        """Read file content. Returns text by default, or bytes if encoding=None."""
        pass

    @abstractmethod
    def write_file(self, path: str, content: str, encoding: Optional[str] = 'utf-8') -> bool:
        """Write file content. Accepts text by default, or bytes if encoding=None."""
        pass

    @abstractmethod
    def list_dir(self, path: str) -> List[str]:
        """List directory contents."""
        pass

    @abstractmethod
    def makedirs(self, path: str, exist_ok: bool = True) -> bool:
        """Create directory structure."""
        pass

    @abstractmethod
    def remove(self, path: str) -> bool:
        """Remove file or directory."""
        pass

    @abstractmethod
    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = True
    ) -> Tuple[int, str, str]:
        """Execute command in the appropriate context."""
        pass

    @abstractmethod
    def resolve_path(self, path: str) -> str:
        """Resolve path to absolute form appropriate for this filesystem."""
        pass

    # Backward compatibility methods (deprecated)
    def read_text(self, path: str, encoding: str = 'utf-8') -> str:
        """Deprecated: use read_file() instead."""
        return self.read_file(path, encoding)

    def write_text(self, path: str, content: str, encoding: str = 'utf-8') -> bool:
        """Deprecated: use write_file() instead."""
        return self.write_file(path, content, encoding)

    def read_binary(self, path: str) -> bytes:
        """Deprecated: use read_file(path, encoding=None).encode('latin1') instead."""
        return self.read_file(path, encoding=None).encode('latin1')

    def write_binary(self, path: str, content: bytes) -> bool:
        """Deprecated: use write_file(path, content.decode('latin1'), encoding=None) instead."""
        return self.write_file(path, content.decode('latin1'), encoding=None)


class LocalFileSystem(FileSystem):
    """FileSystem implementation for local execution."""

    def exists(self, path: str) -> bool:
        return os.path.exists(path)

    def read_file(self, path: str, encoding: Optional[str] = 'utf-8') -> str:
        try:
            if encoding is None:
                # Binary mode - return content as string representation of bytes
                with open(path, 'rb') as f:
                    return f.read().decode('latin1')  # Use latin1 for byte preservation
            else:
                # Text mode
                with open(path, 'r', encoding=encoding) as f:
                    return f.read()
        except IOError as e:
            raise FileNotFoundError(f'Cannot read {path}: {e}')

    def write_file(self, path: str, content: str, encoding: Optional[str] = 'utf-8') -> bool:
        try:
            # Ensure parent directory exists
            parent = os.path.dirname(path)
            if parent:
                os.makedirs(parent, exist_ok=True)

            if encoding is None:
                # Binary mode - content should be string representation of bytes
                with open(path, 'wb') as f:
                    f.write(content.encode('latin1'))  # Use latin1 for byte preservation
            else:
                # Text mode
                with open(path, 'w', encoding=encoding) as f:
                    f.write(content)
            return True
        except IOError:
            return False

    def list_dir(self, path: str) -> List[str]:
        try:
            return os.listdir(path)
        except OSError:
            return []

    def makedirs(self, path: str, exist_ok: bool = True) -> bool:
        try:
            os.makedirs(path, exist_ok=exist_ok)
            return True
        except OSError:
            return False

    def remove(self, path: str) -> bool:
        try:
            if os.path.isdir(path):
                import shutil

                shutil.rmtree(path)
            else:
                os.remove(path)
            return True
        except OSError:
            return False

    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = True
    ) -> Tuple[int, str, str]:
        """Execute command locally."""
        try:
            # Merge environment variables
            full_env = os.environ.copy()
            if env:
                full_env.update(env)

            # Always capture output to ensure tests work properly
            result = subprocess.run(
                command,
                shell=True,
                cwd=cwd,
                env=full_env,
                capture_output=True,
                text=True,
                timeout=300,  # 5 minute default timeout
            )

            # For non-quiet mode, also print to console for interactive use
            if not quiet:
                if result.stdout:
                    print(result.stdout, end='')
                if result.stderr:
                    print(result.stderr, end='', file=sys.stderr)

            return result.returncode, result.stdout, result.stderr

        except subprocess.TimeoutExpired:
            return -1, '', f'Command timed out: {command}'
        except Exception as e:
            return -1, '', f'Command failed: {e}'

    def resolve_path(self, path: str) -> str:
        """Resolve to absolute local path."""
        return str(Path(path).resolve())


class DockerFileSystem(FileSystem):
    """FileSystem implementation for Docker execution."""

    def __init__(self, container_manager):
        """
        Initialize with container manager.

        Args:
            container_manager: ContainerManager instance for Docker operations
        """
        self.container_manager = container_manager

    def exists(self, path: str) -> bool:
        exit_code, _, _ = self.container_manager.run_cmd(f'test -e "{path}"')
        return exit_code == 0

    def read_file(self, path: str, encoding: Optional[str] = 'utf-8') -> str:
        if encoding is None:
            # Binary mode - read as base64 to handle binary content safely
            cmd = f"python3 -c \"import base64; print(base64.b64encode(open('{path}', 'rb').read()).decode())\""
            exit_code, content, stderr = self.container_manager.run_cmd(cmd)
            if exit_code != 0:
                raise FileNotFoundError(f'Cannot read {path}: {stderr}')

            import base64

            # Return as string representation of bytes using latin1
            return base64.b64decode(content.strip()).decode('latin1')
        else:
            # Text mode
            exit_code, content, stderr = self.container_manager.run_cmd(f'cat "{path}"')
            if exit_code != 0:
                raise FileNotFoundError(f'Cannot read {path}: {stderr}')
            return content

    def write_file(self, path: str, content: str, encoding: Optional[str] = 'utf-8') -> bool:
        try:
            # Ensure parent directory exists
            parent_dir = os.path.dirname(path)
            if parent_dir:
                self.container_manager.run_cmd(f'mkdir -p "{parent_dir}"')

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

            exit_code, _, _ = self.container_manager.run_cmd(cmd)
            return exit_code == 0
        except Exception:
            return False

    def list_dir(self, path: str) -> List[str]:
        exit_code, output, _ = self.container_manager.run_cmd(f'ls -1 "{path}" 2>/dev/null || true')
        if exit_code != 0 or not output.strip():
            return []
        return [line.strip() for line in output.strip().split('\n') if line.strip()]

    def makedirs(self, path: str, exist_ok: bool = True) -> bool:
        cmd = f'mkdir -p "{path}"' if exist_ok else f'mkdir "{path}"'
        exit_code, _, _ = self.container_manager.run_cmd(cmd)
        return exit_code == 0

    def remove(self, path: str) -> bool:
        exit_code, _, _ = self.container_manager.run_cmd(f'rm -rf "{path}"')
        return exit_code == 0

    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = True
    ) -> Tuple[int, str, str]:
        """Execute command in Docker container."""
        # Build command with environment variables and working directory
        if env:
            env_vars = ' '.join(f'{k}="{v}"' for k, v in env.items())
            command = f'env {env_vars} {command}'

        if cwd and cwd != '.':
            command = f'cd "{cwd}" && {command}'

        return self.container_manager.run_cmd(command)

    def resolve_path(self, path: str) -> str:
        """Resolve to absolute container path."""
        if os.path.isabs(path):
            return path

        # For Docker, resolve relative to container working directory
        # This may need adjustment based on container setup
        exit_code, pwd_output, _ = self.container_manager.run_cmd('pwd')
        if exit_code == 0:
            container_cwd = pwd_output.strip()
            return os.path.join(container_cwd, path)

        # Fallback
        return os.path.abspath(path)


class FileSystemFactory:
    """Factory to create appropriate FileSystem implementation."""

    @staticmethod
    def create(container_manager=None) -> FileSystem:
        """
        Create appropriate FileSystem based on execution mode.

        Args:
            container_manager: ContainerManager for Docker mode (required if Docker)

        Returns:
            FileSystem implementation appropriate for current execution mode
        """
        execution_mode = os.environ.get('HAGENT_EXECUTION_MODE', 'local')

        if execution_mode == 'docker':
            if not container_manager:
                raise ValueError('ContainerManager required for Docker execution mode')
            return DockerFileSystem(container_manager)
        else:
            return LocalFileSystem()

    @staticmethod
    def create_for_builder(builder) -> FileSystem:
        """
        Create FileSystem for Builder instance.

        Args:
            builder: Builder instance with runner and container_manager

        Returns:
            Appropriate FileSystem implementation
        """
        if builder.is_docker_mode():
            return DockerFileSystem(builder.runner.container_manager)
        else:
            return LocalFileSystem()
