"""
Docker Executor for HAgent

Provides Docker command execution strategy that runs commands within Docker containers.
"""

import os
from pathlib import Path
from typing import Dict, Optional, Tuple

from .path_manager import PathManager
from .container_manager import ContainerManager


class DockerExecutor:
    """Execution strategy that runs commands within Docker containers."""

    def __init__(self, container_manager: ContainerManager):
        """
        Initialize DockerExecutor.

        Args:
            container_manager: ContainerManager instance for Docker operations
        """
        self.container_manager = container_manager

        # Container instance for reuse
        self._container = None
        self.error_message = ''

    def set_error(self, message: str) -> None:
        """Set error message following Tool pattern."""
        self.error_message = message

    def get_error(self) -> str:
        """Get current error message following Tool pattern."""
        return self.error_message

    def setup(self) -> bool:
        """
        Setup Docker execution environment.
        Working directory is always /code/workspace/repo.

        Returns:
            True if setup successful, False otherwise
        """
        success = self.container_manager.setup()
        if not success:
            self.set_error(f'Container setup failed: {self.container_manager.get_error()}')
        return success

    def set_cwd(self, new_workdir: str) -> bool:
        """
        Change the working directory with validation.

        Args:
            new_workdir: New working directory path (relative to /code/workspace/repo or absolute)

        Returns:
            True if successful, False if path doesn't exist
        """
        success = self.container_manager.set_cwd(new_workdir)
        if not success:
            self.set_error(self.container_manager.get_error())
        return success

    def get_cwd(self) -> str:
        """
        Get the current working directory.

        Returns:
            Current working directory path
        """
        return self.container_manager.get_cwd()

    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = False
    ) -> Tuple[int, str, str]:
        """
        Execute command using ContainerManager or File_manager (Docker).

        Args:
            command: The command to execute
            cwd: Working directory (will be converted for container, defaults to ".")
            env: Additional environment variables (set in the host environment, HAGENT vars are automatically included)
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        # Convert host paths to container paths if needed
        if cwd == '.':
            # Default to container's working directory instead of translating host path
            container_cwd = '.'  # ContainerManager will use its internal _workdir
        else:
            container_cwd = self._translate_path_to_container(cwd)

        # Set environment variables in the current process
        # (they'll be inherited by the Docker execution)
        combined_env = {}
        if env:
            combined_env.update(env)  # Additional env vars override defaults

        old_env = {}
        for key, value in combined_env.items():
            old_env[key] = os.environ.get(key)
            os.environ[key] = value

        try:
            # Use ContainerManager approach
            return self.container_manager.run_cmd(command, container_cwd, quiet)
        finally:
            # Restore previous environment
            for key, old_value in old_env.items():
                if old_value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = old_value

    def _translate_path_to_container(self, host_path: str) -> str:
        """
        Translate host paths to container paths.

        Args:
            host_path: Absolute path on the host system

        Returns:
            Corresponding path inside the container
        """
        host_path_obj = Path(host_path).resolve()

        # Check if this is a known host path that should be translated
        if PathManager().is_docker_mode():
            try:
                # Try to translate repo_dir path
                if host_path_obj == PathManager().repo_dir or PathManager().repo_dir in host_path_obj.parents:
                    relative = host_path_obj.relative_to(PathManager().repo_dir)
                    return str(Path('/code/workspace/repo') / relative)

                # Try to translate build_dir path
                if host_path_obj == PathManager().build_dir or PathManager().build_dir in host_path_obj.parents:
                    relative = host_path_obj.relative_to(PathManager().build_dir)
                    return str(Path('/code/workspace/build') / relative)

                # Try to translate cache_dir path
                if host_path_obj == PathManager().cache_dir or PathManager().cache_dir in host_path_obj.parents:
                    relative = host_path_obj.relative_to(PathManager().cache_dir)
                    return str(Path('/code/workspace/cache') / relative)

                # Try to translate tech_dir path
                if host_path_obj == PathManager().tech_dir or PathManager().tech_dir in host_path_obj.parents:
                    relative = host_path_obj.relative_to(PathManager().tech_dir)
                    return str(Path('/code/workspace/tech') / relative)

                # Try to translate private_dir path (if configured)
                if PathManager().has_private_dir():
                    private_dir = PathManager().private_dir
                    if host_path_obj == private_dir or private_dir in host_path_obj.parents:
                        relative = host_path_obj.relative_to(private_dir)
                        return str(Path('/code/workspace/private') / relative)
            except (ValueError, AttributeError):
                # If path translation fails, use the original path
                pass

        # Default: return the original path (may work in some container setups)
        return str(host_path_obj)
