"""
Executor for HAgent

Provides unified command execution interface with ExecutionStrategy pattern.
Replaces image_conf.py functionality with clean separation between
local and Docker execution.
"""

from typing import Dict, Optional, Tuple, Protocol

from hagent.inou.container_manager import ContainerManager
from hagent.inou.path_manager import PathManager

from .executor_local import LocalExecutor
from .executor_docker import DockerExecutor


class ExecutionStrategy(Protocol):
    """Protocol defining the interface for command execution strategies."""

    def setup(self) -> bool:
        """
        Setup the execution environment.

        Returns:
            True if setup successful, False otherwise
        """
        ...

    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = False
    ) -> Tuple[int, str, str]:
        """
        Execute a command with the given parameters.

        Args:
            command: The command to execute
            cwd: Working directory for the command (defaults to "." which uses internal _workdir)
            env: Additional environment variables (defaults to None, HAGENT vars are automatically included)
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        ...

    def set_cwd(self, new_workdir: str) -> bool:
        """
        Change the working directory with validation.

        Args:
            new_workdir: New working directory path

        Returns:
            True if successful, False if path doesn't exist
        """
        ...

    def get_cwd(self) -> str:
        """
        Get the current working directory.

        Returns:
            Current working directory path
        """
        ...


class ExecutorFactory:
    """Factory for creating appropriate executor instances."""

    @staticmethod
    def create_executor(container_manager: ContainerManager = None) -> ExecutionStrategy:
        """
        Create an appropriate executor based on HAGENT_DOCKER setting.

        Args:
            container_manager: Optional ContainerManager instance for Docker execution

        Returns:
            ExecutionStrategy instance (LocalExecutor or DockerExecutor)
        """
        # Check if we're in docker mode
        pm = PathManager()
        if pm.is_docker_mode() or container_manager:
            # Docker mode: create or use provided container_manager
            if not container_manager:
                container_manager = ContainerManager()
            return DockerExecutor(container_manager)
        return LocalExecutor()
