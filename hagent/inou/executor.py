"""
Executor for HAgent

Provides unified command execution interface with ExecutionStrategy pattern.
Replaces image_conf.py functionality with clean separation between
local and Docker execution.
"""

from typing import Dict, Optional, Tuple, Protocol

from .path_manager import PathManager
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

    # Backward-compatible alias (deprecated). Prefer run_cmd().
    def run(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = False
    ) -> Tuple[int, str, str]: ...

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
    def create_executor(container_manager=None, path_manager: Optional[PathManager] = None) -> ExecutionStrategy:
        """
        Create an appropriate executor based on HAGENT_EXECUTION_MODE.

        Args:
            container_manager: Optional ContainerManager instance for Docker execution
            path_manager: Optional PathManager instance

        Returns:
            ExecutionStrategy instance (LocalExecutor or DockerExecutor)

        Raises:
            ValueError: If execution mode is invalid
        """
        if not path_manager:
            path_manager = PathManager()

        execution_mode = path_manager.execution_mode

        if execution_mode == 'local':
            return LocalExecutor(path_manager)
        elif execution_mode == 'docker':
            return DockerExecutor(container_manager, path_manager)
        else:
            raise ValueError(f"Invalid execution mode: '{execution_mode}'. Must be 'local' or 'docker'.")


# Convenience functions for backward compatibility and ease of use


def create_executor(container_manager=None, path_manager: Optional[PathManager] = None) -> ExecutionStrategy:
    """
    Convenience function to create an appropriate executor.

    Args:
        container_manager: Optional ContainerManager instance for Docker execution
        path_manager: Optional PathManager instance

    Returns:
        ExecutionStrategy instance
    """
    return ExecutorFactory.create_executor(container_manager, path_manager)


def run_cmd(
    command: str,
    cwd: str = '.',
    env: Optional[Dict[str, str]] = None,
    quiet: bool = False,
    container_manager=None,
    path_manager: Optional[PathManager] = None,
) -> Tuple[int, str, str]:
    """
    Convenience function to run a command using the appropriate executor.

    Args:
        command: The command to execute
        cwd: Working directory for the command
        env: Additional environment variables
        quiet: Whether to run in quiet mode
        container_manager: Optional ContainerManager instance for Docker execution
        path_manager: Optional PathManager instance

    Returns:
        Tuple of (exit_code, stdout, stderr)
    """
    executor = create_executor(container_manager, path_manager)
    env = env or {}

    # Resolve working directory
    if cwd == '.':
        if not path_manager:
            path_manager = PathManager()
        cwd = str(path_manager.repo_dir)

    return executor.run_cmd(command, cwd, env, quiet)


# Backward-compatible alias (deprecated). Prefer run_cmd().
def run_command(
    command: str,
    cwd: str = '.',
    env: Optional[Dict[str, str]] = None,
    quiet: bool = False,
    container_manager=None,
    path_manager: Optional[PathManager] = None,
) -> Tuple[int, str, str]:
    return run_cmd(command, cwd, env, quiet, container_manager, path_manager)
