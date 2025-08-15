"""
Executor for HAgent

Provides unified command execution interface with ExecutionStrategy pattern.
Replaces image_conf.py functionality with clean separation between
local and Docker execution.
"""

import os
import subprocess
import sys
from pathlib import Path
from typing import Dict, Optional, Tuple, Protocol

from .path_manager import PathManager


class ExecutionStrategy(Protocol):
    """Protocol defining the interface for command execution strategies."""

    def run(self, command: str, cwd: str, env: Dict[str, str], quiet: bool = False) -> Tuple[int, str, str]:
        """
        Execute a command with the given parameters.

        Args:
            command: The command to execute
            cwd: Working directory for the command
            env: Environment variables
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        ...


class LocalExecutor:
    """Execution strategy that runs commands directly on the host system."""

    def __init__(self, path_manager: Optional[PathManager] = None):
        """
        Initialize LocalExecutor.

        Args:
            path_manager: PathManager instance for path resolution
        """
        self.path_manager = path_manager or PathManager()

    def run(self, command: str, cwd: str, env: Dict[str, str], quiet: bool = False) -> Tuple[int, str, str]:
        """
        Execute command directly on the host system.

        Args:
            command: The command to execute
            cwd: Working directory for the command (absolute path)
            env: Environment variables
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        try:
            # Validate working directory exists
            cwd_path = Path(cwd).resolve()
            if not cwd_path.exists():
                return -1, '', f'Working directory does not exist: {cwd_path}'
            if not cwd_path.is_dir():
                return -1, '', f'Working directory path is not a directory: {cwd_path}'

            # Prepare environment
            full_env = os.environ.copy()
            full_env.update(env)

            # Execute command
            if quiet:
                # Capture output
                result = subprocess.run(
                    command,
                    shell=True,
                    cwd=str(cwd_path),
                    env=full_env,
                    capture_output=True,
                    text=True,
                )
                return result.returncode, result.stdout, result.stderr
            else:
                # Stream output in real-time
                process = subprocess.Popen(
                    command,
                    shell=True,
                    cwd=str(cwd_path),
                    env=full_env,
                    stdout=subprocess.PIPE,
                    stderr=subprocess.PIPE,
                    text=True,
                )

                stdout_lines = []
                stderr_lines = []

                # Read output in real-time
                while process.poll() is None:
                    if process.stdout:
                        line = process.stdout.readline()
                        if line:
                            stdout_lines.append(line)
                            print(f'local:run: {line.rstrip()}')

                    if process.stderr:
                        line = process.stderr.readline()
                        if line:
                            stderr_lines.append(line)
                            print(f'local:run: {line.rstrip()}', file=sys.stderr)

                # Get remaining output
                if process.stdout:
                    remaining_stdout = process.stdout.read()
                    if remaining_stdout:
                        stdout_lines.append(remaining_stdout)
                        for line in remaining_stdout.splitlines():
                            if line.strip():
                                print(f'local:run: {line}')

                if process.stderr:
                    remaining_stderr = process.stderr.read()
                    if remaining_stderr:
                        stderr_lines.append(remaining_stderr)
                        for line in remaining_stderr.splitlines():
                            if line.strip():
                                print(f'local:run: {line}', file=sys.stderr)

                exit_code = process.wait()
                stdout_str = ''.join(stdout_lines)
                stderr_str = ''.join(stderr_lines)

                return exit_code, stdout_str, stderr_str

        except Exception as e:
            return -1, '', f'Command execution failed: {e}'


class DockerExecutor:
    """Execution strategy that runs commands within Docker containers."""

    def __init__(self, container_manager=None, file_manager=None, path_manager: Optional[PathManager] = None):
        """
        Initialize DockerExecutor.

        Args:
            container_manager: ContainerManager instance for Docker operations (preferred)
            file_manager: File_manager instance for Docker operations (deprecated, for backwards compatibility)
            path_manager: PathManager instance for path resolution
        """
        self.path_manager = path_manager or PathManager()

        # Prefer container_manager over file_manager
        if container_manager is not None:
            self.container_manager = container_manager
            self.file_manager = None  # Don't use deprecated file_manager
        elif file_manager is not None:
            self.file_manager = file_manager
            self.container_manager = None
        else:
            # Create a new container_manager if neither provided
            from .container_manager import ContainerManager

            self.container_manager = ContainerManager(
                image='mascucsc/hagent-simplechisel:2025.08', path_manager=self.path_manager
            )
            self.file_manager = None

        # Container instance for reuse
        self._container = None

    def execute_command(self, command, working_dir=None, **kwargs):
        """
        Execute command with automatic container setup.

        This is the new standardized interface for Phase 5 & 6.

        Args:
            command: Command to execute
            working_dir: Optional working directory
            **kwargs: Additional arguments (env, quiet, etc.)

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        if not self._container and self.container_manager:
            # Create container with standardized setup
            self._container = self.container_manager.create_container(
                repo_dir=getattr(self.path_manager, 'repo_dir', None),
                build_dir=getattr(self.path_manager, 'build_dir', None),
                cache_dir=self.path_manager.cache_dir,
            )

            if not self._container:
                return -1, '', f'Failed to create container: {self.container_manager.get_error()}'

        # Translate host paths to container paths
        container_command = self._translate_paths(command)
        container_working_dir = self._translate_working_dir(working_dir)

        return self._execute_in_container(container_command, container_working_dir, **kwargs)

    def _translate_paths(self, command):
        """Translate host paths in command to container paths."""
        # For now, return command as-is
        # TODO: Implement path translation logic if needed
        return command

    def _translate_working_dir(self, working_dir):
        """Translate host working directory to container working directory."""
        if not working_dir:
            return '/code/workspace/repo'  # Default container working dir

        # Simple translation - could be enhanced based on needs
        if working_dir.startswith(str(self.path_manager.repo_dir)):
            rel_path = os.path.relpath(working_dir, self.path_manager.repo_dir)
            return f'/code/workspace/repo/{rel_path}'.replace('//', '/')
        elif hasattr(self.path_manager, 'build_dir') and working_dir.startswith(str(self.path_manager.build_dir)):
            rel_path = os.path.relpath(working_dir, self.path_manager.build_dir)
            return f'/code/workspace/build/{rel_path}'.replace('//', '/')

        # Default to repo if unable to translate
        return '/code/workspace/repo'

    def _execute_in_container(self, command, working_dir, **kwargs):
        """Execute command in the container."""
        if self.container_manager and self._container:
            # Use container manager's run method
            quiet = kwargs.get('quiet', False)
            return self.container_manager.run(command, working_dir, quiet)
        else:
            # Fallback to old method
            return self.run(command, working_dir or '/code/workspace/repo', kwargs.get('env', {}), kwargs.get('quiet', False))

    def run(self, command: str, cwd: str, env: Dict[str, str], quiet: bool = False) -> Tuple[int, str, str]:
        """
        Execute command using ContainerManager or File_manager (Docker).

        Args:
            command: The command to execute
            cwd: Working directory (absolute path, will be converted for container)
            env: Environment variables (set in the host environment)
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        # Convert host paths to container paths if needed
        container_cwd = self._translate_path_to_container(cwd)

        # Set environment variables in the current process
        # (they'll be inherited by the Docker execution)
        old_env = {}
        for key, value in env.items():
            old_env[key] = os.environ.get(key)
            os.environ[key] = value

        try:
            if self.container_manager is not None:
                # Use new ContainerManager approach
                return self.container_manager.run(command, container_cwd, quiet)
            elif self.file_manager is not None:
                # Use deprecated File_manager approach for backwards compatibility
                return self.file_manager.run(command, container_cwd, quiet)
            else:
                return -1, '', 'No Docker execution backend available'
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
        if self.path_manager.is_docker_mode():
            try:
                # Try to translate repo_dir path
                if host_path_obj == self.path_manager.repo_dir or self.path_manager.repo_dir in host_path_obj.parents:
                    relative = host_path_obj.relative_to(self.path_manager.repo_dir)
                    return str(Path('/code/workspace/repo') / relative)

                # Try to translate build_dir path
                if host_path_obj == self.path_manager.build_dir or self.path_manager.build_dir in host_path_obj.parents:
                    relative = host_path_obj.relative_to(self.path_manager.build_dir)
                    return str(Path('/code/workspace/build') / relative)

                # Try to translate cache_dir path
                if host_path_obj == self.path_manager.cache_dir or self.path_manager.cache_dir in host_path_obj.parents:
                    relative = host_path_obj.relative_to(self.path_manager.cache_dir)
                    return str(Path('/code/workspace/cache') / relative)
            except (ValueError, AttributeError):
                # If path translation fails, use the original path
                pass

        # Default: return the original path (may work in some container setups)
        return str(host_path_obj)


class ExecutorFactory:
    """Factory for creating appropriate executor instances."""

    @staticmethod
    def create_executor(
        container_manager=None, file_manager=None, path_manager: Optional[PathManager] = None
    ) -> ExecutionStrategy:
        """
        Create an appropriate executor based on HAGENT_EXECUTION_MODE.

        Args:
            container_manager: Optional ContainerManager instance for Docker execution (preferred)
            file_manager: Optional File_manager instance for Docker execution (deprecated)
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
            return DockerExecutor(container_manager, file_manager, path_manager)
        else:
            raise ValueError(f"Invalid execution mode: '{execution_mode}'. Must be 'local' or 'docker'.")


# Convenience functions for backward compatibility and ease of use


def create_executor(container_manager=None, file_manager=None, path_manager: Optional[PathManager] = None) -> ExecutionStrategy:
    """
    Convenience function to create an appropriate executor.

    Args:
        container_manager: Optional ContainerManager instance for Docker execution (preferred)
        file_manager: Optional File_manager instance for Docker execution (deprecated)
        path_manager: Optional PathManager instance

    Returns:
        ExecutionStrategy instance
    """
    return ExecutorFactory.create_executor(container_manager, file_manager, path_manager)


def run_command(
    command: str,
    cwd: str = '.',
    env: Optional[Dict[str, str]] = None,
    quiet: bool = False,
    container_manager=None,
    file_manager=None,
    path_manager: Optional[PathManager] = None,
) -> Tuple[int, str, str]:
    """
    Convenience function to run a command using the appropriate executor.

    Args:
        command: The command to execute
        cwd: Working directory for the command
        env: Additional environment variables
        quiet: Whether to run in quiet mode
        container_manager: Optional ContainerManager instance for Docker execution (preferred)
        file_manager: Optional File_manager instance for Docker execution (deprecated)
        path_manager: Optional PathManager instance

    Returns:
        Tuple of (exit_code, stdout, stderr)
    """
    executor = create_executor(container_manager, file_manager, path_manager)
    env = env or {}

    # Resolve working directory
    if cwd == '.':
        if not path_manager:
            path_manager = PathManager()
        cwd = str(path_manager.repo_dir)

    return executor.run(command, cwd, env, quiet)
