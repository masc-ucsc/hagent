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
from .container_manager import is_docker_mode


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


class LocalExecutor:
    """Execution strategy that runs commands directly on the host system."""

    def __init__(self, path_manager: Optional[PathManager] = None):
        """
        Initialize LocalExecutor.

        Args:
            path_manager: PathManager instance for path resolution
        """
        self.path_manager = path_manager or PathManager()
        self._workdir = str(self.path_manager.repo_dir)
        self.error_message = ''

    def set_error(self, message: str) -> None:
        """Set error message following Tool pattern."""
        self.error_message = message

    def get_error(self) -> str:
        """Get current error message following Tool pattern."""
        return self.error_message

    def _setup_hagent_environment(self) -> Dict[str, str]:
        """Setup HAGENT environment variables for local execution."""
        env_vars = {
            'HAGENT_EXECUTION_MODE': 'local',
            'HAGENT_REPO_DIR': str(self.path_manager.repo_dir),
            'HAGENT_BUILD_DIR': str(getattr(self.path_manager, 'build_dir', '')),
            'HAGENT_CACHE_DIR': str(self.path_manager.cache_dir),
        }
        return env_vars

    def setup(self) -> bool:
        """
        Setup local execution environment.
        Working directory is always the repo directory.

        Returns:
            True if setup successful, False otherwise
        """
        try:
            # Validate that the repo directory exists
            repo_path = Path(self._workdir).resolve()
            if not repo_path.exists():
                self.set_error(f'Repository directory does not exist: {repo_path}')
                return False
            if not repo_path.is_dir():
                self.set_error(f'Repository path is not a directory: {repo_path}')
                return False
            return True
        except Exception as e:
            self.set_error(f'Local setup failed: {e}')
            return False

    def set_cwd(self, new_workdir: str) -> bool:
        """
        Change the working directory with validation.

        Args:
            new_workdir: New working directory path (relative to repo or absolute)

        Returns:
            True if successful, False if path doesn't exist
        """
        try:
            # Convert relative paths to absolute
            if not os.path.isabs(new_workdir):
                target_workdir = os.path.join(self._workdir, new_workdir)
            else:
                target_workdir = new_workdir

            # Validate that the path exists and is a directory
            target_path = Path(target_workdir).resolve()
            if not target_path.exists():
                self.set_error(f'Directory does not exist: {target_path}')
                return False
            if not target_path.is_dir():
                self.set_error(f'Path exists but is not a directory: {target_path}')
                return False

            # Update the working directory
            self._workdir = str(target_path)
            return True
        except Exception as e:
            self.set_error(f'Failed to change working directory: {e}')
            return False

    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = False
    ) -> Tuple[int, str, str]:
        """
        Execute command directly on the host system.

        Args:
            command: The command to execute
            cwd: Working directory for the command (relative to current workdir or absolute path)
            env: Additional environment variables (HAGENT vars are automatically included)
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        try:
            # Handle working directory
            if cwd == '.':
                workdir = self._workdir
            else:
                if not os.path.isabs(cwd):
                    workdir = os.path.join(self._workdir, cwd)
                else:
                    workdir = cwd

            # Validate working directory exists
            cwd_path = Path(workdir).resolve()
            if not cwd_path.exists():
                error_msg = f'Working directory does not exist: {cwd_path}'
                self.set_error(error_msg)
                return -1, '', error_msg
            if not cwd_path.is_dir():
                error_msg = f'Working directory path is not a directory: {cwd_path}'
                self.set_error(error_msg)
                return -1, '', error_msg

            # Prepare environment with HAGENT variables
            full_env = os.environ.copy()
            hagent_env = self._setup_hagent_environment()
            full_env.update(hagent_env)
            if env:
                full_env.update(env)  # Additional env vars override defaults

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

    # Backward-compatible alias (deprecated). Prefer run_cmd().
    def run(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = False
    ) -> Tuple[int, str, str]:
        return self.run_cmd(command, cwd, env, quiet)


class DockerExecutor:
    """Execution strategy that runs commands within Docker containers."""

    def __init__(self, container_manager=None, path_manager: Optional[PathManager] = None):
        """
        Initialize DockerExecutor.

        Args:
            container_manager: ContainerManager instance for Docker operations
            path_manager: PathManager instance for path resolution
        """
        self.path_manager = path_manager or PathManager()

        if container_manager is not None:
            self.container_manager = container_manager
        else:
            # Create a new container_manager if not provided
            from .container_manager import ContainerManager

            self.container_manager = ContainerManager(
                image='mascucsc/hagent-simplechisel:2025.09', path_manager=self.path_manager
            )

        # Container instance for reuse
        self._container = None
        self.error_message = ''

    def set_error(self, message: str) -> None:
        """Set error message following Tool pattern."""
        self.error_message = message

    def get_error(self) -> str:
        """Get current error message following Tool pattern."""
        return self.error_message

    def _setup_hagent_environment(self) -> Dict[str, str]:
        """Setup HAGENT environment variables for Docker execution."""
        env_vars = {
            'HAGENT_EXECUTION_MODE': 'docker',
            'HAGENT_REPO_DIR': str(self.path_manager.repo_dir),
            'HAGENT_BUILD_DIR': str(getattr(self.path_manager, 'build_dir', '')),
            'HAGENT_CACHE_DIR': str(self.path_manager.cache_dir),
        }
        return env_vars

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
        hagent_env = self._setup_hagent_environment()
        combined_env = hagent_env.copy()
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

    # Backward-compatible alias (deprecated). Prefer run_cmd().
    def run(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = False
    ) -> Tuple[int, str, str]:
        return self.run_cmd(command, cwd, env, quiet)

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
        if is_docker_mode():
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
