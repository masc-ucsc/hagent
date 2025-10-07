"""
Local Executor for HAgent

Provides local command execution strategy that runs commands directly on the host system.
"""

import os
import subprocess
import sys
from pathlib import Path
from typing import Dict, Optional, Tuple

from .path_manager import PathManager


class LocalExecutor:
    """Execution strategy that runs commands directly on the host system."""

    def __init__(self):
        """
        Initialize LocalExecutor.
        """
        self.path_manager = PathManager()
        self._workdir = str(self.path_manager.repo_dir)
        self.error_message = ''

    def set_error(self, message: str) -> None:
        """Set error message following Tool pattern."""
        self.error_message = message

    def get_error(self) -> str:
        """Get current error message following Tool pattern."""
        return self.error_message

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

    def get_cwd(self) -> str:
        """
        Get the current working directory.

        Returns:
            Current working directory path
        """
        return self._workdir

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
