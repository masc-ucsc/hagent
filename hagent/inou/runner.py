"""
Runner for HAgent - Simplified wrapper for Executor, ContainerManager, PathManager, and FileTracker

Provides a unified interface that hides the complexity of the 4 underlying classes.
Handles HAGENT_EXECUTION_MODE checking and provides lazy FileTracker initialization.
"""

from typing import Optional, Tuple, Dict, Set, Any

from .container_manager import ContainerManager
from .executor import ExecutorFactory
from .path_manager import PathManager
from .file_tracker import FileTracker


class Runner:
    """
    Simplified wrapper for Executor, ContainerManager, PathManager, and FileTracker.

    Provides a unified interface that handles:
    - HAGENT_EXECUTION_MODE mode checking
    - Automatic executor and container setup
    - Lazy FileTracker initialization (only when tracking is needed)
    - Common error handling and cleanup

    Example usage:
        runner = Runner(docker_image='mascucsc/hagent-simplechisel:2025.09r')
        if not runner.setup():
            print(f"Setup failed: {runner.get_error()}")
            return

        # Run commands
        exit_code, stdout, stderr = runner.run_cmd('ls -la')

        # Track files (lazy FileTracker initialization)
        runner.track_file('src/main.scala')
        runner.track_dir('build', '.sv')

        # Get diffs
        diffs = runner.get_all_diffs('.scala')

        # Cleanup
        runner.cleanup()
    """

    def __init__(self, docker_image: Optional[str] = None, path_manager: Optional[PathManager] = None):
        """
        Initialize Runner with optional Docker image.

        Args:
            docker_image: Docker image to use if HAGENT_EXECUTION_MODE is 'docker'
            path_manager: Optional PathManager instance (created if not provided)
        """
        self.docker_image = docker_image
        self.path_manager = path_manager or PathManager()
        self.container_manager: Optional[ContainerManager] = None
        self.executor = None
        self.file_tracker: Optional[FileTracker] = None  # Lazy initialization
        self.error_message = ''

        # Check execution mode
        self.execution_mode = self.path_manager.execution_mode

        # Create container manager for docker mode
        if self.execution_mode == 'docker':
            if not docker_image:
                self.set_error('Docker image must be provided when HAGENT_EXECUTION_MODE is docker')
                return
            self.container_manager = ContainerManager(docker_image, self.path_manager)

        # Create executor
        self.executor = ExecutorFactory.create_executor(self.container_manager, self.path_manager)

    def set_error(self, message: str) -> None:
        """Set error message following Tool pattern."""
        self.error_message = message

    def get_error(self) -> str:
        """Get current error message following Tool pattern."""
        return self.error_message

    def setup(self) -> bool:
        """
        Setup the execution environment.

        Returns:
            True if setup successful, False otherwise
        """
        if not self.executor:
            self.set_error('Executor not available - check initialization errors')
            return False

        success = self.executor.setup()
        if not success:
            self.set_error(f'Executor setup failed: {self.executor.get_error()}')
        return success

    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = False
    ) -> Tuple[int, str, str]:
        """
        Execute a command using the appropriate executor.

        Args:
            command: The command to execute
            cwd: Working directory for the command (defaults to "." which uses internal workdir)
            env: Additional environment variables (defaults to None, HAGENT vars are automatically included)
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        if not self.executor:
            error_msg = 'Executor not available - call setup() first'
            self.set_error(error_msg)
            return -1, '', error_msg

        return self.executor.run_cmd(command, cwd, env, quiet)

    # Backward-compatible alias (deprecated). Prefer run_cmd().
    def run(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = False
    ) -> Tuple[int, str, str]:
        return self.run_cmd(command, cwd, env, quiet)

    def set_cwd(self, new_workdir: str) -> bool:
        """
        Change the working directory with validation.

        Args:
            new_workdir: New working directory path

        Returns:
            True if successful, False if path doesn't exist
        """
        if not self.executor:
            self.set_error('Executor not available - call setup() first')
            return False

        success = self.executor.set_cwd(new_workdir)
        if not success:
            self.set_error(self.executor.get_error())
        return success

    def _ensure_file_tracker(self) -> bool:
        """
        Ensure FileTracker is initialized (lazy initialization).

        Returns:
            True if FileTracker is available, False otherwise
        """
        if self.file_tracker is None:
            try:
                # Provide container_manager so FileTracker can perform Docker-aware checks
                self.file_tracker = FileTracker(self.path_manager, self.container_manager)
                return True
            except Exception as e:
                self.set_error(f'Failed to initialize FileTracker: {e}')
                return False
        return True

    def track_file(self, file_path: str) -> bool:
        """
        Track individual file for changes.

        Args:
            file_path: Path to file (can be relative or absolute)

        Returns:
            True if successfully added to tracking, False otherwise
        """
        if not self._ensure_file_tracker():
            return False

        success = self.file_tracker.track_file(file_path)
        if not success:
            self.set_error(self.file_tracker.get_error() if hasattr(self.file_tracker, 'get_error') else 'File tracking failed')
        return success

    def track_dir(self, dir_path: str, ext_filter: Optional[str] = None) -> bool:
        """
        Track directory with optional extension filter.

        Args:
            dir_path: Path to directory (can be relative or absolute)
            ext_filter: Optional extension filter (e.g., '.scala', '.v')

        Returns:
            True if successfully added to tracking, False otherwise
        """
        if not self._ensure_file_tracker():
            return False

        success = self.file_tracker.track_dir(dir_path, ext_filter)
        if not success:
            self.set_error(
                self.file_tracker.get_error() if hasattr(self.file_tracker, 'get_error') else 'Directory tracking failed'
            )
        return success

    def get_tracked_files(self, ext_filter: Optional[str] = None) -> Set[str]:
        """
        Get set of currently tracked files.

        Args:
            ext_filter: Optional extension filter

        Returns:
            Set of tracked file paths (includes files from tracked directories)
        """
        if not self._ensure_file_tracker():
            return set()

        return self.file_tracker.get_tracked_files(ext_filter)

    def get_diff(self, file_path: str) -> str:
        """
        Get unified diff for specific tracked file.

        Args:
            file_path: Path to file to get diff for

        Returns:
            Unified diff output as string
        """
        if not self._ensure_file_tracker():
            return ''

        return self.file_tracker.get_diff(file_path)

    def get_all_diffs(self, ext_filter: Optional[str] = None) -> Dict[str, str]:
        """
        Get diffs for all tracked files with optional filtering.

        Args:
            ext_filter: Optional extension filter (e.g., '.scala')

        Returns:
            Dictionary mapping file paths to their diff content
        """
        if not self._ensure_file_tracker():
            return {}

        return self.file_tracker.get_all_diffs(ext_filter)

    def get_patch_dict(self) -> Dict[str, Any]:
        """
        Generate patch dictionary compatible with YAML export.

        Returns:
            Dictionary with 'full' and 'patch' lists compatible with existing format
        """
        if not self._ensure_file_tracker():
            return {'full': [], 'patch': []}

        return self.file_tracker.get_patch_dict()

    def cleanup(self) -> None:
        """
        Clean up all resources including FileTracker, ContainerManager, etc.

        This method is idempotent and safe to call multiple times.
        """
        # Cleanup FileTracker first
        if self.file_tracker:
            try:
                self.file_tracker.cleanup()
                self.file_tracker = None
            except Exception as e:
                # Log but don't fail - continue with other cleanup
                print(f'Warning: FileTracker cleanup failed: {e}')

        # Cleanup ContainerManager
        if self.container_manager:
            try:
                self.container_manager.cleanup()
            except Exception as e:
                print(f'Warning: ContainerManager cleanup failed: {e}')

        # Clear error state
        self.error_message = ''

    def is_docker_mode(self) -> bool:
        """Check if running in Docker execution mode."""
        return self.execution_mode == 'docker'

    def is_local_mode(self) -> bool:
        """Check if running in local execution mode."""
        return self.execution_mode == 'local'

    def __enter__(self):
        """Context manager entry."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit - ensures cleanup."""
        self.cleanup()
        return False

    def __del__(self) -> None:
        """On destruction, ensures cleanup."""
        try:
            self.cleanup()
        except Exception:
            # Ignore any errors during destruction cleanup
            pass
