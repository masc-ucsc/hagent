"""
Execution Context for HAgent

Provides transparent execution context that works seamlessly across Docker and
local execution modes. This is the primary interface for tools to execute
commands without needing to know about the underlying execution environment.
"""

from .execution_detector import ExecutionDetector
from .output_manager import get_output_dir


class ExecutionContext:
    """Provides transparent execution context for HAgent tools."""

    def __init__(self):
        """
        Initialize ExecutionContext with automatic mode detection.

        Automatically detects execution mode and creates appropriate executor.
        """
        self.execution_mode = ExecutionDetector.detect_execution_mode()
        self.executor = ExecutionDetector.create_executor(self.execution_mode)
        self.path_manager = self.executor.path_manager

    def execute(self, command, **kwargs):
        """
        Execute command transparently in current mode.

        Args:
            command: Command to execute
            **kwargs: Additional arguments (working_dir, env, quiet, etc.)

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        return self.executor.execute_command(command, **kwargs)

    def get_working_dir(self):
        """
        Get appropriate working directory for current mode.

        Returns:
            Working directory path suitable for current execution mode
        """
        if self.execution_mode == 'docker':
            return '/code/workspace/repo'
        else:
            return str(self.path_manager.repo_dir)

    def resolve_path(self, path):
        """
        Resolve path for current execution context.

        Args:
            path: Path to resolve

        Returns:
            Resolved path appropriate for current execution mode
        """
        # Use the executor's path resolution if available
        if hasattr(self.executor, 'resolve_path'):
            return self.executor.resolve_path(path)
        else:
            # Fallback to basic path resolution
            return str(self.path_manager.repo_dir / path) if not path.startswith('/') else path

    def get_cache_dir(self):
        """
        Get cache directory for current execution mode.

        Returns:
            Cache directory path
        """
        if self.execution_mode == 'docker':
            return '/code/workspace/cache'
        else:
            return str(self.path_manager.cache_dir)

    def get_yaml_path(self, filename):
        """
        Get path for YAML file in current execution context.

        Args:
            filename: Name of YAML file

        Returns:
            Path to YAML file appropriate for current mode
        """
        if self.execution_mode == 'docker':
            return f'/code/workspace/cache/inou/{filename}'
        else:
            return str(self.path_manager.get_yaml_path(filename))

    def get_logs_dir(self):
        """
        Get logs directory for current execution mode.

        Uses output_manager to respect HAGENT_OUTPUT_DIR if set,
        otherwise uses structured cache directory.

        Returns:
            Logs directory path
        """
        return get_output_dir()

    def is_local_mode(self) -> bool:
        """Check if running in local execution mode."""
        return self.execution_mode == 'local'

    def is_docker_mode(self) -> bool:
        """Check if running in Docker execution mode."""
        return self.execution_mode == 'docker'
