"""
Execution Mode Detection for HAgent

Provides automatic detection and validation of execution modes (local vs docker)
and creates appropriate executors based on environment configuration.
"""

import os
from typing import Protocol

from .path_manager import PathManager
from .executor import LocalExecutor, DockerExecutor
from .container_manager import ContainerManager


class ExecutionStrategy(Protocol):
    """Protocol for execution strategies."""

    def execute_command(self, command, working_dir=None, **kwargs):
        """Execute command in the appropriate execution context."""
        ...


class ExecutionDetector:
    """Detect and validate execution mode from environment."""

    @staticmethod
    def detect_execution_mode() -> str:
        """
        Detect execution mode from HAGENT_EXECUTION_MODE.

        Returns:
            'local' or 'docker' based on environment variable

        Raises:
            ValueError: If execution mode is invalid or not set
        """
        mode = os.environ.get('HAGENT_EXECUTION_MODE', '').lower()

        if mode not in ['local', 'docker']:
            raise ValueError(f"Invalid HAGENT_EXECUTION_MODE='{mode}'. Must be 'local' or 'docker'")

        return mode

    @staticmethod
    def create_executor(execution_mode: str) -> ExecutionStrategy:
        """
        Factory method to create appropriate executor.

        Args:
            execution_mode: 'local' or 'docker'

        Returns:
            LocalExecutor for local mode, DockerExecutor for docker mode

        Raises:
            ValueError: If execution mode is unsupported
        """
        path_manager = PathManager()  # Will validate env vars

        if execution_mode == 'local':
            return LocalExecutor(path_manager)
        elif execution_mode == 'docker':
            container_manager = ContainerManager(image='mascucsc/hagent-simplechisel:2025.08', path_manager=path_manager)
            return DockerExecutor(container_manager=container_manager, path_manager=path_manager)
        else:
            raise ValueError(f'Unsupported execution mode: {execution_mode}')

    @staticmethod
    def create_auto_executor() -> ExecutionStrategy:
        """
        Automatically detect execution mode and create appropriate executor.

        Returns:
            Executor for the detected execution mode

        Raises:
            ValueError: If execution mode detection fails
        """
        mode = ExecutionDetector.detect_execution_mode()
        return ExecutionDetector.create_executor(mode)
