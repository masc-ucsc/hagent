"""
Unified FileSystem interface for HAgent

Eliminates local/docker branching by providing a single abstraction
that works transparently in both execution modes.
"""

import os

# Import all components
from .filesystem_base import FileSystem
from .filesystem_local import FileSystemLocal
from .filesystem_docker import FileSystemDocker

# Keep old names as aliases for backward compatibility  
LocalFileSystem = FileSystemLocal
DockerFileSystem = FileSystemDocker


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
            return FileSystemDocker(container_manager)
        else:
            return FileSystemLocal()

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
            return FileSystemDocker(builder.runner.container_manager)
        else:
            return FileSystemLocal()