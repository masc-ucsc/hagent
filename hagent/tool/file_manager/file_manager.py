from typing import Optional, Tuple, List

from hagent.inou.container_manager import ContainerManager
from hagent.inou.file_tracker import FileTracker
from hagent.inou.path_manager import PathManager
from .file_operations import FileOperations
from .patch_operations import PatchOperations


class File_manager:
    """
    Wrapper to manage docker setups, tracks file state within a container,
    and exports/imports patches as unified diffs in YAML.
    """

    def __init__(self, image: str) -> None:
        """
        Create a new class with the docker image.
        Verify docker is available, and that the user has permission to run the docker.

        Initializes internal state; does not create the container yet.

        The object destruction or termination should clear the docker.
        """
        self.image = image
        self.error_message = ''
        self._state = 'INITIALIZED'
        self._workdir = '/code/workspace/repo'  # Updated working directory for new mount structure
        self._config_sources: List[str] = []  # Store paths to configuration files to be sourced

        # Initialize PathManager and new components
        self.path_manager = PathManager()
        self.file_tracker = FileTracker(self.path_manager)

        # Initialize component managers with new inou components
        self._docker = ContainerManager(image, self.path_manager)
        self._files = FileOperations(self)
        self._patches = PatchOperations(self)

    def __enter__(self):
        """Context manager entry."""
        return self

    def __exit__(self, exc_type, exc_val, exc_tb):
        """Context manager exit - ensures cleanup."""
        self.cleanup()
        return False

    def __del__(self) -> None:
        """On destruction, ensures the created docker container is stopped and removed."""
        try:
            self.cleanup()
        except Exception:
            # Ignore any errors during destruction cleanup
            pass

    def get_error(self) -> str:
        """Return the last recorded error message (empty if none)."""
        return self.error_message

    # Docker and container management methods

    def cleanup(self) -> None:
        """Explicitly clean up resources."""
        # Clean up FileTracker first
        if hasattr(self, 'file_tracker'):
            try:
                self.file_tracker.cleanup()
            except Exception:
                # Ignore cleanup errors for FileTracker
                pass

        return self._docker.cleanup()

    def add_mount(self, host_path: str, container_path: str) -> bool:
        """Registers a directory to be mounted from the host. Must be called before setup()."""
        result = self._docker.add_mount(host_path, container_path)
        if not result:
            # Propagate error message from ContainerManager
            self.error_message = self._docker.get_error()
        return result

    def run(self, command: str, container_path: Optional[str] = '.', quiet: bool = False) -> Tuple[int, str, str]:
        """Execute command inside the container."""
        return self._docker.run(command, container_path, quiet, config_sources=self._config_sources)

    # File operations methods

    def get_file_content(self, container_path: str, container=None) -> str:
        """Return the text content of a file from a container (defaults to main container)."""
        return self._files.get_file_content(container_path, container)

    def path_exists(self, container_path: str) -> bool:
        """Check if a path exists in the container."""
        exit_code, _, _ = self.run(f'test -e "{container_path}"', quiet=True)
        return exit_code == 0

    def _container_to_host_path(self, container_path: str) -> Optional[str]:
        """
        Convert container path to corresponding host path for FileTracker.

        Args:
            container_path: Path inside the container

        Returns:
            Corresponding host path if mapping exists, None otherwise
        """
        # Handle the new mount structure
        if container_path.startswith('/code/workspace/repo'):
            relative_path = container_path[len('/code/workspace/repo') :].lstrip('/')
            return str(self.path_manager.repo_dir / relative_path) if relative_path else str(self.path_manager.repo_dir)
        elif container_path.startswith('/code/workspace/build'):
            relative_path = container_path[len('/code/workspace/build') :].lstrip('/')
            return str(self.path_manager.build_dir / relative_path) if relative_path else str(self.path_manager.build_dir)
        elif container_path.startswith('.'):
            # Relative paths in working directory
            relative_path = container_path.lstrip('./')
            return str(self.path_manager.repo_dir / relative_path) if relative_path else str(self.path_manager.repo_dir)

        return None

    # Patch operations methods
