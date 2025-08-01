from typing import Optional, Dict, Tuple, Any, Set, List

from .docker_manager import DockerManager
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
        self._workdir = '/code/rundir'  # Default working directory inside the container
        self._config_sources: List[str] = []  # Store paths to configuration files to be sourced

        # Initialize component managers with shared state
        self._docker = DockerManager(self)
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

    @property
    def workdir(self) -> str:
        """Get the current working directory path inside the container."""
        return self._workdir

    def get_error(self) -> str:
        """Return the last recorded error message (empty if none)."""
        return self.error_message

    # Docker and container management methods
    def get_docker_info(self) -> Dict[str, str]:
        """Get information about the Docker connection for debugging."""
        return self._docker.get_docker_info()

    def setup(self, workdir: Optional[str] = None) -> bool:
        """
        If a docker container was already configured, this clears it and allows for a new setup.
        Downloads (docker pull equivalent) and creates, but does not start, a docker container.

        Args:
            workdir: Optional working directory path inside the container.
                    If provided, must exist in the image or be creatable.
        """
        return self._docker.setup(workdir)

    def cleanup(self) -> None:
        """Explicitly clean up resources."""
        return self._docker.cleanup()

    def add_mount(self, host_path: str, container_path: str) -> bool:
        """Registers a directory to be mounted from the host. Must be called before setup()."""
        return self._docker.add_mount(host_path, container_path)

    def add_config_source(self, config_path: str) -> Tuple[int, str, str]:
        """
        Add a configuration file path to be sourced before running commands.
        The file will be sourced before any command executed by run().
        
        Args:
            config_path: Path to the configuration file inside the container.
                        This file should exist and be readable.
        
        Returns:
            A tuple of (exit_code, stdout, stderr) indicating whether the file exists and is readable.
        """
        # First verify the file exists and is readable
        exit_code, stdout, stderr = self._docker.run(f'test -r "{config_path}"', quiet=True)
        
        if exit_code == 0:
            self._config_sources.append(config_path)
        else:
            self.error_message = f"Configuration file '{config_path}' does not exist or is not readable: {stderr}"
            
        return exit_code, stdout, stderr
    
    def run(self, command: str, container_path: Optional[str] = '.', quiet: bool = False) -> Tuple[int, str, str]:
        """Execute command inside the container."""
        return self._docker.run(command, container_path, quiet, config_sources=self._config_sources)

    def image_checkpoint(self, name: Optional[str] = None) -> Optional[str]:
        """Create a checkpoint (Docker image) from the current container state.

        Args:
            name: Optional name for the checkpoint. If not provided, creates an anonymous
                  checkpoint that will be cleaned up when the file_manager exits.

        Returns:
            The image name/tag of the created checkpoint, or None if failed.
        """
        return self._docker.image_checkpoint(name)

    # File operations methods
    def copy_dir(self, host_path: str, container_path: str = '.', ext: Optional[str] = None) -> bool:
        """Copies a host directory into the container. Must be called after setup()."""
        return self._files.copy_dir(host_path, container_path, ext)

    def copy_file(self, host_path: str, container_path: Optional[str] = '.') -> bool:
        """Copies a single file from the host into the container's tracked directory."""
        return self._files.copy_file(host_path, container_path)

    def install_executable(self, host_path: str, container_path: Optional[str] = '/usr/local/bin') -> bool:
        """Install an executable file from the host into the container with execute permissions.

        Similar to copy_file but sets 755 permissions and defaults to /usr/local/bin for PATH access.

        Args:
            host_path: Path to the executable file on the host
            container_path: Destination directory in the container (default: /usr/local/bin)

        Returns:
            True if successful, False otherwise
        """
        return self._files.install_executable(host_path, container_path)

    def get_file_content(self, container_path: str, container=None) -> str:
        """Return the text content of a file from a container (defaults to main container)."""
        return self._files.get_file_content(container_path, container)

    def track_file(self, container_path: str) -> bool:
        """Track an existing file in the container for change detection."""
        return self._files.track_file(container_path)

    def track_dir(self, container_path: str = '.', ext: Optional[str] = None) -> bool:
        """Track a directory for change detection. Files will be discovered dynamically in get_patch_dict."""
        return self._files.track_dir(container_path, ext)

    def get_current_tracked_files(self, ext: Optional[str] = None) -> Set[str]:
        """Return a set of unique files currently being tracked.

        Args:
            ext: Optional extension filter. If provided, only returns files ending with this extension.

        Returns:
            Set of unique file paths that are currently tracked.
        """
        return self._files.get_current_tracked_files(ext)

    # Patch operations methods
    def get_diff(self, filename: str) -> str:
        """Return the unified diff (as text) for a single tracked file."""
        return self._patches.get_diff(filename)

    def get_patch_dict(self) -> Dict[str, Any]:
        """Generate a dictionary of new files and patched files."""
        return self._patches.get_patch_dict()

    def patch_file(self, container_path: str, patch_content: str) -> bool:
        """Apply a unified diff patch to a file in the container."""
        return self._patches.patch_file(container_path, patch_content)

    def apply_line_patch(self, container_path: str, line_number: int, old_line: str, new_line: str) -> bool:
        """Apply a simple line replacement patch to a file in the container."""
        return self._patches.apply_line_patch(container_path, line_number, old_line, new_line)

    def save_patches(self, host_path: str, name: str) -> bool:
        """Dump current patch-dict to YAML at host_path."""
        return self._patches.save_patches(host_path, name)

    def load_patches(self, host_path: str) -> bool:
        """(Not Implemented) Reads a patch YAML and applies it."""
        return self._patches.load_patches(host_path)
