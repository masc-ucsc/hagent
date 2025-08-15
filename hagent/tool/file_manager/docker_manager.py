import docker
import platform
import os
import threading
import sys
import time
from typing import Optional, List, Dict, Any


class DockerManager:
    """Handles all Docker-related operations including client initialization, container management, and checkpoints."""

    def __init__(self, file_manager):
        """Initialize with reference to main File_manager instance."""
        self.fm = file_manager
        self.client: Optional[docker.DockerClient] = None
        self.container: Optional[docker.models.containers.Container] = None
        self._reference_container: Optional[docker.models.containers.Container] = None
        self._image_user: Optional[str] = None  # Cache for image's default user
        self._has_bash: bool = False  # Track if container has bash available
        self._checkpoints: List[str] = []  # Track created checkpoints for cleanup
        self._mounts: List[Dict[str, str]] = []

        # Initialize Docker client with cross-platform support
        self._initialize_docker_client()

    def _initialize_docker_client(self) -> None:
        """
        Initialize Docker client with support for:
        - Linux (standard Docker)
        - macOS with Docker Desktop
        - macOS with Colima
        """
        # First, try the standard docker.from_env() which uses environment variables
        # and Docker context - this works in most cases
        first_error = None
        try:
            self.client = docker.from_env()
            if self.client.ping():
                return  # Success!
        except Exception as err:
            first_error = err
            pass  # Continue to try other methods

        # If from_env() failed, try platform-specific socket paths
        socket_paths = self._get_docker_socket_paths()

        for socket_path in socket_paths:
            if os.path.exists(socket_path):
                try:
                    self.client = docker.DockerClient(base_url=f'unix://{socket_path}')
                    if self.client.ping():
                        return  # Success!
                except Exception:
                    continue  # Try next socket path

        # If all attempts failed, set error state
        self.fm.error_message = (
            f'Docker client initialization failed. Tried:\n'
            f'- Environment-based connection\n'
            f'- Socket paths: {socket_paths}\n'
            f'Please ensure Docker is running and accessible.\n'
            f'Original error: {first_error if first_error else "Unknown"}'
        )
        self.fm._state = 'ERROR'

    def _get_docker_socket_paths(self) -> List[str]:
        """
        Get list of potential Docker socket paths based on the current platform.
        """
        system = platform.system().lower()
        username = os.getenv('USER', os.getenv('USERNAME', 'user'))

        if system == 'darwin':  # macOS
            return [
                # Colima (most common alternative on macOS)
                f'/Users/{username}/.colima/default/docker.sock',
                os.path.expanduser('~/.colima/default/docker.sock'),
                # Docker Desktop paths
                f'/Users/{username}/.docker/run/docker.sock',
                os.path.expanduser('~/.docker/run/docker.sock'),
                '/var/run/docker.sock',
                # Lima (another Docker alternative)
                f'/Users/{username}/.lima/default/sock/docker.sock',
                os.path.expanduser('~/.lima/default/sock/docker.sock'),
            ]
        elif system == 'linux':
            return [
                # Standard Linux Docker socket
                '/var/run/docker.sock',
                # Rootless Docker
                f'/run/user/{os.getuid()}/docker.sock',
                os.path.expanduser('~/.docker/run/docker.sock'),
                # Podman compatibility
                f'/run/user/{os.getuid()}/podman/podman.sock',
            ]
        elif system == 'windows':
            return [
                # Windows Docker Desktop (named pipe)
                'npipe:////./pipe/docker_engine',
            ]
        else:
            # Fallback for unknown systems
            return ['/var/run/docker.sock']

    def _pull_image_with_progress(self, image: str) -> None:
        """
        Pull Docker image with a simple progress indicator.
        Shows a spinning progress indicator while the pull is in progress.
        """
        # Progress indicator characters
        spinner_chars = ['⠋', '⠙', '⠹', '⠸', '⠼', '⠴', '⠦', '⠧', '⠇', '⠏']

        # Shared state for the progress thread
        pull_complete = threading.Event()
        pull_error = None

        def progress_indicator():
            """Show spinning progress indicator"""
            i = 0
            while not pull_complete.is_set():
                sys.stdout.write(f'\r{spinner_chars[i % len(spinner_chars)]} Downloading layers...')
                sys.stdout.flush()
                time.sleep(0.1)
                i += 1

        def pull_image():
            """Pull the image in a separate thread"""
            nonlocal pull_error
            try:
                self.client.images.pull(image)
            except Exception as e:
                pull_error = e
            finally:
                pull_complete.set()

        # Start progress indicator and pull threads
        progress_thread = threading.Thread(target=progress_indicator, daemon=True)
        pull_thread = threading.Thread(target=pull_image, daemon=True)

        progress_thread.start()
        pull_thread.start()

        # Wait for pull to complete
        pull_thread.join()

        # Stop progress indicator
        pull_complete.set()
        progress_thread.join(timeout=0.1)

        # Clear the progress line and show completion
        sys.stdout.write('\r✓ Image downloaded successfully\n')
        sys.stdout.flush()

        # Re-raise any error that occurred during pull
        if pull_error:
            raise pull_error

    def _get_image_user(self) -> Optional[str]:
        """Get the default user from the Docker image."""
        if self._image_user is not None:
            return self._image_user  # Return cached value (could be empty string)

        try:
            if not self.client:
                return None
            image_info = self.client.images.get(self.fm.image)
            config = image_info.attrs.get('Config', {})
            user = config.get('User')
            self._image_user = user if user else ''  # Cache empty string for no user
            return user
        except Exception:
            self._image_user = ''  # Cache that we failed to get user info
            return None

    def _get_image_config(self) -> Dict[str, Any]:
        """Get the original image configuration including command and entrypoint."""
        try:
            if not self.client:
                return {}
            image_info = self.client.images.get(self.fm.image)
            return image_info.attrs.get('Config', {})
        except Exception:
            return {}

    def _ensure_workdir_exists(self) -> bool:
        """Ensure the working directory exists in the container."""
        try:
            result = self.container.exec_run(f'mkdir -p {self.fm._workdir}')
            return result.exit_code == 0
        except Exception as e:
            self.fm.error_message = f'Failed to create working directory: {e}'
            return False

    def _validate_workdir(self, workdir: str) -> bool:
        """
        Validate that the working directory exists in the container or can be created.

        Args:
            workdir: The working directory path to validate

        Returns:
            True if the directory exists or was successfully created, False otherwise
        """
        try:
            # First, check if the directory already exists
            result = self.container.exec_run(f'test -d "{workdir}"')
            if result.exit_code == 0:
                return True  # Directory already exists

            # If it doesn't exist, try to create it
            result = self.container.exec_run(f'mkdir -p "{workdir}"')
            if result.exit_code == 0:
                # Verify it was created successfully
                result = self.container.exec_run(f'test -d "{workdir}"')
                if result.exit_code == 0:
                    return True
                else:
                    self.fm.error_message = f'Working directory "{workdir}" was not created successfully'
                    return False
            else:
                self.fm.error_message = f'Failed to create working directory "{workdir}"'
                return False

        except Exception as e:
            self.fm.error_message = f'Failed to validate working directory "{workdir}": {e}'
            return False

    def _cleanup_reference_container(self) -> None:
        """Clean up reference container."""
        if self._reference_container:
            try:
                self._reference_container.kill()
                self._reference_container.remove()
                self._reference_container = None
            except Exception as e:
                print(f'Warning: Failed to clean up reference container: {e}')

    def _cleanup_anonymous_checkpoints(self) -> None:
        """Clean up anonymous checkpoints created by this instance."""
        if not self.client or not self._checkpoints:
            return

        for checkpoint_name in self._checkpoints:
            try:
                # Get the image to find its ID
                image = self.client.images.get(checkpoint_name)
                image_id = image.id

                # Find and stop/remove any containers using this image
                containers = self.client.containers.list(all=True)
                for container in containers:
                    try:
                        # Check if container is using our checkpoint image
                        if container.image.id == image_id:
                            print(f'Stopping container {container.short_id} using checkpoint {checkpoint_name}')
                            if container.status == 'running':
                                container.kill()
                            container.remove()
                    except Exception as e:
                        print(f'Warning: Failed to cleanup container {container.short_id}: {e}')

                # Now remove the image
                self.client.images.remove(checkpoint_name, force=True)
                try:
                    # Also remove by ID to clean up any dangling references
                    self.client.images.remove(image_id, force=True)
                except docker.errors.ImageNotFound:
                    # Image already removed, which is fine
                    pass

                print(f'Cleaned up anonymous checkpoint: {checkpoint_name}')
            except docker.errors.ImageNotFound:
                # Image doesn't exist, skip
                pass
            except Exception as e:
                print(f'Warning: Failed to clean up checkpoint {checkpoint_name}: {e}')

        self._checkpoints.clear()

    def cleanup(self) -> None:
        """Explicitly clean up resources."""
        if self.container:
            try:
                self.container.kill()
                self.container.remove()
                self.container = None
            except docker.errors.APIError:
                pass

        # Clean up anonymous checkpoints
        self._cleanup_anonymous_checkpoints()

        # Clean up reference container
        self._cleanup_reference_container()
