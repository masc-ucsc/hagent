import docker
import platform
import os
import threading
import sys
import time
from datetime import datetime
from typing import Optional, List, Dict, Tuple, Any


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

    def get_docker_info(self) -> Dict[str, str]:
        """
        Get information about the Docker connection for debugging.
        """
        if self.client is None:
            return {'status': 'ERROR', 'message': self.fm.error_message}

        try:
            info = self.client.info()
            version = self.client.version()
            return {
                'status': 'CONNECTED',
                'docker_version': version.get('Version', 'Unknown'),
                'api_version': version.get('ApiVersion', 'Unknown'),
                'platform': info.get('OSType', 'Unknown'),
                'architecture': info.get('Architecture', 'Unknown'),
                'server_version': info.get('ServerVersion', 'Unknown'),
            }
        except Exception as e:
            return {'status': 'ERROR', 'message': str(e)}

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

    def _ensure_container_directory(self, dir_path: str) -> bool:
        """Ensure a directory exists in the container."""
        try:
            # Create directory if it doesn't exist
            result = self.container.exec_run(f'mkdir -p {dir_path}')
            return result.exit_code == 0
        except Exception as e:
            self.fm.error_message = f"Failed to create directory '{dir_path}': {e}"
            return False

    def add_mount(self, host_path: str, container_path: str) -> bool:
        """Registers a directory to be mounted from the host. Must be called before setup()."""
        if self.fm._state != 'INITIALIZED':
            self.fm.error_message = 'add_mount must be called before setup().'
            return False

        full_container_path = container_path if os.path.isabs(container_path) else os.path.join(self.fm._workdir, container_path)
        self._mounts.append({'source': host_path, 'target': full_container_path})
        return True

    def setup(self, workdir: Optional[str] = None) -> bool:
        """
        If a docker container was already configured, this clears it and allows for a new setup.
        Downloads (docker pull equivalent) and creates, but does not start, a docker container.

        Args:
            workdir: Optional working directory path inside the container.
                    If provided, must exist in the image or be creatable.
        """
        if self.fm._state == 'ERROR':
            return False

        # Set working directory if provided
        if workdir:
            self.fm._workdir = workdir

        # Clean up existing container if not reusing
        if self.container:
            self.cleanup()

        try:
            # Skip image pull message for better performance
            image_available = False

            # First, check if image exists locally (skip pulling)
            try:
                self.client.images.get(self.fm.image)
                image_available = True
            except docker.errors.ImageNotFound:
                pass

            # Only pull if image doesn't exist locally
            if not image_available:
                print(f"Pulling image '{self.fm.image}'...")
                try:
                    # Pull image with progress tracking
                    self._pull_image_with_progress(self.fm.image)
                    image_available = True
                except docker.errors.APIError as e:
                    error_msg = str(e).lower()
                    if 'credential' in error_msg or 'unauthorized' in error_msg:
                        print(f'Warning: Credential issue detected: {e}')
                        print(f'Please manually pull the image: docker pull {self.fm.image}')
                        print('Or fix Docker credentials configuration.')
                        return False
                    else:
                        print(f'Failed to pull image: {e}')
                        return False

            if not image_available:
                self.fm.error_message = f"Image '{self.fm.image}' is not available"
                return False

            mount_objs = [
                docker.types.Mount(target=m['target'], source=os.path.abspath(m['source']), type='bind') for m in self._mounts
            ]

            # Create the container but keep it alive with a do-nothing command
            self.container = self.client.containers.create(
                self.fm.image,
                command='tail -f /dev/null',  # Keeps container running
                mounts=mount_objs,
                working_dir=self.fm._workdir,
                detach=True,
            )
            self.container.start()

            # Ensure working directory exists (Alpine might not have /code/rundir by default)
            if not self._ensure_workdir_exists():
                return False

            # If workdir was provided, validate it exists or can be created
            if workdir and not self._validate_workdir(workdir):
                return False

            # Check if bash exists in the container
            result = self.container.exec_run(['test', '-x', '/bin/bash'])
            if result.exit_code == 0:
                self._has_bash = True
            else:
                self._has_bash = False
                print(f'Warning: Container image {self.fm.image} does not have /bin/bash available, falling back to /bin/sh')

            self.fm._state = 'CONFIGURED'
            return True
        except Exception as e:
            self.fm.error_message = f'Setup failed: {e}'
            self.fm._state = 'ERROR'
            return False

    def run(
        self, command: str, container_path: Optional[str] = '.', quiet: bool = False, config_sources: Optional[List[str]] = None
    ) -> Tuple[int, str, str]:
        """Execute command inside the container."""
        # Allow running in both CONFIGURED and EXECUTED states
        if self.fm._state not in ['CONFIGURED', 'EXECUTED']:
            self.fm.error_message = f'run must be called after setup(). {self.fm._state}'
            return -1, '', self.fm.error_message

        # Set state to EXECUTED after first successful setup
        if self.fm._state == 'CONFIGURED':
            self.fm._state = 'EXECUTED'

        # Handle working directory
        if container_path == '.':
            workdir = self.fm._workdir
        else:
            # If container_path is relative, join with workdir
            if not os.path.isabs(container_path):
                workdir = os.path.join(self.fm._workdir, container_path)
            else:
                workdir = container_path

        try:
            # Build the command with sourcing configuration files if provided
            wrapped_command = command

            # Add configuration sources if provided
            if config_sources:
                source_commands = [f"source '{source}' 2>/dev/null || true" for source in config_sources]
                config_prefix = '; '.join(source_commands)
                wrapped_command = f'{config_prefix}; {wrapped_command}'

            # Use bash with login shell if available, otherwise fall back to sh
            if self._has_bash:
                # When using bash, make it non-login if we have config sources to avoid double sourcing
                # of profile files that might be included in config_sources
                if config_sources:
                    shell_command = ['/bin/bash', '-c', wrapped_command]
                else:
                    shell_command = ['/bin/bash', '--login', '-c', command]
            else:
                # Fall back to sh and try to source /etc/profile for basic environment setup
                # if no config_sources are provided
                if not config_sources:
                    wrapped_command = f'source /etc/profile 2>/dev/null || true; {wrapped_command}'
                shell_command = ['/bin/sh', '-c', wrapped_command]

            # Get the user to run as (if image has a default user)
            exec_kwargs = {'workdir': workdir, 'demux': True}
            image_user = self._get_image_user()
            if image_user:
                exec_kwargs['user'] = image_user

            if quiet:
                # Original behavior - capture all output
                result = self.container.exec_run(shell_command, **exec_kwargs)
                exit_code = result.exit_code
                stdout, stderr = result.output
                stdout_str = stdout.decode('utf-8', 'replace') if stdout else ''
                stderr_str = stderr.decode('utf-8', 'replace') if stderr else ''
                return exit_code, stdout_str, stderr_str
            else:
                # New behavior - stream output in real-time
                # Create execution but don't start streaming yet
                exec_create_kwargs = {
                    'container': self.container.id,
                    'cmd': shell_command,
                    'workdir': workdir,
                    'stdout': True,
                    'stderr': True,
                }
                if image_user:
                    exec_create_kwargs['user'] = image_user

                exec_id = self.client.api.exec_create(**exec_create_kwargs)['Id']

                # Start execution with streaming
                stream = self.client.api.exec_start(exec_id, stream=True, demux=True)

                stdout_lines = []
                stderr_lines = []

                # Stream and capture output
                for stdout_chunk, stderr_chunk in stream:
                    if stdout_chunk:
                        chunk_str = stdout_chunk.decode('utf-8', 'replace')
                        stdout_lines.append(chunk_str)
                        # Print chunk directly without splitting into lines to preserve formatting
                        if chunk_str.strip():
                            # Remove trailing newline to avoid double newlines
                            clean_chunk = chunk_str.rstrip('\n')
                            if clean_chunk:
                                print(f'{self.fm.image.split("/")[-1]}:run: {clean_chunk}')

                    if stderr_chunk:
                        chunk_str = stderr_chunk.decode('utf-8', 'replace')
                        stderr_lines.append(chunk_str)
                        # Print chunk directly without splitting into lines to preserve formatting
                        if chunk_str.strip():
                            # Remove trailing newline to avoid double newlines
                            clean_chunk = chunk_str.rstrip('\n')
                            if clean_chunk:
                                print(f'{self.fm.image.split("/")[-1]}:run: {clean_chunk}')

                # Get the exit code after streaming completes
                exec_inspect = self.client.api.exec_inspect(exec_id)
                exit_code = exec_inspect.get('ExitCode', 0)
                if exit_code is None:
                    exit_code = 0  # Default to 0 if None

                stdout_str = ''.join(stdout_lines)
                stderr_str = ''.join(stderr_lines)

                return exit_code, stdout_str, stderr_str

        except Exception as e:
            self.fm.error_message = f'Command execution failed: {e}'
            return -1, '', str(e)

    def get_reference_container(self) -> Optional[docker.models.containers.Container]:
        """Get or create a reference container for comparing original files."""
        if self._reference_container is None:
            try:
                # Create a fresh container from the same image
                self._reference_container = self.client.containers.create(
                    self.fm.image,
                    command='tail -f /dev/null',  # Keep it alive
                    working_dir=self.fm._workdir,
                    detach=True,
                )
                self._reference_container.start()
            except Exception as e:
                self.fm.error_message = f'Failed to create reference container: {e}'
                return None
        return self._reference_container

    def _cleanup_reference_container(self) -> None:
        """Clean up reference container."""
        if self._reference_container:
            try:
                self._reference_container.kill()
                self._reference_container.remove()
                self._reference_container = None
            except Exception as e:
                print(f'Warning: Failed to clean up reference container: {e}')

    def image_checkpoint(self, name: Optional[str] = None) -> Optional[str]:
        """Create a checkpoint (Docker image) from the current container state.

        Args:
            name: Optional name for the checkpoint. If not provided, creates an anonymous
                  checkpoint that will be cleaned up when the file_manager exits.

        Returns:
            The image name/tag of the created checkpoint, or None if failed.
        """
        if self.fm._state not in ['CONFIGURED', 'EXECUTED']:
            self.fm.error_message = 'image_checkpoint must be called after setup().'
            return None

        if not self.container:
            self.fm.error_message = 'No container available for checkpoint.'
            return None

        try:
            # Generate checkpoint name
            if name:
                checkpoint_name = f'{self.fm.image}_checkpoint_{name}'
            else:
                # Anonymous checkpoint with timestamp
                timestamp = datetime.now().strftime('%Y%m%d_%H%M%S_%f')[:-3]  # milliseconds
                checkpoint_name = f'{self.fm.image}_checkpoint_anon_{timestamp}'
                # Track for cleanup
                self._checkpoints.append(checkpoint_name)

            # Get original image configuration to restore command and entrypoint
            original_config = self._get_image_config()

            # Prepare changes to restore original behavior using Docker commit format
            changes = []

            # Restore original command if it exists, otherwise use sensible defaults
            original_cmd = original_config.get('Cmd')
            original_entrypoint = original_config.get('Entrypoint')

            if original_cmd:
                # Format as Docker expects: CMD ["executable", "param1", "param2"]
                cmd_str = '["' + '", "'.join(original_cmd) + '"]'
                changes.append(f'CMD {cmd_str}')
            else:
                # No original cmd, provide interactive shell fallback
                if self._has_bash:
                    changes.append('CMD ["/bin/bash"]')
                else:
                    changes.append('CMD ["/bin/sh"]')

            # Restore original entrypoint if it exists
            if original_entrypoint:
                # Format as Docker expects: ENTRYPOINT ["executable", "param1", "param2"]
                entrypoint_str = '["' + '", "'.join(original_entrypoint) + '"]'
                changes.append(f'ENTRYPOINT {entrypoint_str}')

            # Create image from container with restored configuration
            print(f"Creating checkpoint '{checkpoint_name}' from current container state...")
            image = self.container.commit(
                repository=checkpoint_name.split(':')[0] if ':' in checkpoint_name else checkpoint_name,
                tag='latest' if ':' not in checkpoint_name else checkpoint_name.split(':', 1)[1],
                message=f'Checkpoint created by file_manager at {datetime.now().isoformat()}',
                changes=changes,
            )

            print(f'Checkpoint created successfully name:{checkpoint_name} id:{image.id}')
            return checkpoint_name

        except Exception as e:
            self.fm.error_message = f'Failed to create checkpoint: {e}'
            return None

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
