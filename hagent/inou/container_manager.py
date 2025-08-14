"""
Container Manager for HAgent

Handles Docker container lifecycle management with new mount points and
environment variable setup. Refactored from docker_manager.py with
updated paths and container initialization.
"""

import docker
import platform
import os
import threading
import sys
import time
from datetime import datetime
from typing import Optional, List, Dict, Tuple, Any

from .path_manager import PathManager


class ContainerManager:
    """
    Manages Docker container lifecycle including setup, execution, and cleanup.

    Handles new mount point structure:
    - Host repo -> /code/workspace/repo
    - Host build -> /code/workspace/build
    - Host cache -> /code/workspace/cache

    Automatically sets HAGENT_* environment variables inside container.
    """

    def __init__(self, image: str, path_manager: Optional[PathManager] = None):
        """
        Initialize ContainerManager.

        Args:
            image: Docker image name to use
            path_manager: PathManager instance for path resolution
        """
        self.image = image
        self.path_manager = path_manager or PathManager()
        self.client: Optional[docker.DockerClient] = None
        self.container: Optional[docker.models.containers.Container] = None
        self._reference_container: Optional[docker.models.containers.Container] = None
        self._image_user: Optional[str] = None
        self._has_bash: bool = False
        self._checkpoints: List[str] = []
        self._mounts: List[Dict[str, str]] = []
        self._workdir = '/code/workspace/repo'  # New default working directory

        # Initialize Docker client
        self._initialize_docker_client()

    def _initialize_docker_client(self) -> None:
        """Initialize Docker client with cross-platform support."""
        # First, try the standard docker.from_env()
        first_error = None
        try:
            self.client = docker.from_env()
            if self.client.ping():
                return  # Success!
        except Exception as err:
            first_error = err
            pass

        # If from_env() failed, try platform-specific socket paths
        socket_paths = self._get_docker_socket_paths()

        for socket_path in socket_paths:
            if os.path.exists(socket_path):
                try:
                    self.client = docker.DockerClient(base_url=f'unix://{socket_path}')
                    if self.client.ping():
                        return  # Success!
                except Exception:
                    continue

        # If all attempts failed, raise error
        raise RuntimeError(
            f'Docker client initialization failed. Tried:\n'
            f'- Environment-based connection\n'
            f'- Socket paths: {socket_paths}\n'
            f'Please ensure Docker is running and accessible.\n'
            f'Original error: {first_error if first_error else "Unknown"}'
        )

    def _get_docker_socket_paths(self) -> List[str]:
        """Get list of potential Docker socket paths based on platform."""
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
                # Lima
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
        """Pull Docker image with progress indicator."""
        spinner_chars = ['-', '\\', '|', '/']
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
        """Get information about the Docker connection for debugging."""
        if self.client is None:
            return {'status': 'ERROR', 'message': 'Docker client not initialized'}

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
            return self._image_user  # Return cached value

        try:
            if not self.client:
                return None
            image_info = self.client.images.get(self.image)
            config = image_info.attrs.get('Config', {})
            user = config.get('User')
            self._image_user = user if user else ''
            return user
        except Exception:
            self._image_user = ''
            return None

    def _get_image_config(self) -> Dict[str, Any]:
        """Get the original image configuration including command and entrypoint."""
        try:
            if not self.client:
                return {}
            image_info = self.client.images.get(self.image)
            return image_info.attrs.get('Config', {})
        except Exception:
            return {}

    def _validate_workspace_directory(self) -> bool:
        """Validate that /code/workspace/ directory exists in the container."""
        try:
            result = self.container.exec_run('test -d /code/workspace')
            if result.exit_code != 0:
                raise RuntimeError(
                    'Container image does not have /code/workspace/ directory. '
                    'This is required for the new HAgent container structure.'
                )
            return True
        except Exception as e:
            raise RuntimeError(f'Failed to validate /code/workspace/ directory: {e}')

    def _setup_container_environment(self) -> Dict[str, str]:
        """Setup HAGENT_* environment variables inside container."""
        env_vars = {
            'HAGENT_EXECUTION_MODE': 'docker',
            'HAGENT_REPO_DIR': '/code/workspace/repo',
            'HAGENT_BUILD_DIR': '/code/workspace/build',
            'HAGENT_CACHE_DIR': '/code/workspace/cache',
            'UV_PROJECT_ENVIRONMENT': '/code/workspace/cache/venv',
        }
        return env_vars

    def _setup_mount_points(self) -> List[docker.types.Mount]:
        """Setup standard mount points based on path manager."""
        mount_objs = []

        # Always mount cache directory
        cache_mount = docker.types.Mount(target='/code/workspace/cache', source=str(self.path_manager.cache_dir), type='bind')
        mount_objs.append(cache_mount)

        # Mount repo directory if available
        try:
            repo_mount = docker.types.Mount(target='/code/workspace/repo', source=str(self.path_manager.repo_dir), type='bind')
            mount_objs.append(repo_mount)
        except (AttributeError, TypeError):
            # Repo dir not available - container will use image default
            pass

        # Mount build directory if available
        try:
            build_mount = docker.types.Mount(target='/code/workspace/build', source=str(self.path_manager.build_dir), type='bind')
            mount_objs.append(build_mount)
        except (AttributeError, TypeError):
            # Build dir not available - container will use image default
            pass

        # Add any additional mounts registered via add_mount()
        for mount_config in self._mounts:
            mount_obj = docker.types.Mount(
                target=mount_config['target'], source=os.path.abspath(mount_config['source']), type='bind'
            )
            mount_objs.append(mount_obj)

        return mount_objs

    def add_mount(self, host_path: str, container_path: str) -> bool:
        """Register additional directory mount. Must be called before setup()."""
        if self.container is not None:
            raise RuntimeError('add_mount must be called before setup()')

        full_container_path = container_path if os.path.isabs(container_path) else os.path.join(self._workdir, container_path)
        self._mounts.append({'source': host_path, 'target': full_container_path})
        return True

    def setup(self, workdir: Optional[str] = None) -> bool:
        """
        Create and start Docker container with new mount structure.

        Args:
            workdir: Optional working directory path inside the container

        Returns:
            True if setup successful, False otherwise
        """
        if workdir:
            self._workdir = workdir

        # Clean up existing container
        if self.container:
            self.cleanup()

        try:
            # Check if image exists locally, pull if needed
            image_available = False
            try:
                self.client.images.get(self.image)
                image_available = True
            except docker.errors.ImageNotFound:
                pass

            if not image_available:
                print(f"Pulling image '{self.image}'...")
                try:
                    self._pull_image_with_progress(self.image)
                    image_available = True
                except docker.errors.APIError as e:
                    error_msg = str(e).lower()
                    if 'credential' in error_msg or 'unauthorized' in error_msg:
                        print(f'Warning: Credential issue detected: {e}')
                        print(f'Please manually pull the image: docker pull {self.image}')
                        return False
                    else:
                        print(f'Failed to pull image: {e}')
                        return False

            if not image_available:
                raise RuntimeError(f"Image '{self.image}' is not available")

            # Setup mount points and environment
            mount_objs = self._setup_mount_points()
            env_vars = self._setup_container_environment()

            # Create the container
            self.container = self.client.containers.create(
                self.image,
                command='tail -f /dev/null',  # Keep container running
                mounts=mount_objs,
                environment=env_vars,
                working_dir=self._workdir,
                detach=True,
            )
            self.container.start()

            # Validate /code/workspace/ directory exists
            self._validate_workspace_directory()

            # Ensure working directory exists
            result = self.container.exec_run(f'mkdir -p {self._workdir}')
            if result.exit_code != 0:
                raise RuntimeError(f'Failed to create working directory: {self._workdir}')

            # Check if bash exists in the container
            result = self.container.exec_run(['test', '-x', '/bin/bash'])
            if result.exit_code == 0:
                self._has_bash = True
            else:
                self._has_bash = False
                print(f'Warning: Container image {self.image} does not have /bin/bash, falling back to /bin/sh')

            return True

        except Exception as e:
            raise RuntimeError(f'Container setup failed: {e}')

    def run(
        self, command: str, container_path: Optional[str] = '.', quiet: bool = False, config_sources: Optional[List[str]] = None
    ) -> Tuple[int, str, str]:
        """
        Execute command inside the container.

        Args:
            command: Command to execute
            container_path: Working directory inside container
            quiet: Whether to run in quiet mode
            config_sources: Optional configuration files to source

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        if not self.container:
            raise RuntimeError('Container not set up. Call setup() first.')

        # Handle working directory
        if container_path == '.':
            workdir = self._workdir
        else:
            if not os.path.isabs(container_path):
                workdir = os.path.join(self._workdir, container_path)
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
                if config_sources:
                    shell_command = ['/bin/bash', '-c', wrapped_command]
                else:
                    shell_command = ['/bin/bash', '--login', '-c', command]
            else:
                if not config_sources:
                    wrapped_command = f'source /etc/profile 2>/dev/null || true; {wrapped_command}'
                shell_command = ['/bin/sh', '-c', wrapped_command]

            # Get the user to run as (if image has a default user)
            exec_kwargs = {'workdir': workdir, 'demux': True}
            image_user = self._get_image_user()
            if image_user:
                exec_kwargs['user'] = image_user

            if quiet:
                # Capture all output
                result = self.container.exec_run(shell_command, **exec_kwargs)
                exit_code = result.exit_code
                stdout, stderr = result.output
                stdout_str = stdout.decode('utf-8', 'replace') if stdout else ''
                stderr_str = stderr.decode('utf-8', 'replace') if stderr else ''
                return exit_code, stdout_str, stderr_str
            else:
                # Stream output in real-time
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
                stream = self.client.api.exec_start(exec_id, stream=True, demux=True)

                stdout_lines = []
                stderr_lines = []

                # Stream and capture output
                for stdout_chunk, stderr_chunk in stream:
                    if stdout_chunk:
                        chunk_str = stdout_chunk.decode('utf-8', 'replace')
                        stdout_lines.append(chunk_str)
                        if chunk_str.strip():
                            clean_chunk = chunk_str.rstrip('\n')
                            if clean_chunk:
                                print(f'{self.image.split("/")[-1]}:run: {clean_chunk}')

                    if stderr_chunk:
                        chunk_str = stderr_chunk.decode('utf-8', 'replace')
                        stderr_lines.append(chunk_str)
                        if chunk_str.strip():
                            clean_chunk = chunk_str.rstrip('\n')
                            if clean_chunk:
                                print(f'{self.image.split("/")[-1]}:run: {clean_chunk}')

                # Get the exit code after streaming completes
                exec_inspect = self.client.api.exec_inspect(exec_id)
                exit_code = exec_inspect.get('ExitCode', 0)
                if exit_code is None:
                    exit_code = 0

                stdout_str = ''.join(stdout_lines)
                stderr_str = ''.join(stderr_lines)

                return exit_code, stdout_str, stderr_str

        except Exception as e:
            raise RuntimeError(f'Command execution failed: {e}')

    def image_checkpoint(self, name: Optional[str] = None) -> Optional[str]:
        """
        Create a checkpoint (Docker image) from the current container state.

        Args:
            name: Optional name for the checkpoint

        Returns:
            The image name/tag of the created checkpoint, or None if failed
        """
        if not self.container:
            raise RuntimeError('No container available for checkpoint')

        try:
            # Generate checkpoint name
            if name:
                checkpoint_name = f'{self.image}_checkpoint_{name}'
            else:
                # Anonymous checkpoint with timestamp
                timestamp = datetime.now().strftime('%Y%m%d_%H%M%S_%f')[:-3]
                checkpoint_name = f'{self.image}_checkpoint_anon_{timestamp}'
                self._checkpoints.append(checkpoint_name)

            # Get original image configuration
            original_config = self._get_image_config()

            # Prepare changes to restore original behavior
            changes = []

            original_cmd = original_config.get('Cmd')
            original_entrypoint = original_config.get('Entrypoint')

            if original_cmd:
                cmd_str = '["' + '", "'.join(original_cmd) + '"]'
                changes.append(f'CMD {cmd_str}')
            else:
                if self._has_bash:
                    changes.append('CMD ["/bin/bash"]')
                else:
                    changes.append('CMD ["/bin/sh"]')

            if original_entrypoint:
                entrypoint_str = '["' + '", "'.join(original_entrypoint) + '"]'
                changes.append(f'ENTRYPOINT {entrypoint_str}')

            # Create image from container with restored configuration
            print(f"Creating checkpoint '{checkpoint_name}' from current container state...")
            image = self.container.commit(
                repository=checkpoint_name.split(':')[0] if ':' in checkpoint_name else checkpoint_name,
                tag='latest' if ':' not in checkpoint_name else checkpoint_name.split(':', 1)[1],
                message=f'Checkpoint created by container_manager at {datetime.now().isoformat()}',
                changes=changes,
            )

            print(f'Checkpoint created successfully name:{checkpoint_name} id:{image.id}')
            return checkpoint_name

        except Exception as e:
            raise RuntimeError(f'Failed to create checkpoint: {e}')

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
                        if container.image.id == image_id:
                            print(f'Stopping container {container.short_id} using checkpoint {checkpoint_name}')
                            if container.status == 'running':
                                container.kill()
                            container.remove()
                    except Exception as e:
                        print(f'Warning: Failed to cleanup container {container.short_id}: {e}')

                # Remove the image
                self.client.images.remove(checkpoint_name, force=True)
                try:
                    self.client.images.remove(image_id, force=True)
                except docker.errors.ImageNotFound:
                    pass

                print(f'Cleaned up anonymous checkpoint: {checkpoint_name}')
            except docker.errors.ImageNotFound:
                pass
            except Exception as e:
                print(f'Warning: Failed to clean up checkpoint {checkpoint_name}: {e}')

        self._checkpoints.clear()

    def cleanup(self) -> None:
        """Clean up container and resources."""
        if self.container:
            try:
                self.container.kill()
                self.container.remove()
                self.container = None
            except docker.errors.APIError:
                pass

        # Clean up reference container
        if self._reference_container:
            try:
                self._reference_container.kill()
                self._reference_container.remove()
                self._reference_container = None
            except docker.errors.APIError:
                pass

        # Clean up anonymous checkpoints
        self._cleanup_anonymous_checkpoints()

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
            pass
