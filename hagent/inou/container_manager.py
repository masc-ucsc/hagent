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
import atexit
import weakref
from datetime import datetime
from typing import Optional, List, Dict, Tuple, Any

from .path_manager import PathManager

# Global registry to track ContainerManager instances for cleanup
_container_manager_registry: weakref.WeakSet = weakref.WeakSet()
_cleanup_registered = False


def _validate_mount_path(host_path: str) -> Tuple[bool, str]:
    """
    Validate that a host path is safe to mount and won't damage the hagent repository.

    Args:
        host_path: The host path to validate

    Returns:
        Tuple of (is_valid, error_message)
    """
    try:
        # Get the absolute path and resolve any symlinks
        abs_path = os.path.realpath(os.path.abspath(host_path))

        # Get the hagent repository root directory based on this file's location
        # This file is at hagent/inou/container_manager.py, so go up 3 levels to get to repo root
        # /path/to/hagent-repo/hagent/inou/container_manager.py -> /path/to/hagent-repo
        current_file = os.path.realpath(__file__)
        hagent_root = os.path.dirname(os.path.dirname(os.path.dirname(current_file)))

        # Log mount validation attempts for debugging
        print(f'🔍 MOUNT VALIDATION: {host_path} -> {abs_path}')
        print(f'🔍 HAGENT ROOT: {hagent_root}')

        # Check if we're trying to mount the hagent repo root
        if abs_path == hagent_root:
            error_msg = f'SAFETY ERROR: Cannot mount hagent repository root directory: {abs_path}'
            print(f'🚨 {error_msg}')
            return False, error_msg

        # Check if we're trying to mount any directory inside the hagent repository
        if abs_path.startswith(hagent_root + os.sep):
            # Allow mounting directories inside ./output
            output_dir = os.path.realpath(os.path.join(hagent_root, 'output'))
            if abs_path.startswith(output_dir + os.sep) or abs_path == output_dir:
                print(f'✅ ALLOWING OUTPUT MOUNT: {abs_path}')
                return True, ''

            # Disallow any other directory inside the hagent repo
            relative_path = os.path.relpath(abs_path, hagent_root)
            error_msg = (
                f'SAFETY ERROR: Cannot mount directory inside hagent repository (except ./output): {relative_path} -> {abs_path}'
            )
            print(f'🚨 {error_msg}')
            return (False, error_msg)

        # Allow mounting directories outside the hagent repo entirely
        print(f'✅ ALLOWING EXTERNAL MOUNT: {abs_path}')
        return True, ''

    except Exception as e:
        error_msg = f'SAFETY ERROR: Failed to validate mount path {host_path}: {e}'
        print(f'🚨 {error_msg}')
        return False, error_msg


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
        global _cleanup_registered, _container_manager_registry

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
        self.error_message: str = ''  # For error handling like Tool pattern
        self._cleaned_up = False  # Track cleanup state

        # Register this instance for cleanup
        _container_manager_registry.add(self)

        # Register global cleanup function once
        if not _cleanup_registered:
            atexit.register(_cleanup_all_containers)
            _cleanup_registered = True

        # Try to initialize Docker client - errors will be stored for later
        try:
            self._initialize_docker_client()
        except Exception as e:
            self.set_error(str(e))

    def set_error(self, message: str) -> None:
        """Set error message following Tool pattern."""
        self.error_message = message

    def get_error(self) -> str:
        """Get current error message following Tool pattern."""
        return self.error_message

    def _check_colima_mount_type(self) -> None:
        """Check if Colima is using a supported mount type (virtiofs or 9p)."""
        import platform
        import subprocess

        # Only check on macOS where Colima is commonly used
        if platform.system() != 'Darwin':
            return

        try:
            # Check if colima command exists
            result = subprocess.run(['which', 'colima'], capture_output=True, text=True)
            if result.returncode != 0:
                return  # Colima not installed, probably using Docker Desktop

            # Check colima status to get mount type
            result = subprocess.run(['colima', 'status'], capture_output=True, text=True)
            if result.returncode != 0:
                return  # Colima not running

            status_output = result.stdout

            # Look for mount type in output
            if 'mountType: sshfs' in status_output:
                error_msg = (
                    '⚠️  COLIMA MOUNT TYPE WARNING ⚠️\n\n'
                    "Colima is using 'sshfs' mount type, which can cause issues with I/O intensive operations.\n"
                    "For better performance and reliability, please switch to 'virtiofs' or '9p':\n\n"
                    '  colima stop\n'
                    '  colima start --mount-type virtiofs\n\n'
                    'Or if virtiofs is not supported:\n'
                    '  colima start --mount-type 9p\n\n'
                    'See the README for more details on Colima configuration.'
                )
                print(error_msg)
                # Don't fail here, just warn - let user decide

        except Exception:
            # If we can't check Colima status, just continue
            pass

    def _initialize_docker_client(self) -> None:
        """Initialize Docker client with cross-platform support."""
        # Check Colima mount type on macOS
        self._check_colima_mount_type()

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

        # If all attempts failed, raise error to be caught by __init__
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

    def _wait_for_container_ready(self, timeout: int = 10) -> bool:
        """Wait for container to be ready for exec commands after start()."""
        import time

        last_status = None
        last_error = None
        
        for attempt in range(timeout * 10):  # 100ms intervals
            try:
                self.container.reload()
                last_status = self.container.status
                
                if self.container.status == 'running':
                    # Try a simple exec to verify it's ready
                    self.container.exec_run('true')
                    return True
                elif self.container.status in ['exited', 'dead']:
                    # Container failed to start or crashed
                    break
            except Exception as e:
                last_error = str(e)
            time.sleep(0.1)

        # Provide detailed error information
        error_parts = [f'Container failed to become ready within {timeout} seconds']
        if last_status:
            error_parts.append(f'Final status: {last_status}')
        if last_error:
            error_parts.append(f'Last error: {last_error}')
            
        # If container exited, get its logs for debugging
        if last_status in ['exited', 'dead']:
            try:
                logs = self.container.logs(tail=50).decode('utf-8', errors='replace')
                if logs.strip():
                    error_parts.append(f'Container logs: {logs}')
            except Exception:
                pass
        
        self.set_error('. '.join(error_parts))
        return False

    def _setup_container_environment(self) -> Dict[str, str]:
        """Setup HAGENT_* environment variables inside container."""
        env_vars = {
            'HAGENT_EXECUTION_MODE': 'docker',
            'HAGENT_REPO_DIR': '/code/workspace/repo',
            'HAGENT_BUILD_DIR': '/code/workspace/build',
            'HAGENT_CACHE_DIR': '/code/workspace/cache',
            'UV_PROJECT_ENVIRONMENT': '/code/workspace/cache/venv',
            # Set LOCAL_USER_ID for the container's entrypoint script to use host UID
            'LOCAL_USER_ID': str(os.getuid()),
            'LOCAL_GROUP_ID': str(os.getgid()),
        }
        return env_vars

    def _get_security_options(self) -> List[str]:
        """
        Get security options to restrict container capabilities and prevent privilege escalation.

        Returns:
            List of security options to apply to the container
        """
        return [
            'no-new-privileges:true',  # Prevent processes from gaining additional privileges
            'apparmor:docker-default',  # Use default AppArmor profile if available
        ]

    def _setup_mount_points(self) -> List[docker.types.Mount]:
        """Setup standard mount points based on path manager."""
        mount_objs = []

        # Always mount cache directory - ensure it exists first
        # Use environment variable directly if available, otherwise use path_manager
        cache_dir_path = os.environ.get('HAGENT_CACHE_DIR')
        if not cache_dir_path:
            try:
                cache_dir_path = str(self.path_manager.cache_dir)
            except (AttributeError, TypeError) as e:
                self.set_error(f'Cache directory not available: {e}')
                return []

        # Only mount cache directory if it's a real host path (not a container path)
        if not cache_dir_path.startswith('/code/workspace/'):
            # Validate the mount path for safety
            is_valid, error_msg = _validate_mount_path(cache_dir_path)
            if not is_valid:
                self.set_error(f'Cache directory mount validation failed: {error_msg}')
                return []

            # Ensure cache directory exists before mounting
            os.makedirs(cache_dir_path, exist_ok=True)
            # Resolve symlinks (important on macOS where /var -> /private/var)
            cache_dir_path = os.path.realpath(cache_dir_path)

            cache_mount = docker.types.Mount(target='/code/workspace/cache', source=cache_dir_path, type='bind')
            mount_objs.append(cache_mount)

        # Mount repo directory if available
        repo_dir_path = os.environ.get('HAGENT_REPO_DIR')
        if not repo_dir_path:
            try:
                repo_dir_path = str(self.path_manager.repo_dir)
            except (AttributeError, TypeError):
                # Repo dir not available - container will use image default
                repo_dir_path = None

        if repo_dir_path and not repo_dir_path.startswith('/code/workspace/'):
            # Validate the mount path for safety
            is_valid, error_msg = _validate_mount_path(repo_dir_path)
            if not is_valid:
                self.set_error(f'Repo directory mount validation failed: {error_msg}')
                return []

            # Ensure repo directory exists before mounting
            os.makedirs(repo_dir_path, exist_ok=True)
            # Resolve symlinks (important on macOS where /var -> /private/var)
            repo_dir_path = os.path.realpath(repo_dir_path)
            repo_mount = docker.types.Mount(target='/code/workspace/repo', source=repo_dir_path, type='bind')
            mount_objs.append(repo_mount)

        # Mount build directory if available
        build_dir_path = os.environ.get('HAGENT_BUILD_DIR')
        if not build_dir_path:
            try:
                build_dir_path = str(self.path_manager.build_dir)
            except (AttributeError, TypeError):
                # Build dir not available - container will use image default
                build_dir_path = None

        if build_dir_path and not build_dir_path.startswith('/code/workspace/'):
            # Validate the mount path for safety
            is_valid, error_msg = _validate_mount_path(build_dir_path)
            if not is_valid:
                self.set_error(f'Build directory mount validation failed: {error_msg}')
                return []

            # Ensure build directory exists before mounting
            os.makedirs(build_dir_path, exist_ok=True)
            # Resolve symlinks (important on macOS where /var -> /private/var)
            build_dir_path = os.path.realpath(build_dir_path)
            build_mount = docker.types.Mount(target='/code/workspace/build', source=build_dir_path, type='bind')
            mount_objs.append(build_mount)

        # Add any additional mounts registered via add_mount()
        for mount_config in self._mounts:
            source_path = os.path.abspath(mount_config['source'])
            # Validate the mount path for safety
            is_valid, error_msg = _validate_mount_path(source_path)
            if not is_valid:
                self.set_error(f'Additional mount validation failed: {error_msg}')
                return []

            # Ensure additional mount source exists
            os.makedirs(source_path, exist_ok=True)
            # Resolve symlinks (important on macOS where /var -> /private/var)
            source_path = os.path.realpath(source_path)
            mount_obj = docker.types.Mount(target=mount_config['target'], source=source_path, type='bind')
            mount_objs.append(mount_obj)

        return mount_objs

    def add_mount(self, host_path: str, container_path: str) -> bool:
        """Register additional directory mount. Must be called before setup()."""
        if self.container is not None:
            self.set_error('add_mount must be called before setup()')
            return False

        full_container_path = container_path if os.path.isabs(container_path) else os.path.join(self._workdir, container_path)
        self._mounts.append({'source': host_path, 'target': full_container_path})
        return True

    def create_container(self, repo_dir=None, build_dir=None, cache_dir=None, workdir=None):
        """
        Create container with standardized mount points.

        This is the new standardized interface for Phase 5 & 6.

        Args:
            repo_dir: Optional host repo directory to mount
            build_dir: Optional host build directory to mount
            cache_dir: Required host cache directory to mount
            workdir: Optional working directory (defaults to /code/workspace/repo)

        Returns:
            Docker container object if successful, None otherwise
        """
        # Set working directory
        working_dir = workdir or '/code/workspace/repo'

        # Setup mount points
        mounts = []
        env_vars = {
            'HAGENT_EXECUTION_MODE': 'docker',
            'HAGENT_CACHE_DIR': '/code/workspace/cache',
            'UV_PROJECT_ENVIRONMENT': '/code/workspace/cache/venv',
            # Set LOCAL_USER_ID for the container's entrypoint script to use host UID
            'LOCAL_USER_ID': str(os.getuid()),
            'LOCAL_GROUP_ID': str(os.getgid()),
        }

        # Optional mounts - only mount if the path is a real host directory
        if repo_dir and not str(repo_dir).startswith('/code/workspace/'):
            # Validate the mount path for safety
            is_valid, error_msg = _validate_mount_path(str(repo_dir))
            if not is_valid:
                self.set_error(f'Repo directory mount validation failed: {error_msg}')
                return None
            mounts.append(f'{repo_dir}:/code/workspace/repo')
            env_vars['HAGENT_REPO_DIR'] = '/code/workspace/repo'

        if build_dir and not str(build_dir).startswith('/code/workspace/'):
            # Validate the mount path for safety
            is_valid, error_msg = _validate_mount_path(str(build_dir))
            if not is_valid:
                self.set_error(f'Build directory mount validation failed: {error_msg}')
                return None
            mounts.append(f'{build_dir}:/code/workspace/build')
            env_vars['HAGENT_BUILD_DIR'] = '/code/workspace/build'

        # Mount cache directory only if it's a real host directory
        if cache_dir and not str(cache_dir).startswith('/code/workspace/'):
            # Validate the mount path for safety
            is_valid, error_msg = _validate_mount_path(str(cache_dir))
            if not is_valid:
                self.set_error(f'Cache directory mount validation failed: {error_msg}')
                return None
            mounts.append(f'{cache_dir}:/code/workspace/cache')

        # Always set the environment variables for container paths
        env_vars['HAGENT_REPO_DIR'] = '/code/workspace/repo'
        env_vars['HAGENT_BUILD_DIR'] = '/code/workspace/build'

        return self._create_container_with_mounts(mounts, env_vars, working_dir)

    def _create_container_with_mounts(self, mounts, env_vars, working_dir):
        """
        Internal method to create container with specified mounts and environment.

        Args:
            mounts: List of mount strings in format "host:container"
            env_vars: Dictionary of environment variables
            working_dir: Working directory inside container

        Returns:
            Docker container object if successful, None otherwise
        """
        try:
            # Ensure Docker client is available
            if not self.client:
                self.set_error('Docker client not initialized')
                return None

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
                        return None
                    else:
                        print(f'Failed to pull image: {e}')
                        return None

            if not image_available:
                self.set_error(f"Image '{self.image}' is not available")
                return None

            # Convert mount strings to Mount objects
            mount_objs = []
            for mount_str in mounts:
                host_path, container_path = mount_str.split(':')
                abs_host_path = os.path.abspath(host_path)

                # Validate the mount path for safety
                is_valid, error_msg = _validate_mount_path(abs_host_path)
                if not is_valid:
                    self.set_error(f'Mount validation failed for {mount_str}: {error_msg}')
                    return None

                # Ensure host directory exists before mounting
                os.makedirs(abs_host_path, exist_ok=True)
                # Resolve symlinks (important on macOS where /var -> /private/var)
                abs_host_path = os.path.realpath(abs_host_path)
                mount_obj = docker.types.Mount(target=container_path, source=abs_host_path, type='bind')
                mount_objs.append(mount_obj)

            # Add LOCAL_USER_ID to environment if not already present
            if 'LOCAL_USER_ID' not in env_vars:
                env_vars['LOCAL_USER_ID'] = str(os.getuid())
                env_vars['LOCAL_GROUP_ID'] = str(os.getgid())

            # Create the container with security restrictions
            # Note: We start as root to allow LOCAL_USER_ID mechanism to work,
            # but with restricted capabilities and no-new-privileges
            container = self.client.containers.create(
                self.image,
                command='tail -f /dev/null',  # Keep container running
                mounts=mount_objs,
                environment=env_vars,
                working_dir=working_dir,
                detach=True,
                user='root',  # Start as root to allow LOCAL_USER_ID switching
                # Security options to prevent privilege escalation
                security_opt=self._get_security_options(),
                # Drop dangerous capabilities, keep minimal ones for user switching
                cap_drop=['NET_ADMIN', 'NET_RAW', 'SYS_ADMIN', 'SYS_TIME', 'SYS_MODULE'],
                cap_add=['SETUID', 'SETGID', 'DAC_OVERRIDE', 'CHOWN', 'FOWNER'],  # For user switching and file ops
                # Prevent new privileges after initial setup
                read_only=False,  # We need write access to mounted volumes
            )

            container.start()

            # Wait for container to be ready for exec commands
            # Temporarily store the container to use the existing wait method
            original_container = self.container
            self.container = container
            try:
                container_ready = self._wait_for_container_ready()
            finally:
                self.container = original_container

            if not container_ready:
                self.set_error('Container failed to start properly')
                container.remove(force=True)
                return None

            # Validate container workspace structure
            if not self._validate_container_workspace(container):
                container.remove(force=True)
                return None

            # Fix permissions for mounted directories to match container user
            # Temporarily store the container to use the existing method
            original_container = self.container
            self.container = container
            try:
                if not self._fix_mounted_directory_permissions():
                    print('Warning: Could not fix mounted directory permissions')
            finally:
                self.container = original_container

            return container

        except Exception as e:
            self.set_error(f'Failed to create container: {e}')
            return None

    def _validate_container_workspace(self, container) -> bool:
        """Validate that container has required /code/workspace/ structure."""
        try:
            result = container.exec_run('test -d /code/workspace')
            if result.exit_code != 0:
                self.set_error(
                    'Container image does not have /code/workspace/ directory. '
                    'This is required for the new HAgent container structure.'
                )
                return False
            return True
        except Exception as e:
            self.set_error(f'Failed to validate /code/workspace/ directory: {e}')
            return False

    def _fix_mounted_directory_permissions(self) -> bool:
        """
        Fix permissions on mounted directories to allow container user to write.

        This addresses permission issues in CI environments where the host
        user UID doesn't match the container user UID.
        """
        try:
            # Get the container user's UID and GID
            result = self.container.exec_run('id -u')
            if result.exit_code != 0:
                self.set_error('Failed to get container user UID')
                return False
            container_uid = result.output.decode('utf-8').strip()

            result = self.container.exec_run('id -g')
            if result.exit_code != 0:
                self.set_error('Failed to get container user GID')
                return False
            container_gid = result.output.decode('utf-8').strip()

            # List of mounted directories that need permission fixes
            mount_points = ['/code/workspace/repo', '/code/workspace/build', '/code/workspace/cache']

            for mount_point in mount_points:
                # Check if the mount point exists
                result = self.container.exec_run(f'test -d {mount_point}')
                if result.exit_code == 0:
                    # For performance, just fix the directory itself rather than recursively
                    # First, try to chown as root (if available in the image)
                    result = self.container.exec_run(f'chown {container_uid}:{container_gid} {mount_point}', user='root')
                    if result.exit_code != 0:
                        # If root user is not available, try chmod to make it writable by all
                        result = self.container.exec_run(f'chmod 755 {mount_point}')
                        if result.exit_code != 0:
                            # As a last resort, just try to make the directory writable
                            result = self.container.exec_run(f'chmod 777 {mount_point}')
                            if result.exit_code != 0:
                                print(f'Warning: Could not fix permissions for {mount_point}')

            return True

        except Exception as e:
            self.set_error(f'Failed to fix mounted directory permissions: {e}')
            return False

    def setup(self, automount: bool = True) -> bool:
        """
        Create and start Docker container with new mount structure.
        Working directory is always /code/workspace/repo.

        Args:
            automount: If True (default), automatically mount repo, build, and cache directories.
                      If False, create container with no automatic mounts.

        Returns:
            True if setup successful, False otherwise
        """

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
                self.set_error(f"Image '{self.image}' is not available")
                return False

            # Setup mount points and environment based on automount setting
            if automount:
                mount_objs = self._setup_mount_points()
                env_vars = self._setup_container_environment()
            else:
                mount_objs = []
                env_vars = {
                    'HAGENT_EXECUTION_MODE': 'docker',
                    # Set LOCAL_USER_ID for the container's entrypoint script to use host UID
                    'LOCAL_USER_ID': str(os.getuid()),
                    'LOCAL_GROUP_ID': str(os.getgid()),
                }

            # Create the container with security restrictions
            # Note: We start as root to allow LOCAL_USER_ID mechanism to work,
            # but with restricted capabilities and no-new-privileges
            self.container = self.client.containers.create(
                self.image,
                command='tail -f /dev/null',  # Keep container running
                mounts=mount_objs,
                environment=env_vars,
                working_dir=self._workdir,
                detach=True,
                user='root',  # Start as root to allow LOCAL_USER_ID switching
                # Security options to prevent privilege escalation
                security_opt=self._get_security_options(),
                # Drop dangerous capabilities, keep minimal ones for user switching
                cap_drop=['NET_ADMIN', 'NET_RAW', 'SYS_ADMIN', 'SYS_TIME', 'SYS_MODULE'],
                cap_add=['SETUID', 'SETGID', 'DAC_OVERRIDE', 'CHOWN', 'FOWNER'],  # For user switching and file ops
                # Prevent new privileges after initial setup
                read_only=False,  # We need write access to mounted volumes
            )
            self.container.start()

            # Wait for container to be ready for exec commands
            if not self._wait_for_container_ready():
                return False

            # Validate /code/workspace/ directory exists
            if not self._validate_container_workspace(self.container):
                return False

            # Ensure working directory exists
            result = self.container.exec_run(f'mkdir -p {self._workdir}')
            if result.exit_code != 0:
                self.set_error(f'Failed to create working directory: {self._workdir}')
                return False

            # Fix permissions for mounted directories to match container user (only if automount is enabled)
            if automount and not self._fix_mounted_directory_permissions():
                return False

            # Check if bash exists in the container
            result = self.container.exec_run(['test', '-x', '/bin/bash'])
            if result.exit_code == 0:
                self._has_bash = True
            else:
                self._has_bash = False
                print(f'Warning: Container image {self.image} does not have /bin/bash, falling back to /bin/sh')

            return True

        except Exception as e:
            self.set_error(f'Container setup failed: {e}')
            return False

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
            self.set_error('Container not set up. Call setup() first.')
            return -1, '', 'Container not set up'

        # Handle working directory
        if container_path == '.':
            workdir = self._workdir
        else:
            if not os.path.isabs(container_path):
                workdir = os.path.join(self._workdir, container_path)
            else:
                workdir = container_path

            # Validate that the container path exists
            if not self._validate_container_path(workdir):
                error_msg = f'Directory does not exist in container: {workdir}'
                self.set_error(error_msg)
                return -1, '', error_msg

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

            # Set execution parameters
            exec_kwargs = {'workdir': workdir, 'demux': True}

            # Important: Don't specify a user - let the container use the user it was switched to
            # by the entrypoint script (via LOCAL_USER_ID). Specifying a user here would override
            # the user switching that happened during container startup.

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
                # Don't specify user - let container use the user it was switched to

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
            self.set_error(f'Command execution failed: {e}')
            return -1, '', str(e)

    def image_checkpoint(self, name: Optional[str] = None) -> Optional[str]:
        """
        Create a checkpoint (Docker image) from the current container state.

        Args:
            name: Optional name for the checkpoint

        Returns:
            The image name/tag of the created checkpoint, or None if failed
        """
        if not self.container:
            self.set_error('No container available for checkpoint')
            return None

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
            self.set_error(f'Failed to create checkpoint: {e}')
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
        if self._cleaned_up:
            return  # Already cleaned up

        self._cleaned_up = True

        if self.container:
            try:
                if self.container.status == 'running':
                    self.container.kill()
                self.container.remove()
                self.container = None
            except docker.errors.APIError:
                pass
            except Exception:
                pass

        # Clean up reference container
        if self._reference_container:
            try:
                if self._reference_container.status == 'running':
                    self._reference_container.kill()
                self._reference_container.remove()
                self._reference_container = None
            except docker.errors.APIError:
                pass
            except Exception:
                pass

        # Clean up anonymous checkpoints
        self._cleanup_anonymous_checkpoints()

    def get_reference_container(self) -> Optional['docker.models.containers.Container']:
        """Get or create a reference container for comparing original files."""
        if self._reference_container is None:
            try:
                # Create a fresh container from the same image
                self._reference_container = self.client.containers.create(
                    self.image,
                    command='tail -f /dev/null',  # Keep it alive
                    working_dir=self._workdir,
                    detach=True,
                )
                self._reference_container.start()
            except Exception as e:
                self.set_error(f'Failed to create reference container: {e}')
                return None
        return self._reference_container

    def _validate_container_path(self, container_path: str) -> bool:
        """Validate that a container path exists in the repo."""
        try:
            # Check if the path exists in the container
            result = self.container.exec_run(f'test -e {container_path}')
            return result.exit_code == 0
        except Exception:
            return False

    def set_cwd(self, new_workdir: str) -> bool:
        """
        Change the working directory with validation.

        Args:
            new_workdir: New working directory path (relative to /code/workspace/repo or absolute)

        Returns:
            True if successful, False if path doesn't exist
        """
        if not self.container:
            self.set_error('Container not set up. Call setup() first.')
            return False

        # Convert relative paths to absolute
        if not os.path.isabs(new_workdir):
            target_workdir = os.path.join('/code/workspace/repo', new_workdir)
        else:
            target_workdir = new_workdir

        # Validate that the path exists and is a directory
        if not self._validate_container_path(target_workdir):
            self.set_error(f'Directory does not exist in container: {target_workdir}')
            return False

        # Check if it's actually a directory
        try:
            result = self.container.exec_run(f'test -d {target_workdir}')
            if result.exit_code != 0:
                self.set_error(f'Path exists but is not a directory: {target_workdir}')
                return False
        except Exception as e:
            self.set_error(f'Failed to validate directory: {e}')
            return False

        # Update the working directory
        self._workdir = target_workdir
        return True

    def _ensure_container_directory(self, dir_path: str) -> bool:
        """Ensure a directory exists in the container."""
        try:
            # Create directory if it doesn't exist
            result = self.container.exec_run(f'mkdir -p {dir_path}')
            return result.exit_code == 0
        except Exception as e:
            print(f"Failed to create directory '{dir_path}': {e}", file=sys.stderr)
            return False

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


def _cleanup_all_containers():
    """
    Global cleanup function called at exit to ensure all containers are cleaned up.

    This function is registered with atexit and will clean up any containers
    that weren't properly cleaned up due to test interruptions or failures.
    """
    global _container_manager_registry

    # Clean up any remaining container managers
    managers_to_cleanup = list(_container_manager_registry)
    if managers_to_cleanup:
        print(f'\n⚠️  atexit: Cleaning up {len(managers_to_cleanup)} remaining ContainerManager instances...')

        for manager in managers_to_cleanup:
            try:
                if hasattr(manager, 'cleanup') and not getattr(manager, '_cleaned_up', False):
                    manager.cleanup()
            except Exception:
                pass
