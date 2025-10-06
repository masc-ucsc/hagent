"""
Container Manager for HAgent

Handles Docker container lifecycle management with new mount points and
environment variable setup. Refactored from docker_manager.py with
updated paths and container initialization.
"""

import docker
import platform
import os
import posixpath
import threading
import sys
import time
import atexit
import weakref
import random
import uuid
import signal
import io
import tarfile
from datetime import datetime
from typing import Optional, List, Dict, Tuple, Any

from .path_manager import PathManager

# Global registry to track ContainerManager instances for cleanup
_container_manager_registry: weakref.WeakSet = weakref.WeakSet()
_cleanup_registered = False

# Session-scoped labels to mark containers created by this Python process
_SESSION_LABEL_KEY = 'hagent.session'
_OWNER_PID_LABEL_KEY = 'hagent.owner_pid'
_MANAGED_LABEL_KEY = 'hagent.managed'
_SESSION_ID = str(uuid.uuid4())
_cleanup_running = False

# Global state to track if we're in validated Docker mode
_docker_workspace_validated = False


class ContainerNotReady(Exception):
    """Exception raised when container fails to become ready within timeout."""

    pass


def is_docker_workspace_ready() -> bool:
    """
    Check if Docker workspace has been validated and is ready.

    Returns:
        True if running in Docker mode with validated workspace, False otherwise
    """
    return _docker_workspace_validated


def is_docker_mode() -> bool:
    """
    Check if we're running in Docker execution mode.

    Returns:
        True if HAGENT_EXECUTION_MODE=docker, False otherwise
    """
    return PathManager().is_docker_mode()


def _default_ready_predicate(container: 'docker.models.containers.Container') -> bool:
    """
    Default readiness check: container is running AND (no Health section OR healthy).
    """
    container.reload()  # refresh attrs/status from engine
    state = container.attrs.get('State', {})
    if state.get('Status') != 'running':
        return False
    health = state.get('Health')
    return (health is None) or (health.get('Status') == 'healthy')


def _validate_docker_workspace(container: 'docker.models.containers.Container') -> bool:
    """
    Comprehensive Docker workspace validation. This is the single place where we check
    that all required workspace directories exist and are accessible.

    Returns:
        True if workspace is ready, False otherwise
    """
    global _docker_workspace_validated

    if not _default_ready_predicate(container):
        return False

    # Check that required workspace directories are available
    required_dirs = [
        '/code/workspace',
        '/code/workspace/repo',
        '/code/workspace/build',
        '/code/workspace/cache',
        '/code/workspace/tech',
    ]

    for dir_path in required_dirs:
        try:
            result = container.exec_run(f'test -d {dir_path}')
            if result.exit_code != 0:
                # Get more detailed info about what exists for error reporting
                ls_result = container.exec_run(f'ls -la {posixpath.dirname(dir_path)}')
                error_info = ''
                if ls_result.exit_code == 0:
                    error_info = (
                        f' Contents of {posixpath.dirname(dir_path)}: {ls_result.output.decode("utf-8", errors="replace")}'
                    )
                print(f'Docker workspace validation failed: {dir_path} does not exist.{error_info}')
                return False
        except Exception as e:
            print(f'Docker workspace validation failed for {dir_path}: {e}')
            return False

    # Mark Docker workspace as validated globally
    _docker_workspace_validated = True
    return True


def setup_docker_workspace(
    container: 'docker.models.containers.Container',
    timeout_s: float = 30.0,
    poll_interval_s: float = 0.25,
) -> None:
    """
    Complete Docker container setup with workspace validation.
    This is the single entry point for Docker readiness - once this succeeds,
    the workspace is guaranteed to be available.

    Args:
        container: Docker container to validate
        timeout_s: Maximum time to wait in seconds
        poll_interval_s: How often to check readiness

    Raises:
        ContainerNotReady: If container doesn't become ready within timeout
    """
    assert timeout_s > 0, 'timeout_s must be positive'
    assert poll_interval_s > 0, 'poll_interval_s must be positive'

    deadline = time.monotonic() + timeout_s
    last_err: Optional[str] = None

    while time.monotonic() < deadline:
        try:
            if _validate_docker_workspace(container):
                return
        except Exception as e:  # validation may raise while container initializes
            last_err = repr(e)
        # small jitter to avoid thundering herd and align with healthcheck interval
        time.sleep(poll_interval_s + random.uniform(0, poll_interval_s * 0.2))

    # On failure, include brief state snapshot for diagnostics
    container.reload()
    state = container.attrs.get('State', {})

    # Get container logs for debugging
    logs = ''
    try:
        logs = container.logs(tail=20).decode('utf-8', errors='replace')
    except Exception:
        pass

    raise ContainerNotReady(
        f'Docker workspace not ready within {timeout_s:.1f}s. '
        f'Status={state.get("Status")}, Health={state.get("Health", {}).get("Status")}, '
        f'Last error={last_err}. Container logs: {logs}'
    )


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
        # print(f'🔍 MOUNT VALIDATION: {host_path} -> {abs_path}')
        # print(f'🔍 HAGENT ROOT: {hagent_root}')

        # Check if we're trying to mount the hagent repo root
        if abs_path == hagent_root:
            error_msg = (
                f'\n'
                f'🚨🚨🚨 CRITICAL SAFETY ERROR 🚨🚨🚨\n'
                f'Cannot mount hagent repository root directory!\n'
                f'This would overwrite the hagent source code.\n'
                f'Path: {abs_path}\n'
                f'🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨\n'
            )
            print(error_msg)
            return False, error_msg

        # Check if we're trying to mount a directory inside the hagent repository
        if abs_path.startswith(hagent_root + os.sep):
            relative_path = os.path.relpath(abs_path, hagent_root)
            path_parts = relative_path.split(os.sep)

            # Only reject if it's a direct child of hagent root (one level under)
            # BUT allow if the directory name contains "tmp" for testing purposes
            if len(path_parts) == 1:
                directory_name = path_parts[0]
                if 'tmp' in directory_name.lower():
                    # Allow mounting directories with "tmp" in the name for testing
                    # print(f'✅ ALLOWING TMP DIRECTORY MOUNT: {relative_path} -> {abs_path}')
                    return True, ''

                error_msg = (
                    f'\n'
                    f'🚨🚨🚨 CRITICAL SAFETY ERROR 🚨🚨🚨\n'
                    f'Cannot mount top-level hagent directory!\n'
                    f'This would overwrite hagent source code.\n'
                    f'Directory: {relative_path}\n'
                    f'Full path: {abs_path}\n'
                    f'Hint: Use a directory name containing "tmp" for testing purposes.\n'
                    f'🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨🚨\n'
                )
                print(error_msg)
                return False, error_msg

            # Allow mounting subdirectories (2+ levels deep)
            # print(f'✅ ALLOWING SUBDIRECTORY MOUNT: {relative_path} -> {abs_path}')
            return True, ''

        # Allow mounting directories outside the hagent repo entirely
        # print(f'✅ ALLOWING EXTERNAL MOUNT: {abs_path}')
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

    def __init__(self, image: str):
        """
        Initialize ContainerManager.

        Args:
            image: Docker image name to use
        """
        global _cleanup_registered, _container_manager_registry

        self.image = image
        self.path_manager = PathManager()
        self.client: Optional[docker.DockerClient] = None
        self.container: Optional[docker.models.containers.Container] = None
        self._reference_container: Optional[docker.models.containers.Container] = None
        self._has_bash: bool = False
        self._checkpoints: List[str] = []
        self._workdir = '/code/workspace/repo'  # New default working directory
        self.error_message: str = ''  # For error handling like Tool pattern
        self._cleaned_up = False  # Track cleanup state

        # Register this instance for cleanup
        _container_manager_registry.add(self)

        # Register global cleanup function once (atexit + signals)
        if not _cleanup_registered:
            atexit.register(_cleanup_all_containers)

            # Best-effort early cleanup on termination signals
            def _sig_cleanup_handler(signum, frame):
                try:
                    _cleanup_all_containers()
                finally:
                    # Re-raise default behavior
                    signal.signal(signum, signal.SIG_DFL)
                    os.kill(os.getpid(), signum)

            for _sig in (signal.SIGINT, signal.SIGTERM):
                try:
                    signal.signal(_sig, _sig_cleanup_handler)
                except Exception:
                    pass
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

    def _get_docker_info(self) -> Dict[str, str]:
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

    def _get_image_config(self) -> Dict[str, Any]:
        """Get the original image configuration including command and entrypoint."""
        try:
            if not self.client:
                return {}
            image_info = self.client.images.get(self.image)
            return image_info.attrs.get('Config', {})
        except Exception:
            return {}

    def _get_container_labels(self) -> Dict[str, str]:
        """Labels to tag containers for session-scoped cleanup."""
        labels = _get_process_labels()
        labels['hagent.image'] = self.image
        return labels

    def _setup_docker_workspace_if_needed(self, timeout: int = 30) -> bool:
        """
        Setup Docker workspace if running in Docker mode.
        This is the single point where Docker workspace validation happens.

        Args:
            timeout: Maximum seconds to wait for workspace setup

        Returns:
            True if workspace is ready (or not needed), False on error
        """
        if not is_docker_mode():
            return True

        if is_docker_workspace_ready():
            return True

        try:
            setup_docker_workspace(container=self.container, timeout_s=float(timeout), poll_interval_s=0.1)
            return True
        except ContainerNotReady as e:
            self.set_error(str(e))
            return False

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

        # Define mount points: (target, path_manager_attr, required)
        mounts_config = [
            ('/code/workspace/cache', 'cache_dir', True),
            ('/code/workspace/repo', 'repo_dir', False),
            ('/code/workspace/build', 'build_dir', False),
            ('/code/workspace/tech', 'tech_dir', False),
        ]

        for target, attr_name, required in mounts_config:
            try:
                host_path = str(getattr(self.path_manager, attr_name))
            except (AttributeError, TypeError) as e:
                if required:
                    self.set_error(f'{attr_name} not available: {e}')
                    return []
                continue  # Optional mount not available

            # Skip if it's already a container path (we're running inside a container)
            if host_path.startswith('/code/workspace/'):
                continue

            # Validate the mount path for safety
            is_valid, error_msg = _validate_mount_path(host_path)
            if not is_valid:
                self.set_error(f'{attr_name} mount validation failed: {error_msg}')
                return []

            # Ensure directory exists and resolve symlinks (important on macOS)
            os.makedirs(host_path, exist_ok=True)
            resolved_path = os.path.realpath(host_path)

            # Create and add mount
            mount = docker.types.Mount(target=target, source=resolved_path, type='bind')
            mount_objs.append(mount)

        return mount_objs

    def _fix_mounted_directory_permissions(self) -> bool:
        """
        Fix permissions on mounted directories to allow container user to write.
        Since we're running as root, this is simplified.
        """
        try:
            # List of mounted directories that need permission fixes
            mount_points = ['/code/workspace/repo', '/code/workspace/build', '/code/workspace/cache', '/code/workspace/tech']

            for mount_point in mount_points:
                # Check if the mount point exists
                result = self.container.exec_run(f'test -d {mount_point}')
                if result.exit_code == 0:
                    # Ensure directory is writable (running as root so this should work)
                    result = self.container.exec_run(f'chmod 755 {mount_point}')
                    if result.exit_code != 0:
                        print(f'Warning: Could not fix permissions for {mount_point}')

            return True

        except Exception as e:
            self.set_error(f'Failed to fix mounted directory permissions: {e}')
            return False

    def setup(self) -> bool:
        """
        Create and start Docker container with new mount structure.
        Working directory is always /code/workspace/repo.

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
            # if automount:
            mount_objs = self._setup_mount_points()
            # else:
            #     mount_objs = []

            # Create the container with security restrictions
            # Run as root consistently for simplified permission handling
            self.container = self.client.containers.create(
                self.image,
                command='tail -f /dev/null',  # Keep container running
                mounts=mount_objs,
                working_dir=self._workdir,
                detach=True,
                user='root',  # Always use root
                # Security options to prevent privilege escalation
                security_opt=self._get_security_options(),
                # Drop dangerous capabilities
                cap_drop=['NET_ADMIN', 'NET_RAW', 'SYS_ADMIN', 'SYS_TIME', 'SYS_MODULE'],
                # Prevent new privileges after initial setup
                read_only=False,  # We need write access to mounted volumes
                # Auto-remove container when it exits to prevent accumulation
                auto_remove=True,
                # Labels to identify and clean up containers for this session
                labels=self._get_container_labels(),
            )
            self.container.start()

            # Setup Docker workspace if needed (includes all validation)
            if not self._setup_docker_workspace_if_needed(timeout=30):
                return False

            # Ensure working directory exists
            result = self.container.exec_run(f'mkdir -p {self._workdir}')
            if result.exit_code != 0:
                self.set_error(f'Failed to create working directory: {self._workdir}')
                return False

            # Fix permissions for mounted directories to match container user (only if automount is enabled)
            # if automount and not self._fix_mounted_directory_permissions():
            #     return False

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

    def run_cmd(
        self,
        command: str,
        cwd: Optional[str] = '.',
        quiet: bool = False,
        config_sources: Optional[List[str]] = None,
        skip_profile: bool = False,
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
        if cwd == '.':
            workdir = self._workdir
        else:
            if not posixpath.isabs(cwd):
                workdir = posixpath.join(self._workdir, cwd)
            else:
                workdir = cwd

            # Validate that the container path exists
            if not self._validate_container_path(workdir):
                error_msg = f'Directory does not exist in container: {workdir}'
                self.set_error(error_msg)
                return -1, '', error_msg

        try:
            # Build the command with optional environment sourcing
            if skip_profile:
                # Skip profile sourcing for performance-critical simple commands
                final_command = command
            else:
                # Always attempt to source common profile files to make tool shims (e.g., sbt via coursier/sdkman) available.
                default_sources = [
                    '/etc/profile',
                    '~/.bash_profile',
                    '~/.profile',
                    '~/.bashrc',
                    '~/.sdkman/bin/sdkman-init.sh',
                ]

                # Merge user-provided sources (if any), preserving order and uniqueness
                merged_sources: List[str] = []
                for src in (config_sources or []) + default_sources:
                    if src not in merged_sources:
                        merged_sources.append(src)

                source_cmds = [f'source {s} 2>/dev/null || true' for s in merged_sources]
                prologue = '; '.join(source_cmds)

                final_command = f'{prologue}; {command}'
            if self._has_bash:
                shell_command = ['/bin/bash', '--login', '-c', final_command]
            else:
                shell_command = ['/bin/sh', '-c', final_command]

            if quiet:
                # Capture all output - don't use demux for better performance
                result = self.container.exec_run(shell_command, workdir=workdir, demux=False)
                exit_code = result.exit_code
                output = result.output
                output_str = output.decode('utf-8', 'replace') if output else ''
                # Return combined output as both stdout and stderr for compatibility
                return exit_code, output_str, ''
            else:
                # Stream output in real-time
                exec_create_kwargs = {
                    'container': self.container.id,
                    'cmd': shell_command,
                    'workdir': workdir,
                    'stdout': True,
                    'stderr': True,
                }

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
                self.container.reload()
                if getattr(self.container, 'status', None) == 'running':
                    self.container.kill()
                self.container.remove(force=True)
                self.container = None
            except docker.errors.APIError:
                pass
            except Exception:
                pass

        # Clean up reference container
        if self._reference_container:
            try:
                self._reference_container.reload()
                if getattr(self._reference_container, 'status', None) == 'running':
                    self._reference_container.kill()
                self._reference_container.remove(force=True)
                self._reference_container = None
            except docker.errors.APIError:
                pass
            except Exception:
                pass

        # Clean up anonymous checkpoints
        self._cleanup_anonymous_checkpoints()

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
        if not posixpath.isabs(new_workdir):
            target_workdir = posixpath.join('/code/workspace/repo', new_workdir)
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

    def get_cwd(self) -> str:
        """
        Get the current working directory.

        Returns:
            Current working directory path
        """
        return self._workdir

    def _ensure_container_directory(self, dir_path: str) -> bool:
        """Ensure a directory exists in the container."""
        try:
            # Create directory if it doesn't exist
            result = self.container.exec_run(f'mkdir -p {dir_path}')
            return result.exit_code == 0
        except Exception as e:
            print(f"Failed to create directory '{dir_path}': {e}", file=sys.stderr)
            return False

    def create_file(self, container_path: str, content: Any, mode: int = 0o644) -> bool:
        """Create or overwrite a file inside the container.

        Args:
            container_path: Absolute path inside the container where the file will be written.
            content: File contents as str or bytes.
            mode: File permissions (default 0644).

        Returns:
            True on success, False otherwise with error populated via set_error.
        """
        if not self.container:
            self.set_error('Container not set up. Call setup() first.')
            return False

        if not container_path:
            self.set_error('No container path provided for create_file')
            return False

        try:
            data = content.encode('utf-8') if isinstance(content, str) else bytes(content)
        except Exception as encode_error:
            self.set_error(f'Failed to serialize file content: {encode_error}')
            return False

        container_dir = posixpath.dirname(container_path) or '.'
        filename = posixpath.basename(container_path)

        if not self._ensure_container_directory(container_dir):
            self.set_error(f'Failed to ensure directory exists: {container_dir}')
            return False

        tar_buffer = io.BytesIO()
        try:
            with tarfile.open(fileobj=tar_buffer, mode='w') as tar:
                tar_info = tarfile.TarInfo(name=filename)
                tar_info.size = len(data)
                tar_info.mode = mode
                tar_info.mtime = int(time.time())
                tar.addfile(tar_info, io.BytesIO(data))

            tar_buffer.seek(0)
            success = self.container.put_archive(container_dir, tar_buffer.getvalue())
            if not success:
                self.set_error(f'Failed to write file to container: {container_path}')
                return False

            self.set_error('')
            return True
        except Exception as e:
            self.set_error(f'Failed to create file {container_path}: {e}')
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
    global _container_manager_registry, _cleanup_running

    if _cleanup_running:
        return
    _cleanup_running = True

    # 1) Clean up any remaining container managers (best-effort)
    try:
        managers_to_cleanup = list(_container_manager_registry)
        if managers_to_cleanup:
            # print(f'\n⚠️  atexit: Cleaning up {len(managers_to_cleanup)} remaining ContainerManager instances...')

            for manager in managers_to_cleanup:
                try:
                    if hasattr(manager, 'cleanup') and not getattr(manager, '_cleaned_up', False):
                        manager.cleanup()
                except Exception:
                    pass
    except Exception:
        pass

    # 2) Additionally, clean up any containers labeled with this session ID
    try:
        client = None
        try:
            client = docker.from_env()
        except Exception:
            # Try common sockets as fallback
            for sock in ('/var/run/docker.sock', os.path.expanduser('~/.docker/run/docker.sock')):
                try:
                    if os.path.exists(sock):
                        client = docker.DockerClient(base_url=f'unix://{sock}')
                        break
                except Exception:
                    continue
        if client is None:
            return

        # Find containers belonging to this session
        flt = {'label': [f'{_MANAGED_LABEL_KEY}=true', f'{_SESSION_LABEL_KEY}={_SESSION_ID}']}
        containers = client.containers.list(all=True, filters=flt)
        if containers:
            print(f'⚠️  atexit: Removing {len(containers)} hagent containers for session {_SESSION_ID}...')
        for c in containers:
            try:
                try:
                    c.reload()
                except Exception:
                    pass
                status = getattr(c, 'status', None)
                if status == 'running':
                    try:
                        c.kill()
                    except Exception:
                        pass
                try:
                    c.remove(force=True)
                except Exception:
                    pass
            except Exception:
                pass
    except Exception:
        pass

    _cleanup_running = False


def _get_process_labels() -> Dict[str, str]:
    return {
        _MANAGED_LABEL_KEY: 'true',
        _SESSION_LABEL_KEY: _SESSION_ID,
        _OWNER_PID_LABEL_KEY: str(os.getpid()),
    }


def _merge_labels(base: Optional[Dict[str, str]], extra: Dict[str, str]) -> Dict[str, str]:
    merged = dict(base) if base else {}
    merged.update(extra)
    return merged


def _safe_getattr(obj: Any, name: str, default: Any = None) -> Any:
    try:
        return getattr(obj, name)
    except Exception:
        return default


def _safe_dict_get(d: Optional[Dict[str, Any]], key: str, default: Any = None) -> Any:
    try:
        return (d or {}).get(key, default)
    except Exception:
        return default
