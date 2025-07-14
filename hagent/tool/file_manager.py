import docker
import platform
import os
import tarfile
import io
import difflib
import tempfile
import shutil
from datetime import datetime
from typing import Optional, List, Dict, Tuple, Any

from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString


# YAML helper function to format multiline strings correctly
def process_multiline_strings(obj):
    """
    Recursively converts strings containing newlines into a LiteralScalarString
    so that ruamel.yaml outputs them in literal block style.
    """
    if isinstance(obj, dict):
        return {k: process_multiline_strings(v) for k, v in obj.items()}
    elif isinstance(obj, list):
        return [process_multiline_strings(item) for item in obj]
    elif isinstance(obj, str) and '\n' in obj and obj.strip():
        return LiteralScalarString(obj)
    return obj


class File_manager:
    """
    Wrapper to manage docker setups, tracks file state within a container,
    and exports/imports patches as unified diffs in YAML.
    """

    # Class-level container cache for reuse
    _container_cache: Dict[str, Any] = {}

    def __init__(self, image: str, reuse_container: bool = True) -> None:
        """
        Create a new class with the docker image.
        Verify docker is available, and that the user has permission to run the docker.

        Initializes internal state; does not create the container yet.

        The object destruction or termination should clear the docker.
        """
        self.image = image
        self.reuse_container = reuse_container
        self.error_message = ''
        self._state = 'INITIALIZED'
        self._workdir = '/code/rundir'  # Default working directory inside the container

        self.client: Optional[docker.DockerClient] = None
        self.container: Optional[docker.models.containers.Container] = None

        self._mounts: List[Dict[str, str]] = []
        self._tracked_files: Dict[str, bytes] = {}  # For copy_file tracked files
        self._tracked_paths: set = set()  # For track_file tracked paths (new approach)
        self._tracking_extensions: List[str] = []
        self._reference_container: Optional[docker.models.containers.Container] = None
        self._image_user: Optional[str] = None  # Cache for image's default user

        # Initialize Docker client with cross-platform support
        self._initialize_docker_client()
    
    @property
    def workdir(self) -> str:
        """Get the current working directory path inside the container."""
        return self._workdir
    
    def _resolve_container_path(self, path: str) -> str:
        """Resolve a path relative to _workdir unless it's absolute."""
        if os.path.isabs(path):
            return path
        return os.path.join(self._workdir, path)
    
    def _check_file_exists(self, container_path: str) -> bool:
        """Check if a file exists in the container."""
        full_path = self._resolve_container_path(container_path)
        try:
            exit_code, _, _ = self.run(f'test -f "{full_path}"', quiet=True)
            return exit_code == 0
        except Exception:
            return False

    def _get_image_user(self) -> Optional[str]:
        """Get the default user from the Docker image."""
        if self._image_user is not None:
            return self._image_user  # Return cached value (could be empty string)
        
        try:
            if not self.client:
                return None
            image_info = self.client.images.get(self.image)
            config = image_info.attrs.get('Config', {})
            user = config.get('User')
            self._image_user = user if user else ''  # Cache empty string for no user
            return user
        except Exception:
            self._image_user = ''  # Cache that we failed to get user info
            return None

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
        self.error_message = (
            f'Docker client initialization failed. Tried:\n'
            f'- Environment-based connection\n'
            f'- Socket paths: {socket_paths}\n'
            f'Please ensure Docker is running and accessible.\n'
            f'Original error: {first_error if first_error else "Unknown"}'
        )
        self._state = 'ERROR'

    def _pull_image_with_progress(self, image: str) -> None:
        """
        Pull Docker image with a simple progress indicator.
        Shows a spinning progress indicator while the pull is in progress.
        """
        import sys
        import time
        import threading

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

    def get_docker_info(self) -> Dict[str, str]:
        """
        Get information about the Docker connection for debugging.
        """
        if self.client is None:
            return {'status': 'ERROR', 'message': self.error_message}

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

    def __del__(self) -> None:
        """On destruction, ensures the created docker container is stopped and removed."""
        if self.container and not self.reuse_container:
            try:
                self.container.stop()
                self.container.remove()
            except docker.errors.APIError:
                # Ignore errors on cleanup, e.g., if container was already removed.
                pass

        # Clean up reference container
        self._cleanup_reference_container()

    @classmethod
    def cleanup_all_containers(cls) -> None:
        """Cleanup all cached containers. Call this at the end of test sessions."""
        for container_key, container_info in cls._container_cache.items():
            try:
                container = container_info['container']
                container.stop()
                container.remove()
                print(f'Cleaned up cached container for {container_key}')
            except Exception as e:
                print(f'Error cleaning up container {container_key}: {e}')
        cls._container_cache.clear()

    def _ensure_workdir_exists(self) -> bool:
        """Ensure the working directory exists in the container."""
        try:
            result = self.container.exec_run(f'mkdir -p {self._workdir}')
            return result.exit_code == 0
        except Exception as e:
            self.error_message = f'Failed to create working directory: {e}'
            return False

    def setup(self) -> bool:
        """
        If a docker container was already configured, this clears it and allows for a new setup.
        Downloads (docker pull equivalent) and creates, but does not start, a docker container.
        """
        if self._state == 'ERROR':
            return False

        # Generate cache key based on image and mounts
        cache_key = f'{self.image}:{hash(tuple(sorted(self._mounts, key=lambda x: x["target"])))}'

        # Try to reuse cached container if enabled
        if self.reuse_container and cache_key in self._container_cache:
            cached_info = self._container_cache[cache_key]
            try:
                # Check if cached container is still running
                cached_container = cached_info['container']
                cached_container.reload()
                if cached_container.status == 'running':
                    self.container = cached_container
                    self._state = 'CONFIGURED'
                    print(f"Reusing cached container for '{self.image}'")
                    # Reset tracked files for this instance
                    self._tracked_files = {}
                    return True
                else:
                    # Container stopped, remove from cache
                    del self._container_cache[cache_key]
            except Exception as e:
                print(f'Cached container unusable, creating new one: {e}')
                if cache_key in self._container_cache:
                    del self._container_cache[cache_key]

        # Clean up existing container if not reusing
        if self.container and not self.reuse_container:
            self.__del__()
            self._tracked_files = {}  # Reset tracked files

        try:
            # Skip image pull message for better performance
            image_available = False

            # First, check if image exists locally (skip pulling)
            try:
                self.client.images.get(self.image)
                image_available = True
            except docker.errors.ImageNotFound:
                pass

            # Only pull if image doesn't exist locally
            if not image_available:
                print(f"Pulling image '{self.image}'...")
                try:
                    # Pull image with progress tracking
                    self._pull_image_with_progress(self.image)
                    image_available = True
                except docker.errors.APIError as e:
                    error_msg = str(e).lower()
                    if 'credential' in error_msg or 'unauthorized' in error_msg:
                        print(f'Warning: Credential issue detected: {e}')
                        print(f'Please manually pull the image: docker pull {self.image}')
                        print('Or fix Docker credentials configuration.')
                        return False
                    else:
                        print(f'Failed to pull image: {e}')
                        return False

            if not image_available:
                self.error_message = f"Image '{self.image}' is not available"
                return False

            mount_objs = [
                docker.types.Mount(target=m['target'], source=os.path.abspath(m['source']), type='bind') for m in self._mounts
            ]

            # Create the container but keep it alive with a do-nothing command
            self.container = self.client.containers.create(
                self.image,
                command='tail -f /dev/null',  # Keeps container running
                mounts=mount_objs,
                working_dir=self._workdir,
                detach=True,
            )
            self.container.start()

            # Ensure working directory exists (Alpine might not have /code/rundir by default)
            if not self._ensure_workdir_exists():
                return False

            # Cache the container if reuse is enabled
            if self.reuse_container:
                self._container_cache[cache_key] = {
                    'container': self.container,
                    'image': self.image,
                    'mounts': self._mounts.copy(),
                }

            self._state = 'CONFIGURED'
            return True
        except Exception as e:
            self.error_message = f'Setup failed: {e}'
            self._state = 'ERROR'
            return False

    def add_mount(self, host_path: str, container_path: str) -> bool:
        """Registers a directory to be mounted from the host. Must be called before setup()."""
        if self._state != 'INITIALIZED':
            self.error_message = 'add_mount must be called before setup().'
            return False

        full_container_path = container_path if os.path.isabs(container_path) else os.path.join(self._workdir, container_path)
        self._mounts.append({'source': host_path, 'target': full_container_path})
        return True

    def copy_dir(self, host_path: str, container_path: str = '.', ext: Optional[str] = None) -> bool:
        """Copies a host directory into the container. Must be called after setup()."""
        if self._state != 'CONFIGURED':
            self.error_message = 'copy_dir must be called after setup() and before run().'
            return False
        try:
            for root, _, files in os.walk(host_path):
                for file in files:
                    if ext and not file.endswith(ext):
                        continue

                    local_file_path = os.path.join(root, file)
                    relative_path = os.path.relpath(local_file_path, host_path)
                    dest_path = os.path.join(container_path, relative_path)

                    if not self.copy_file(local_file_path, dest_path):
                        return False
            return True
        except Exception as e:
            self.error_message = f"Failed to copy directory '{host_path}': {e}"
            return False

    def copy_file(self, host_path: str, container_path: Optional[str] = '.') -> bool:
        """Copies a single file from the host into the container's tracked directory."""
        if self._state != 'CONFIGURED':
            self.error_message = 'copy_file must be called after setup() and before run().'
            return False

        try:
            # Read the file content from host
            with open(host_path, 'rb') as f:
                file_content = f.read()

            filename = os.path.basename(host_path)

            # Determine the destination path in container
            if container_path == '.':
                # Copy to working directory with same filename
                dest_path = self._workdir
                final_container_path = filename
            elif container_path.endswith('/') or not os.path.splitext(container_path)[1]:
                # container_path is a directory
                dest_path = os.path.join(self._workdir, container_path.rstrip('/'))
                final_container_path = os.path.join(container_path.rstrip('/'), filename)
            else:
                # container_path includes filename
                dest_path = os.path.join(self._workdir, os.path.dirname(container_path))
                final_container_path = container_path
                filename = os.path.basename(container_path)

            # Create tar archive in memory
            tar_stream = io.BytesIO()
            tar = tarfile.open(fileobj=tar_stream, mode='w')

            # Add file to tar
            tarinfo = tarfile.TarInfo(name=filename)
            tarinfo.size = len(file_content)
            tarinfo.mode = 0o644
            tar.addfile(tarinfo, io.BytesIO(file_content))
            tar.close()

            # Reset stream position
            tar_stream.seek(0)

            # Ensure the destination directory exists
            if dest_path != self._workdir:
                self._ensure_container_directory(dest_path)

            # Copy to container using put_archive
            success = self.container.put_archive(path=dest_path, data=tar_stream.getvalue())

            if success:
                # Track file content for diffing
                self._tracked_files[final_container_path] = file_content
                print(f"Successfully copied '{host_path}' to container path '{final_container_path}'")
                return True
            else:
                self.error_message = f"Failed to copy file '{host_path}' to container"
                return False

        except Exception as e:
            self.error_message = f"Failed to copy file '{host_path}': {e}"
            return False

    def _ensure_container_directory(self, dir_path: str) -> bool:
        """Ensure a directory exists in the container."""
        try:
            # Create directory if it doesn't exist
            result = self.container.exec_run(f'mkdir -p {dir_path}')
            return result.exit_code == 0
        except Exception as e:
            self.error_message = f"Failed to create directory '{dir_path}': {e}"
            return False

    def _ensure_temp_dir(self) -> bool:
        """Ensure temporary directory exists for tracking files."""
        if self._temp_dir is None:
            try:
                self._temp_dir = tempfile.mkdtemp(prefix='file_manager_')
                return True
            except Exception as e:
                self.error_message = f'Failed to create temporary directory: {e}'
                return False
        return True

    def _get_reference_container(self) -> Optional[docker.models.containers.Container]:
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
                self.error_message = f'Failed to create reference container: {e}'
                return None
        return self._reference_container
    
    def _cleanup_reference_container(self) -> None:
        """Clean up reference container."""
        if self._reference_container:
            try:
                self._reference_container.stop()
                self._reference_container.remove()
                self._reference_container = None
            except Exception as e:
                print(f'Warning: Failed to clean up reference container: {e}')

    def _copy_file_from_container(self, container_path: str, temp_file_path: str) -> bool:
        """Copy a file from container to temporary location on host."""
        try:
            full_path = self._resolve_container_path(container_path)
            bits, stat = self.container.get_archive(full_path)

            with io.BytesIO() as bio:
                for chunk in bits:
                    bio.write(chunk)
                bio.seek(0)
                with tarfile.open(fileobj=bio, mode='r') as tar:
                    member = tar.getmembers()[0]
                    extracted_file = tar.extractfile(member)

                    # Write to temporary file
                    with open(temp_file_path, 'wb') as temp_file:
                        shutil.copyfileobj(extracted_file, temp_file)

            return True
        except Exception as e:
            self.error_message = f'Failed to copy file from container: {e}'
            return False

    def run(self, command: str, container_path: Optional[str] = '.', quiet: bool = False) -> Tuple[int, str, str]:
        """Execute command inside the container."""
        # Allow running in both CONFIGURED and EXECUTED states
        if self._state not in ['CONFIGURED', 'EXECUTED']:
            self.error_message = 'run must be called after setup().'
            return -1, '', self.error_message

        # Set state to EXECUTED after first successful setup
        if self._state == 'CONFIGURED':
            self._state = 'EXECUTED'

        # Handle working directory
        if container_path == '.':
            workdir = self._workdir
        else:
            # If container_path is relative, join with workdir
            if not os.path.isabs(container_path):
                workdir = os.path.join(self._workdir, container_path)
            else:
                workdir = container_path

        try:
            # Source profile to get proper PATH setup (includes oss-cad-suite tools)
            wrapped_command = f'source /etc/profile 2>/dev/null || true; {command}'
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
                    'stderr': True
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
                                print(f"{self.image.split('/')[-1]}:run: {clean_chunk}")
                    
                    if stderr_chunk:
                        chunk_str = stderr_chunk.decode('utf-8', 'replace')
                        stderr_lines.append(chunk_str)
                        # Print chunk directly without splitting into lines to preserve formatting
                        if chunk_str.strip():
                            # Remove trailing newline to avoid double newlines
                            clean_chunk = chunk_str.rstrip('\n')
                            if clean_chunk:
                                print(f"{self.image.split('/')[-1]}:run: {clean_chunk}")
                
                # Get the exit code after streaming completes
                exec_inspect = self.client.api.exec_inspect(exec_id)
                exit_code = exec_inspect.get('ExitCode', 0)
                if exit_code is None:
                    exit_code = 0  # Default to 0 if None
                
                stdout_str = ''.join(stdout_lines)
                stderr_str = ''.join(stderr_lines)
                
                return exit_code, stdout_str, stderr_str

        except Exception as e:
            self.error_message = f'Command execution failed: {e}'
            return -1, '', str(e)

    def track_file(self, container_path: str) -> bool:
        """Track an existing file in the container for change detection."""
        if self._state not in ['CONFIGURED', 'EXECUTED']:
            self.error_message = 'track_file must be called after setup().'
            return False
        
        # Check if file exists
        if not self._check_file_exists(container_path):
            self.error_message = f'File not found: {container_path}'
            return False

        try:
            # Simply record the path for tracking - no file copying needed
            self._tracked_paths.add(container_path)
            print(f"Successfully tracking file '{container_path}' in container")
            return True

        except Exception as e:
            self.error_message = f'Failed to track file {container_path}: {e}'
            return False

    def track_dir(self, container_path: str = '.', ext: Optional[str] = None) -> bool:
        """Track all files in an existing directory in the container for change detection."""
        if self._state not in ['CONFIGURED', 'EXECUTED']:
            self.error_message = 'track_dir must be called after setup().'
            return False

        try:
            # Find all files in the directory
            if container_path == '.':
                find_path = '.'
                search_dir = '.'
            else:
                find_path = container_path
                # Use the resolved path for the search directory
                search_dir = '.' if not os.path.isabs(container_path) else '/'

            exit_code, out, stderr = self.run(f'find {find_path} -type f', container_path=search_dir, quiet=True)
            if exit_code != 0:
                self.error_message = f'Failed to list files in directory {container_path}: {stderr}'
                return False

            files = [f.strip() for f in out.strip().split('\n') if f.strip()]
            tracked_count = 0

            for file_path in files:
                # Clean up the path (remove ./ prefix if present)
                if file_path.startswith('./'):
                    file_path = file_path[2:]

                # Filter by extension if specified
                if ext and not file_path.endswith(ext):
                    continue

                # Track the file
                self._tracked_paths.add(container_path)
                tracked_count += 1

            print(f"Successfully tracking {tracked_count} files in directory '{container_path}'")
            return tracked_count > 0

        except Exception as e:
            self.error_message = f'Failed to track directory {container_path}: {e}'
            return False

    def patch_file(self, container_path: str, patch_content: str) -> bool:
        """Apply a unified diff patch to a file in the container."""
        if self._state not in ['CONFIGURED', 'EXECUTED']:
            self.error_message = 'patch_file must be called after setup().'
            return False

        try:
            # Create a temporary patch file in the container
            temp_patch_path = f'/tmp/patch_{len(self._tracked_files) + len(self._tracked_temp_files)}.patch'

            # Write patch content to temporary file using echo and redirection

            # Write patch to temp file
            exit_code, stdout, stderr = self.run(f"cat > {temp_patch_path} << 'EOF'\n{patch_content}\nEOF")
            if exit_code != 0:
                self.error_message = f'Failed to create patch file: {stderr}'
                return False

            # Apply the patch
            exit_code, stdout, stderr = self.run(f'patch -p1 < {temp_patch_path}', container_path='.')

            # Clean up temporary patch file
            self.run(f'rm -f {temp_patch_path}')

            if exit_code != 0:
                self.error_message = f'Failed to apply patch: {stderr}'
                return False

            print(f"Successfully applied patch to '{container_path}'")
            return True

        except Exception as e:
            self.error_message = f'Failed to patch file {container_path}: {e}'
            return False

    def apply_line_patch(self, container_path: str, line_number: int, old_line: str, new_line: str) -> bool:
        """Apply a simple line replacement patch to a file in the container."""
        if self._state not in ['CONFIGURED', 'EXECUTED']:
            self.error_message = 'apply_line_patch must be called after setup().'
            return False
        
        # Check if file exists
        if not self._check_file_exists(container_path):
            self.error_message = f'File not found: {container_path}'
            return False

        try:
            # Get current file content
            current_content = self.get_file_content(container_path)
            if not current_content and self.error_message:
                return False

            lines = current_content.splitlines()

            # Validate line number
            if line_number < 1 or line_number > len(lines):
                self.error_message = f'Line number {line_number} is out of range (file has {len(lines)} lines)'
                return False

            # Check if the old line matches (with stripped whitespace comparison)
            actual_line = lines[line_number - 1]
            if old_line.strip() != actual_line.strip():
                self.error_message = f'Line {line_number} does not match expected content.\nExpected: "{old_line.strip()}"\nActual: "{actual_line.strip()}"'
                return False

            # Replace the line
            lines[line_number - 1] = new_line
            modified_content = '\n'.join(lines)

            # Write the modified content back to the file
            temp_file_path = f'/tmp/modified_{os.path.basename(container_path)}'

            # Write content to temp file with proper escaping
            exit_code, stdout, stderr = self.run(f"cat > {temp_file_path} << 'EOF'\n{modified_content}\nEOF")
            if exit_code != 0:
                self.error_message = f'Failed to create temporary file: {stderr}'
                return False

            # Move temp file to target location
            full_container_path = self._resolve_container_path(container_path)
            exit_code, stdout, stderr = self.run(f'mv {temp_file_path} {full_container_path}')
            if exit_code != 0:
                self.error_message = f'Failed to replace file: {stderr}'
                return False

            print(f"Successfully patched line {line_number} in '{container_path}'")
            return True

        except Exception as e:
            self.error_message = f'Failed to apply line patch to {container_path}: {e}'
            return False

    def get_file_content(self, container_path: str, container: Optional[docker.models.containers.Container] = None) -> str:
        """Return the text content of a file from a container (defaults to main container)."""
        # Allow getting file content in EXECUTED state (and also CONFIGURED for flexibility)
        if self._state not in ['CONFIGURED', 'EXECUTED']:
            self.error_message = 'get_file_content must be called after setup().'
            return ''

        # Use provided container or default to main container
        target_container = container if container else self.container
        if not target_container:
            self.error_message = 'No container available'
            return ''

        try:
            full_path = self._resolve_container_path(container_path)
            bits, stat = target_container.get_archive(full_path)

            with io.BytesIO() as bio:
                for chunk in bits:
                    bio.write(chunk)
                bio.seek(0)
                with tarfile.open(fileobj=bio, mode='r') as tar:
                    member = tar.getmembers()[0]
                    extracted_file = tar.extractfile(member)
                    content = extracted_file.read()

            try:
                return content.decode('utf-8')
            except UnicodeDecodeError:
                self.error_message = f"File '{container_path}' is binary or has non-UTF-8 content."
                return ''
        except docker.errors.NotFound:
            self.error_message = f'File not found in container: {container_path}'
            return ''
        except Exception as e:
            self.error_message = f'Failed to get file content: {e}'
            return ''

    def get_diff(self, filename: str) -> str:
        """Return the unified diff (as text) for a single tracked file."""
        original_content_str = ''

        # Check if file was tracked via copy_file (in-memory) - legacy support
        if filename in self._tracked_files:
            original_content_bytes = self._tracked_files[filename]
            try:
                original_content_str = original_content_bytes.decode('utf-8')
            except UnicodeDecodeError:
                self.error_message = f"Original file '{filename}' is binary."
                return ''
        # Check if file was tracked via new track_file (path-only)
        elif filename in self._tracked_paths:
            # Get original content from reference container
            reference_container = self._get_reference_container()
            if not reference_container:
                return ''
            original_content_str = self.get_file_content(filename, container=reference_container)
            if not original_content_str and self.error_message:
                return ''
        else:
            self.error_message = f"File '{filename}' was not tracked initially."
            return ''

        # Get modified content from main container
        modified_content_str = self.get_file_content(filename)

        diff_lines = difflib.unified_diff(
            original_content_str.splitlines(keepends=True),
            modified_content_str.splitlines(keepends=True),
            fromfile=f'a/{filename}',
            tofile=f'b/{filename}',
        )
        return ''.join(diff_lines)

    def add_tracking_extension(self, ext: str) -> List[str]:
        """Adds a file extension to the list of types that will be monitored for changes."""
        if ext not in self._tracking_extensions:
            self._tracking_extensions.append(ext)
        return self._tracking_extensions

    def get_patch_dict(self) -> Dict[str, Any]:
        """Generate a dictionary of new files and patched files."""
        if self._state != 'EXECUTED':
            self.error_message = 'get_patch_dict must be called after run().'
            return {}

        patches = {'full': [], 'patch': []}

        # Find all files in the working directory
        exit_code, out, _ = self.run('find . -type f', container_path='.')
        if exit_code != 0:
            return patches

        all_files = [f[2:] for f in out.strip().split('\n') if f]  # Clean ./ prefix

        for file_path in all_files:
            if self._tracking_extensions and not any(file_path.endswith(ext) for ext in self._tracking_extensions):
                continue

            modified_content_str = self.get_file_content(file_path)
            if not modified_content_str and self.error_message:  # Likely binary file
                patches['full'].append({'filename': file_path, 'contents': '[Binary File]'})
                continue

            # Check if file is tracked (legacy copy_file or new track_file)
            is_tracked = file_path in self._tracked_files or file_path in self._tracked_paths

            if not is_tracked:
                # This is a new file
                patches['full'].append({'filename': file_path, 'contents': modified_content_str})
            else:
                # This is a tracked file, create a diff
                diff = self.get_diff(file_path)
                if not diff:  # No changes detected
                    continue

                # Get original file size for comparison
                original_len = 0
                if file_path in self._tracked_files:
                    # Legacy copy_file approach
                    original_len = len(self._tracked_files[file_path])
                elif file_path in self._tracked_paths:
                    # New track_file approach - get size from reference container
                    reference_container = self._get_reference_container()
                    if reference_container:
                        original_content = self.get_file_content(file_path, container=reference_container)
                        original_len = len(original_content.encode('utf-8')) if original_content else 0

                # Add as full if diff is large or file is small
                if original_len == 0 or (len(diff) / original_len > 0.25):
                    patches['full'].append({'filename': file_path, 'contents': modified_content_str})
                else:
                    patches['patch'].append({'filename': file_path, 'diff': diff})

        return patches

    def save_patches(self, host_path: str, name: str) -> bool:
        """Dump current patch-dict to YAML at host_path."""
        patch_dict = self.get_patch_dict()
        if not patch_dict:
            return False

        try:
            yaml = YAML()
            data = {}
            if os.path.exists(host_path):
                with open(host_path, 'r') as f:
                    data = yaml.load(f) or {}

            # Add metadata and process for literal block style
            patch_with_meta = {
                'metadata': {'timestamp': datetime.utcnow().isoformat(), 'image': self.image},
                'patches': process_multiline_strings(patch_dict),
            }
            data[name] = patch_with_meta

            with open(host_path, 'w') as f:
                yaml.dump(data, f)
            return True
        except Exception as e:
            self.error_message = f'Failed to save patches to YAML: {e}'
            return False

    def load_patches(self, host_path: str) -> bool:
        """(Not Implemented) Reads a patch YAML and applies it."""
        self.error_message = 'load_patches is not yet implemented.'
        return False

    def get_error(self) -> str:
        """Return the last recorded error message (empty if none)."""
        return self.error_message
