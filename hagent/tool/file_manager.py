import docker
import platform
import os
import tarfile
import io
import difflib
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
        self._tracked_files: Dict[str, bytes] = {}
        self._tracking_extensions: List[str] = []

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
        self.error_message = (
            f'Docker client initialization failed. Tried:\n'
            f'- Environment-based connection\n'
            f'- Socket paths: {socket_paths}\n'
            f'Please ensure Docker is running and accessible.\n'
            f'Original error: {first_error if first_error else "Unknown"}'
        )
        self._state = 'ERROR'

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
        
    @classmethod
    def cleanup_all_containers(cls) -> None:
        """Cleanup all cached containers. Call this at the end of test sessions."""
        for container_key, container_info in cls._container_cache.items():
            try:
                container = container_info['container']
                container.stop()
                container.remove()
                print(f"Cleaned up cached container for {container_key}")
            except Exception as e:
                print(f"Error cleaning up container {container_key}: {e}")
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
        cache_key = f"{self.image}:{hash(tuple(sorted(self._mounts, key=lambda x: x['target'])))}"
        
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
                print(f"Cached container unusable, creating new one: {e}")
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
                print(f"Pulling image '{self.image}'... This may take a moment.")
                try:
                    self.client.images.pull(self.image)
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
                    'mounts': self._mounts.copy()
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

    def run(self, command: str, container_path: Optional[str] = '.') -> Tuple[int, str, str]:
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

            result = self.container.exec_run(
                shell_command,
                workdir=workdir,
                demux=True
            )

            exit_code = result.exit_code
            stdout, stderr = result.output

            stdout_str = stdout.decode('utf-8', 'replace') if stdout else ''
            stderr_str = stderr.decode('utf-8', 'replace') if stderr else ''

            return exit_code, stdout_str, stderr_str

        except Exception as e:
            self.error_message = f'Command execution failed: {e}'
            return -1, '', str(e)


    def get_file_content(self, container_path: str) -> str:
        """Return the *modified* text content of a file inside the container."""
        # Allow getting file content in EXECUTED state (and also CONFIGURED for flexibility)
        if self._state not in ['CONFIGURED', 'EXECUTED']:
            self.error_message = 'get_file_content must be called after setup().'
            return ''

        try:
            full_path = os.path.join(self._workdir, container_path)
            bits, stat = self.container.get_archive(full_path)

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
        if filename not in self._tracked_files:
            self.error_message = f"File '{filename}' was not tracked initially."
            return ''

        original_content_bytes = self._tracked_files[filename]
        modified_content_str = self.get_file_content(filename)

        try:
            original_content_str = original_content_bytes.decode('utf-8')
        except UnicodeDecodeError:
            self.error_message = f"Original file '{filename}' is binary."
            return ''

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

            if file_path not in self._tracked_files:
                # This is a new file
                patches['full'].append({'filename': file_path, 'contents': modified_content_str})
            else:
                # This is a modified file, create a diff
                diff = self.get_diff(file_path)
                original_len = len(self._tracked_files[file_path])

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
