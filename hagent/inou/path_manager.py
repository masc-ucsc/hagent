"""
Path Manager for HAgent

Consolidates path resolution, environment variable handling, and configuration
file discovery functionality. Replaces functionality from hagent_build.py
and output_manager.py.

Provides centralized management of HAGENT_* environment variables and
path validation with fail-fast error handling.

This is implemented as a singleton to ensure consistent path management
across the entire application.
"""

import os
import sys
from contextlib import contextmanager
from pathlib import Path
from typing import List, Optional


class PathManager:
    """
    Manages all path-related operations for HAgent including environment
    variable validation, path resolution, and cache directory structure.

    Singleton pattern: Only one instance exists per process.
    """

    _instance: Optional['PathManager'] = None
    _initialized: bool = False

    def __new__(cls):
        """
        Singleton pattern implementation.

        Returns:
            The singleton instance of PathManager
        """
        if cls._instance is None:
            cls._instance = super().__new__(cls)
        return cls._instance

    def __init__(self):
        """
        Initialize PathManager singleton.

        Only initializes once - subsequent calls are no-ops.
        Always validates and sets up environment.
        """
        # Only initialize once
        if PathManager._initialized:
            return

        # Initialize attributes to None first (will be set during validation)
        # xxx_dir = internal path (Docker path in Docker mode, local path in local mode)
        # xxx_mount_dir = local mount path (same as xxx_dir in local mode)
        self._repo_dir: Optional[Path] = None
        self._build_dir: Optional[Path] = None
        self._cache_dir: Optional[Path] = None
        self._tech_dir: Optional[Path] = None
        self._private_dir: Optional[Path] = None
        # Mount directories (local paths that get mounted into Docker)
        self._repo_mount_dir: Optional[Path] = None
        self._build_mount_dir: Optional[Path] = None
        self._cache_mount_dir: Optional[Path] = None
        self._tech_mount_dir: Optional[Path] = None
        self._private_mount_dir: Optional[Path] = None
        self._is_docker: Optional[bool] = None

        self._validate_and_setup_environment()

        PathManager._initialized = True

    def _validate_and_setup_environment(self) -> None:
        """
        Validate required HAGENT_* environment variables and setup paths.
        Fails fast with clear error messages if validation fails.

        Execution mode is determined by HAGENT_DOCKER:
        - If HAGENT_DOCKER is set → docker mode
        - If HAGENT_DOCKER is not set → local mode
        """
        # Determine execution mode based on HAGENT_DOCKER
        self._is_docker = bool(os.environ.get('HAGENT_DOCKER'))
        if self._is_docker:
            self._validate_docker_mode()
        else:
            self._validate_local_mode()

        # Create cache directory structure
        self._create_cache_structure()

    def _validate_local_mode(self) -> None:
        """Validate environment variables for local execution mode.

        In local mode, xxx_dir and xxx_mount_dir are the same (local paths).
        """
        missing_vars = []

        repo_dir = os.environ.get('HAGENT_REPO_DIR')
        if not repo_dir:
            missing_vars.append('HAGENT_REPO_DIR')
        else:
            self._repo_dir = Path(repo_dir).resolve()
            self._repo_mount_dir = self._repo_dir  # Same in local mode
            if not self._repo_dir.exists():
                self._fail_fast(f'HAGENT_REPO_DIR path does not exist: {self._repo_dir}')
                return  # Should not reach here in normal execution, but helps in tests

        build_dir = os.environ.get('HAGENT_BUILD_DIR')
        if not build_dir:
            missing_vars.append('HAGENT_BUILD_DIR')
        else:
            self._build_dir = Path(build_dir).resolve()
            self._build_mount_dir = self._build_dir  # Same in local mode

        cache_dir = os.environ.get('HAGENT_CACHE_DIR')
        if not cache_dir:
            missing_vars.append('HAGENT_CACHE_DIR')
        else:
            self._cache_dir = Path(cache_dir).resolve()
            self._cache_mount_dir = self._cache_dir  # Same in local mode

        # Tech dir - use cache_dir/tech as default if not specified
        tech_dir = os.environ.get('HAGENT_TECH_DIR')
        if tech_dir:
            self._tech_dir = Path(tech_dir).resolve()
        elif cache_dir:
            # Default to cache_dir/tech if cache_dir is set
            self._tech_dir = Path(cache_dir).resolve() / 'tech'
        else:
            # Will be set to a default after validation completes
            self._tech_dir = Path('/tmp/tech')
        self._tech_mount_dir = self._tech_dir  # Same in local mode

        # Private dir - optional, not required
        private_dir = os.environ.get('HAGENT_PRIVATE_DIR')
        if private_dir:
            self._private_dir = Path(private_dir).resolve()
            self._private_mount_dir = self._private_dir  # Same in local mode
            if not self._private_dir.exists():
                self._fail_fast(f'HAGENT_PRIVATE_DIR path does not exist: {self._private_dir}')
                return

        if missing_vars:
            self._fail_fast(
                f'Local execution mode requires these environment variables: {", ".join(missing_vars)}\n'
                'All HAGENT_* variables must be set for local mode.'
            )
            return  # Should not reach here in normal execution, but helps in tests

    def _validate_docker_mode(self) -> None:
        """Validate environment variables for Docker execution mode.

        In Docker mode:
        - xxx_dir = Docker container path (/code/workspace/xxx)
        - xxx_mount_dir = local host path (from HAGENT_XXX_DIR, or None if not set)
        """
        # In Docker mode, only HAGENT_DOCKER is required from user
        # Other variables are optional - if provided, they will be mounted as host directories
        # If not provided, use default container paths

        # Check for host directory mounts (optional)
        if os.environ.get('HAGENT_REPO_DIR'):
            self._repo_mount_dir = Path(os.environ['HAGENT_REPO_DIR']).resolve()
            if not self._repo_mount_dir.exists():
                self._fail_fast(f'HAGENT_REPO_DIR path does not exist: {self._repo_mount_dir}')
                return
        else:
            self._repo_mount_dir = None
        # Docker container path
        self._repo_dir = Path('/code/workspace/repo')

        if os.environ.get('HAGENT_BUILD_DIR'):
            self._build_mount_dir = Path(os.environ['HAGENT_BUILD_DIR']).resolve()
        else:
            self._build_mount_dir = None
        # Docker container path
        self._build_dir = Path('/code/workspace/build')

        if os.environ.get('HAGENT_CACHE_DIR'):
            self._cache_mount_dir = Path(os.environ['HAGENT_CACHE_DIR']).resolve()
        else:
            self._cache_mount_dir = None
        # Docker container path
        self._cache_dir = Path('/code/workspace/cache')

        if os.environ.get('HAGENT_TECH_DIR'):
            self._tech_mount_dir = Path(os.environ['HAGENT_TECH_DIR']).resolve()
        else:
            self._tech_mount_dir = None
        # Docker container path
        self._tech_dir = Path('/code/workspace/tech')

        # Private dir - optional, only set if explicitly provided
        if os.environ.get('HAGENT_PRIVATE_DIR'):
            self._private_mount_dir = Path(os.environ['HAGENT_PRIVATE_DIR']).resolve()
            self._private_dir = Path('/code/workspace/private')
            if not self._private_mount_dir.exists():
                self._fail_fast(f'HAGENT_PRIVATE_DIR path does not exist: {self._private_mount_dir}')
                return
        else:
            self._private_mount_dir = None
            self._private_dir = None
        # Note: Do not set a default value - private_dir remains None if not provided

    def _create_cache_structure(self) -> None:
        """Create the HAGENT_CACHE_DIR directory structure on the local filesystem.

        Uses cache_mount_dir (local path) since we need to create directories locally.
        """
        # Use mount_dir for local filesystem operations
        cache_local = self._cache_mount_dir if self._cache_mount_dir else self._cache_dir
        if not cache_local:
            return

        # Skip cache creation for container paths (they don't exist on the host)
        if str(cache_local).startswith('/code/workspace/'):
            return

        try:
            # Create main directories
            (cache_local / 'inou').mkdir(parents=True, exist_ok=True)
            (cache_local / 'inou' / 'logs').mkdir(parents=True, exist_ok=True)
            (cache_local / 'build').mkdir(parents=True, exist_ok=True)
            (cache_local / 'venv').mkdir(parents=True, exist_ok=True)
        except Exception as e:
            self._fail_fast(f'Failed to create cache directory structure: {e}')
            return  # Should not reach here in normal execution, but helps in tests

    def _fail_fast(self, message: str) -> None:
        """Print error message and exit immediately."""
        print(f'ERROR: {message}', file=sys.stderr)
        sys.exit(1)

    @staticmethod
    def possible_config_paths() -> List[str]:
        """
        Get list of possible configuration file paths in search order.
        Priority: environment-specific paths first, then fallback paths.

        Returns:
            List of potential configuration file paths to check
        """
        paths = []

        # Add environment-based paths first (highest priority)
        if os.environ.get('HAGENT_REPO_DIR'):
            paths.append(str(Path(os.environ['HAGENT_REPO_DIR']) / 'hagent.yaml'))
        if os.environ.get('HAGENT_BUILD_DIR'):
            paths.append(str(Path(os.environ['HAGENT_BUILD_DIR']) / 'hagent.yaml'))

        # Add Docker-specific paths
        paths.extend(
            [
                '/code/workspace/repo/hagent.yaml',
            ]
        )

        # Add current directory paths (lowest priority)
        paths.extend(
            [
                './hagent.yaml',
                'hagent.yaml',
            ]
        )

        return paths

    @staticmethod
    def find_config() -> str:
        """
        Locate hagent.yaml via the standard search path.

        Uses a hybrid approach: checks local paths first (for local mode),
        then returns container paths (for Docker mode where files will exist in container).

        Returns:
            Path to the first existing configuration file

        Raises:
            FileNotFoundError: If no configuration file is found
        """
        # Determine execution mode based on HAGENT_DOCKER
        possible_paths = PathManager.possible_config_paths()
        docker_mode = bool(os.environ.get('HAGENT_DOCKER'))
        for candidate in possible_paths:
            resolved = PathManager._resolve_readable_config_path(candidate, docker_mode)
            if resolved:
                return resolved

        # If we get here, no readable paths were found
        raise FileNotFoundError('No hagent.yaml found, try to set HAGENT_REPO_DIR')

    @staticmethod
    def _resolve_readable_config_path(path: Optional[str], docker_mode: bool) -> Optional[str]:
        """
        Resolve a candidate configuration path if it exists and is readable.

        Args:
            path: Candidate path string to validate.
            docker_mode: Whether Docker mode is enabled (via HAGENT_DOCKER).

        Returns:
            Resolved host path string if readable, otherwise None.
        """
        if not path:
            return None

        candidate = Path(path)

        # Helper to check readability of a path
        def _is_readable(p: Path) -> bool:
            return p.exists() and os.access(p, os.R_OK)

        try:
            resolved_candidate = candidate.resolve()
        except FileNotFoundError:
            resolved_candidate = candidate

        if _is_readable(resolved_candidate):
            return str(resolved_candidate)

        # Attempt to translate known Docker container paths to host paths for validation
        docker_prefix_map = {
            Path('/code/workspace/repo'): os.environ.get('HAGENT_REPO_DIR'),
            Path('/code/workspace/build'): os.environ.get('HAGENT_BUILD_DIR'),
            Path('/code/workspace/cache'): os.environ.get('HAGENT_CACHE_DIR'),
        }

        for container_prefix, host_prefix in docker_prefix_map.items():
            if not host_prefix:
                continue

            try:
                relative = candidate.relative_to(container_prefix)
            except ValueError:
                continue

            host_candidate = Path(host_prefix) / relative
            try:
                resolved_host_candidate = host_candidate.resolve()
            except FileNotFoundError:
                continue

            if _is_readable(resolved_host_candidate):
                return str(resolved_host_candidate)

        # For Docker mode, allow returning container paths when host translation is unavailable
        if docker_mode and candidate.as_posix().startswith('/code/workspace/'):
            return str(candidate)

        return None

    @property
    def repo_dir(self) -> Path:
        """Get the repository directory path (Docker path in Docker mode)."""
        return self._repo_dir

    @property
    def repo_mount_dir(self) -> Optional[Path]:
        """Get the repository mount directory path (local path for Docker mounts)."""
        return self._repo_mount_dir

    @property
    def build_dir(self) -> Path:
        """Get the build directory path (Docker path in Docker mode)."""
        return self._build_dir

    @property
    def build_mount_dir(self) -> Optional[Path]:
        """Get the build mount directory path (local path for Docker mounts)."""
        return self._build_mount_dir

    @property
    def cache_dir(self) -> Path:
        """Get the cache directory path (Docker path in Docker mode)."""
        return self._cache_dir

    @property
    def cache_mount_dir(self) -> Optional[Path]:
        """Get the cache mount directory path (local path for Docker mounts)."""
        return self._cache_mount_dir

    @property
    def tech_dir(self) -> Path:
        """Get the tech directory path (Docker path in Docker mode)."""
        return self._tech_dir

    @property
    def tech_mount_dir(self) -> Optional[Path]:
        """Get the tech mount directory path (local path for Docker mounts)."""
        return self._tech_mount_dir

    @property
    def private_dir(self) -> Optional[Path]:
        """Get the private directory path (optional, may be None)."""
        return self._private_dir

    @property
    def private_mount_dir(self) -> Optional[Path]:
        """Get the private mount directory path (local path for Docker mounts)."""
        return self._private_mount_dir

    def has_private_dir(self) -> bool:
        """Check if a private directory is configured and available."""
        return self._private_dir is not None

    def is_docker_mode(self) -> bool:
        """Check if running in Docker execution mode."""
        if self._is_docker is None:
            self._fail_fast('Execution mode not available. Internal error - should be set during initialization.')
        return self._is_docker

    def is_local_mode(self) -> bool:
        """Check if running in local execution mode."""
        return not self.is_docker_mode()

    def get_cache_dir(self) -> str:
        """
        Get the cache directory path for general hagent files.
        Replaces output_manager.get_output_dir().

        Returns:
            Path to HAGENT_CACHE_DIR/inou/
        """
        cache_inou = self.cache_dir / 'inou'
        return str(cache_inou)

    def get_cache_path(self, filename: str) -> str:
        """
        Get the full path for a cache file.
        Replaces output_manager.get_output_path().

        Args:
            filename: The name of the cache file (must be relative path)

        Returns:
            Full path to the cache file in HAGENT_CACHE_DIR/inou/

        Raises:
            SystemExit: If filename is invalid (same validation as output_manager)
        """
        # Use the same validation logic as output_manager.get_output_path()
        is_absolute = (
            os.path.isabs(filename)
            or filename.startswith('~')
            or (len(filename) >= 3 and filename[1:3] == ':\\')
            or filename.startswith('../')
            or filename == '..'
        )

        if is_absolute:
            print(f"ERROR: get_cache_path() called with invalid path: '{filename}'", file=sys.stderr)
            print('', file=sys.stderr)
            print('API CONSTRAINT VIOLATION:', file=sys.stderr)
            print('get_cache_path() only accepts relative paths within the cache directory.', file=sys.stderr)
            print('', file=sys.stderr)
            print('Examples of correct usage:', file=sys.stderr)
            print("  get_cache_path('my_file.log')           #  filename only", file=sys.stderr)
            print("  get_cache_path('subdir/my_file.txt')    #  relative path", file=sys.stderr)
            print('', file=sys.stderr)
            print('Examples of incorrect usage:', file=sys.stderr)
            print("  get_cache_path('/tmp/my_file.log')      #  absolute path", file=sys.stderr)
            print("  get_cache_path('../escape/file.txt')    #  escapes cache directory", file=sys.stderr)
            sys.exit(1)

        return str(self.cache_dir / 'inou' / filename)

    def get_log_dir(self) -> str:
        """
        Get the log directory path.

        Returns:
            Path to HAGENT_CACHE_DIR/inou/logs/
        """
        log_dir = self.cache_dir / 'inou' / 'logs'
        return str(log_dir)

    def get_build_cache_dir(self) -> str:
        """
        Get the build cache directory path for local mode file tracking.

        Returns:
            Path to HAGENT_CACHE_DIR/build/
        """
        build_cache = self.cache_dir / 'build'
        return str(build_cache)

    def _get_venv_dir(self) -> str:
        """
        Get the UV virtual environment directory path.

        Returns:
            Path to HAGENT_CACHE_DIR/venv/
        """
        venv_dir = self.cache_dir / 'venv'
        return str(venv_dir)

    @property
    def inou_dir(self) -> Path:
        """Directory for HAgent-internal files."""
        return self.cache_dir / 'inou'

    @property
    def logs_dir(self) -> Path:
        """Directory for log files."""
        return self.inou_dir / 'logs'

    @classmethod
    @contextmanager
    def configured(
        cls,
        docker_image: Optional[str] = None,
        repo_dir: Optional[str] = None,
        build_dir: Optional[str] = None,
        cache_dir: Optional[str] = None,
        tech_dir: Optional[str] = None,
        private_dir: Optional[str] = None,
    ):
        """Context manager for temporarily configuring PathManager.

        This is the preferred way to configure PathManager in tests, avoiding
        direct manipulation of environment variables.

        Args:
            docker_image: Docker image name (if set, enables Docker mode)
            repo_dir: Repository directory path
            build_dir: Build directory path
            cache_dir: Cache directory path
            tech_dir: Tech directory path
            private_dir: Private directory path (optional)

        Usage in tests:
            with PathManager.configured(docker_image='test:latest'):
                # PathManager uses these settings
                processor = V2chisel_batch()
            # Automatically restored after

        Yields:
            The configured PathManager instance
        """
        # Save current state
        old_instance = cls._instance
        old_initialized = cls._initialized

        # Reset singleton
        cls._instance = None
        cls._initialized = False

        try:
            # Create new instance with explicit config
            instance = super().__new__(cls)
            cls._instance = instance

            # Initialize attributes
            instance._repo_dir = None
            instance._build_dir = None
            instance._cache_dir = None
            instance._tech_dir = None
            instance._private_dir = None
            instance._repo_mount_dir = None
            instance._build_mount_dir = None
            instance._cache_mount_dir = None
            instance._tech_mount_dir = None
            instance._private_mount_dir = None
            instance._is_docker = None

            # Configure with explicit values
            instance._configure_explicit(
                docker_image=docker_image,
                repo_dir=repo_dir,
                build_dir=build_dir,
                cache_dir=cache_dir,
                tech_dir=tech_dir,
                private_dir=private_dir,
            )

            cls._initialized = True
            yield instance
        finally:
            # Restore previous state
            cls._instance = old_instance
            cls._initialized = old_initialized

    def _configure_explicit(
        self,
        docker_image: Optional[str],
        repo_dir: Optional[str],
        build_dir: Optional[str],
        cache_dir: Optional[str],
        tech_dir: Optional[str],
        private_dir: Optional[str],
    ) -> None:
        """Configure PathManager with explicit values instead of environment variables.

        Args:
            docker_image: Docker image name (if set, enables Docker mode)
            repo_dir: Repository directory path
            build_dir: Build directory path
            cache_dir: Cache directory path
            tech_dir: Tech directory path
            private_dir: Private directory path (optional)
        """
        self._is_docker = docker_image is not None

        if self._is_docker:
            # Docker mode - xxx_dir = Docker path, xxx_mount_dir = local path
            self._repo_mount_dir = Path(repo_dir) if repo_dir else None
            self._build_mount_dir = Path(build_dir) if build_dir else None
            self._cache_mount_dir = Path(cache_dir) if cache_dir else None
            self._tech_mount_dir = Path(tech_dir) if tech_dir else None
            # Docker container paths
            self._repo_dir = Path('/code/workspace/repo')
            self._build_dir = Path('/code/workspace/build')
            self._cache_dir = Path('/code/workspace/cache')
            self._tech_dir = Path('/code/workspace/tech')
        else:
            # Local mode - use provided paths or create temp paths for testing
            import tempfile

            temp_base = Path(tempfile.gettempdir()) / 'hagent_test'
            self._repo_dir = Path(repo_dir) if repo_dir else temp_base / 'repo'
            self._build_dir = Path(build_dir) if build_dir else temp_base / 'build'
            self._cache_dir = Path(cache_dir) if cache_dir else temp_base / 'cache'
            self._tech_dir = Path(tech_dir) if tech_dir else temp_base / 'tech'
            # In local mode, mount_dir = dir
            self._repo_mount_dir = self._repo_dir
            self._build_mount_dir = self._build_dir
            self._cache_mount_dir = self._cache_dir
            self._tech_mount_dir = self._tech_dir

            # Create directories if they don't exist (for local test mode)
            for dir_path in [self._repo_dir, self._build_dir, self._cache_dir, self._tech_dir]:
                dir_path.mkdir(parents=True, exist_ok=True)

        # Private dir is optional
        if private_dir:
            self._private_dir = Path(private_dir) if not self._is_docker else Path('/code/workspace/private')
            self._private_mount_dir = Path(private_dir)
        else:
            self._private_dir = None
            self._private_mount_dir = None

        # Create cache structure (skip for Docker container paths)
        self._create_cache_structure()


# Global singleton instance getter
def get_path_manager() -> PathManager:
    """
    Get the global PathManager singleton instance.

    Returns:
        The singleton PathManager instance
    """
    return PathManager()
