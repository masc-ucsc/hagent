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
        self._repo_dir: Optional[Path] = None
        self._build_dir: Optional[Path] = None
        self._cache_dir: Optional[Path] = None
        self._tech_dir: Optional[Path] = None
        self._private_dir: Optional[Path] = None
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
        """Validate environment variables for local execution mode."""
        missing_vars = []

        repo_dir = os.environ.get('HAGENT_REPO_DIR')
        if not repo_dir:
            missing_vars.append('HAGENT_REPO_DIR')
        else:
            self._repo_dir = Path(repo_dir).resolve()
            if not self._repo_dir.exists():
                self._fail_fast(f'HAGENT_REPO_DIR path does not exist: {self._repo_dir}')
                return  # Should not reach here in normal execution, but helps in tests

        build_dir = os.environ.get('HAGENT_BUILD_DIR')
        if not build_dir:
            missing_vars.append('HAGENT_BUILD_DIR')
        else:
            self._build_dir = Path(build_dir).resolve()

        cache_dir = os.environ.get('HAGENT_CACHE_DIR')
        if not cache_dir:
            missing_vars.append('HAGENT_CACHE_DIR')
        else:
            self._cache_dir = Path(cache_dir).resolve()

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

        # Private dir - optional, not required
        private_dir = os.environ.get('HAGENT_PRIVATE_DIR')
        if private_dir:
            self._private_dir = Path(private_dir).resolve()
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
        """Validate environment variables for Docker execution mode."""
        # In Docker mode, only HAGENT_DOCKER is required from user
        # Other variables are optional - if provided, they will be mounted as host directories
        # If not provided, use default container paths

        # Check for host directory mounts (optional)
        if os.environ.get('HAGENT_REPO_DIR'):
            self._repo_dir = Path(os.environ['HAGENT_REPO_DIR']).resolve()
            if not self._repo_dir.exists():
                self._fail_fast(f'HAGENT_REPO_DIR path does not exist: {self._repo_dir}')
                return
        else:
            # Use default container path - this will be a virtual path for container creation
            self._repo_dir = Path('/code/workspace/repo')

        if os.environ.get('HAGENT_BUILD_DIR'):
            self._build_dir = Path(os.environ['HAGENT_BUILD_DIR']).resolve()
        else:
            # Use default container path
            self._build_dir = Path('/code/workspace/build')

        if os.environ.get('HAGENT_CACHE_DIR'):
            self._cache_dir = Path(os.environ['HAGENT_CACHE_DIR']).resolve()
        else:
            # Use default container path
            self._cache_dir = Path('/code/workspace/cache')

        if os.environ.get('HAGENT_TECH_DIR'):
            self._tech_dir = Path(os.environ['HAGENT_TECH_DIR']).resolve()
        else:
            # Use default container path
            self._tech_dir = Path('/code/workspace/tech')

        # Private dir - optional, only set if explicitly provided
        if os.environ.get('HAGENT_PRIVATE_DIR'):
            self._private_dir = Path(os.environ['HAGENT_PRIVATE_DIR']).resolve()
            if not self._private_dir.exists():
                self._fail_fast(f'HAGENT_PRIVATE_DIR path does not exist: {self._private_dir}')
                return
        # Note: Do not set a default value - private_dir remains None if not provided

    def _create_cache_structure(self) -> None:
        """Create the HAGENT_CACHE_DIR directory structure."""
        if not self._cache_dir:
            return

        # Skip cache creation for container paths (they don't exist on the host)
        if str(self._cache_dir).startswith('/code/workspace/'):
            return

        try:
            # Create main directories
            (self._cache_dir / 'inou').mkdir(parents=True, exist_ok=True)
            (self._cache_dir / 'inou' / 'logs').mkdir(parents=True, exist_ok=True)
            (self._cache_dir / 'build').mkdir(parents=True, exist_ok=True)
            (self._cache_dir / 'venv').mkdir(parents=True, exist_ok=True)
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
        """Get the repository directory path."""
        if not self._repo_dir:
            self._fail_fast('Repository directory not available. Ensure HAGENT_REPO_DIR is set.')
        return self._repo_dir

    @property
    def build_dir(self) -> Path:
        """Get the build directory path."""
        if not self._build_dir:
            self._fail_fast('Build directory not available. Ensure HAGENT_BUILD_DIR is set.')
        return self._build_dir

    @property
    def cache_dir(self) -> Path:
        """Get the cache directory path."""
        if not self._cache_dir:
            self._fail_fast('Cache directory not available. Ensure HAGENT_CACHE_DIR is set.')
        return self._cache_dir

    @property
    def tech_dir(self) -> Path:
        """Get the tech directory path."""
        return self._tech_dir

    @property
    def private_dir(self) -> Optional[Path]:
        """Get the private directory path (optional, may be None)."""
        return self._private_dir

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
    def reset(cls) -> None:
        """
        Reset the singleton instance.

        Useful for testing when you need to reinitialize with different environment.
        """
        cls._instance = None
        cls._initialized = False


# Global singleton instance getter
def get_path_manager() -> PathManager:
    """
    Get the global PathManager singleton instance.

    Returns:
        The singleton PathManager instance
    """
    return PathManager()
