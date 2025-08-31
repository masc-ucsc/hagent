"""
Path Manager for HAgent

Consolidates path resolution, environment variable handling, and configuration
file discovery functionality. Replaces functionality from hagent_build.py
and output_manager.py.

Provides centralized management of HAGENT_* environment variables and
path validation with fail-fast error handling.
"""

import os
import sys
from pathlib import Path
from typing import List, Optional


class PathManager:
    """
    Manages all path-related operations for HAgent including environment
    variable validation, path resolution, and cache directory structure.
    """

    def __init__(self, validate_env: bool = True):
        """
        Initialize PathManager with optional environment validation.

        Args:
            validate_env: Whether to validate environment variables at initialization
        """
        self._repo_dir: Optional[Path] = None
        self._build_dir: Optional[Path] = None
        self._cache_dir: Optional[Path] = None
        self._execution_mode: Optional[str] = None

        if validate_env:
            self._validate_and_setup_environment()

    def _validate_and_setup_environment(self) -> None:
        """
        Validate required HAGENT_* environment variables and setup paths.
        Fails fast with clear error messages if validation fails.
        """
        self._execution_mode = os.environ.get('HAGENT_EXECUTION_MODE')

        if not self._execution_mode:
            self._fail_fast("HAGENT_EXECUTION_MODE environment variable is not set.\nMust be either 'local' or 'docker'.")
            return  # Should not reach here in normal execution, but helps in tests

        if self._execution_mode not in ['local', 'docker']:
            self._fail_fast(f"Invalid HAGENT_EXECUTION_MODE: '{self._execution_mode}'.\nMust be either 'local' or 'docker'.")
            return  # Should not reach here in normal execution, but helps in tests

        if self._execution_mode == 'local':
            self._validate_local_mode()
        elif self._execution_mode == 'docker':
            self._validate_docker_mode()

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

        if missing_vars:
            self._fail_fast(
                f'Local execution mode requires these environment variables: {", ".join(missing_vars)}\n'
                'All HAGENT_* variables must be set for local mode.'
            )
            return  # Should not reach here in normal execution, but helps in tests

    def _validate_docker_mode(self) -> None:
        """Validate environment variables for Docker execution mode."""
        # In Docker mode, only HAGENT_EXECUTION_MODE is required from user
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

        Returns:
            List of potential configuration file paths to check
        """
        paths = [
            './hagent.yaml',
            'hagent.yaml',
        ]

        # Add Docker-specific paths
        paths.extend(
            [
                '/code/workspace/repo/hagent.yaml',
                '/code/workspace/hagent.yaml',
            ]
        )

        # Add environment-based paths
        if os.environ.get('HAGENT_REPO_DIR'):
            paths.append(str(Path(os.environ['HAGENT_REPO_DIR']) / 'hagent.yaml'))
        if os.environ.get('HAGENT_BUILD_DIR'):
            paths.append(str(Path(os.environ['HAGENT_BUILD_DIR']) / 'hagent.yaml'))

        return paths

    @staticmethod
    def find_config() -> str:
        """
        Locate hagent.yaml via the standard search path.

        Returns:
            Path to the first existing configuration file

        Raises:
            FileNotFoundError: If no configuration file is found
        """
        for path in PathManager.possible_config_paths():
            if path and os.path.exists(path):
                return str(Path(path).resolve())
        repo_dir = os.environ.get('HAGENT_REPO_DIR')
        if repo_dir:
            raise FileNotFoundError(f'No hagent.yaml found in HAGENT_REPO_DIR set to {repo_dir} paths')
        raise FileNotFoundError('No hagent.yaml found, try to set HAGENT_REPO_DIR')

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
    def execution_mode(self) -> str:
        """Get the execution mode."""
        if not self._execution_mode:
            self._fail_fast('Execution mode not available. Ensure HAGENT_EXECUTION_MODE is set.')
        return self._execution_mode

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
