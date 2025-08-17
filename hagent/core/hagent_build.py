"""
Shared HagentBuilder core functionality.

Provides a unified interface for managing YAML configurations, profiles,
and build operations. Supports both direct shell execution and Docker-based
execution through pluggable execution strategies.
"""

import os
import yaml
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from hagent.inou.path_manager import PathManager
from hagent.inou.executor import ExecutionStrategy


class HagentBuildCore:
    """
    Core functionality for HAgent build operations.

    Handles YAML configuration loading, profile management, environment setup,
    and validation. Execution is delegated to pluggable execution strategies.
    """

    def __init__(self, config_path: str, execution_strategy: Optional[ExecutionStrategy] = None):
        """
        Initialize HagentBuildCore.

        Args:
            config_path: Path to the YAML configuration file (required)
            execution_strategy: Strategy for executing commands
        """
        self.config_path = config_path
        self.config = self._load_config()
        self.execution_strategy = execution_strategy

        # Initialize PathManager for centralized path management
        self.path_manager = PathManager(validate_env=True)

        # Get paths from PathManager
        self.repo_dir = self.path_manager.repo_dir
        self.build_base = self.path_manager.build_dir

        # Basic sanity checks
        assert self.config_path, 'config_path must be resolved'
        assert self.repo_dir.is_absolute(), 'repo_dir must be an absolute path'
        assert self.build_base.is_absolute(), 'build_base must be an absolute path'

    @staticmethod
    def possible_config_paths() -> List[str]:
        """
        Get list of possible configuration file paths in search order.

        Returns:
            List of potential configuration file paths to check
        """
        return PathManager.possible_config_paths()

    @staticmethod
    def find_config() -> str:
        """
        Locate hagent.yaml via the standard search path.

        Returns:
            Path to the first existing configuration file

        Raises:
            FileNotFoundError: If no configuration file is found
        """
        return PathManager.find_config()

    def _load_config(self) -> dict:
        """Load YAML configuration from file."""
        with open(self.config_path, 'r') as f:
            data = yaml.safe_load(f) or {}
        assert isinstance(data, dict), 'Top-level YAML must be a mapping'
        return data

    # ---------------------------- helpers ----------------------------

    @staticmethod
    def profile_title(p: dict) -> str:
        """Get profile title, preferring 'title' over 'description' for backward compatibility."""
        return (p.get('title') or p.get('description') or '').strip()

    def get_all_profiles(self) -> List[dict]:
        """Get all profiles from configuration."""
        profs = self.config.get('profiles', []) or []
        assert isinstance(profs, list), "'profiles' must be a list"
        return profs

    def find_profile_by_name(self, name: str) -> List[dict]:
        """Find profiles by exact name match (case-insensitive)."""
        return [p for p in self.get_all_profiles() if (p.get('name') or '').lower() == name.lower()]

    def find_profile_by_title(self, query: str) -> List[dict]:
        """Find profiles by title substring match (case-insensitive)."""
        q = (query or '').strip().lower()
        return [p for p in self.get_all_profiles() if q in self.profile_title(p).lower()]

    def get_profile_commands(self, profile: dict) -> List[dict]:
        """Get all commands/APIs for a profile."""
        return profile.get('apis', [])

    def find_command_in_profile(self, profile: dict, command_name: str) -> Optional[dict]:
        """Find a specific command/API within a profile."""
        for api in self.get_profile_commands(profile):
            if api.get('name') == command_name:
                return api
        return None

    def get_memory_requirement(self, profile: dict) -> int:
        """Get the memory requirement for a profile in GB."""
        return profile.get('memory', 0)

    # ---------------------------- environment setup ----------------------------

    def setup_environment(self, profile: dict, build_dir: Optional[Path] = None) -> Dict[str, str]:
        """
        Setup environment variables for a profile.

        Args:
            profile: Profile configuration
            build_dir: Build directory (defaults to self.build_base)

        Returns:
            Environment dictionary
        """
        if build_dir is None:
            build_dir = self.build_base

        env = os.environ.copy()
        cfg = profile.get('configuration', {})

        if isinstance(cfg, dict):
            for k, v in (cfg.get('environment') or {}).items():
                # Allow $VAR expansion in YAML values
                env[k] = os.path.expandvars(v)

        # Use PathManager to ensure consistent path handling
        env['HAGENT_REPO_DIR'] = str(self.path_manager.repo_dir)
        env['HAGENT_BUILD_DIR'] = str(build_dir)
        env['HAGENT_CACHE_DIR'] = str(self.path_manager.cache_dir)
        env['HAGENT_EXECUTION_MODE'] = self.path_manager.execution_mode
        return env

    # ---------------------------- track directive parsing ----------------------------

    def parse_track_directive(self, directive: str, build_dir: Optional[Path] = None) -> Tuple[str, str, Optional[str]]:
        """
        Parse track_repo_dir() or track_build_dir() directives.

        Note: This only parses the directive and computes paths.
        Directory validation is left to execution strategies since they
        understand their execution context (Docker vs direct).

        Args:
            directive: The directive string (e.g., "track_repo_dir('src/main/scala', ext='.scala')")
            build_dir: The build directory for this profile (defaults to self.build_base)

        Returns:
            Tuple of (resolved_path, func_type, ext) where:
            - resolved_path: Computed path (may not exist yet)
            - func_type: "repo_dir", "build_dir", or "unknown"
            - ext: The extension filter (if specified)
        """
        if build_dir is None:
            build_dir = self.build_base

        if directive.startswith('track_repo_dir('):
            func_type = 'repo_dir'
            content = directive[15:-1]  # Remove "track_repo_dir(" and ")"
        elif directive.startswith('track_build_dir('):
            func_type = 'build_dir'
            content = directive[16:-1]  # Remove "track_build_dir(" and ")"
        else:
            return directive, 'unknown', None

        # Parse parameters
        parts = [p.strip().strip('\'"') for p in content.split(',')]
        path = parts[0]
        ext = None

        for part in parts[1:]:
            if part.startswith('ext='):
                ext = part[4:].strip('\'"')

        # Compute paths without validation
        if func_type == 'repo_dir':
            resolved_path = str((self.repo_dir / path).resolve())
        elif func_type == 'build_dir':
            resolved_path = str((build_dir / path).resolve())
        else:
            resolved_path = path

        return resolved_path, func_type, ext

    def validate_configuration(self, profile: dict, build_dir: Optional[Path] = None, dry_run: bool = False) -> None:
        """
        Parse and validate track directives in the configuration.

        Note: This only validates syntax and extracts directory paths.
        Actual directory existence validation is left to execution strategies
        since they understand their execution context (Docker vs direct).

        Args:
            profile: Profile configuration dictionary
            build_dir: Build directory for this profile (defaults to self.build_base)
            dry_run: If True, skip parsing (currently unused)

        Raises:
            ValueError: If configuration directive syntax is invalid
        """
        if build_dir is None:
            build_dir = self.build_base

        cfg = profile.get('configuration', {})
        if not isinstance(cfg, dict):
            return

        # Parse source and output directives to validate syntax
        for key in ['source', 'output']:
            if key in cfg:
                directive = cfg[key]
                if isinstance(directive, str) and ('track_repo_dir(' in directive or 'track_build_dir(' in directive):
                    try:
                        # Extract the directory argument from the directive
                        if directive.startswith('track_repo_dir('):
                            content = directive[15:-1]  # Remove "track_repo_dir(" and ")"
                            directory = content.split(',')[0].strip().strip('\'"')
                        elif directive.startswith('track_build_dir('):
                            content = directive[16:-1]  # Remove "track_build_dir(" and ")"
                            directory = content.split(',')[0].strip().strip('\'"')
                        else:
                            continue

                        # Validate syntax - directory argument should not be empty
                        if not directory:
                            raise ValueError(f'Empty directory argument in directive: {directive}')

                    except (IndexError, ValueError) as e:
                        raise ValueError(
                            f"Configuration validation failed for {key} '{directive}': Invalid directive syntax: {e}"
                        )

    # ---------------------------- profile selection ----------------------------

    def select_profile(self, exact_name: Optional[str] = None, title_query: Optional[str] = None) -> dict:
        """
        Select a profile based on name or title query.

        Args:
            exact_name: Exact profile name match
            title_query: Title substring match

        Returns:
            Selected profile dictionary

        Raises:
            ValueError: If no profile found or multiple matches
        """
        if exact_name:
            hits = self.find_profile_by_name(exact_name)
            if not hits:
                avail = ', '.join(p.get('name', '<unnamed>') for p in self.get_all_profiles())
                raise ValueError(f"No profile matched name '{exact_name}'. Available names: {avail}")
            if len(hits) > 1:
                raise ValueError(
                    f"Multiple profiles matched name '{exact_name}': " + ', '.join(p.get('name', '<unnamed>') for p in hits)
                )
            return hits[0]

        if title_query:
            hits = self.find_profile_by_title(title_query)
            if not hits:
                raise ValueError(
                    f"No profile matched title query '{title_query}' in titles. "
                    + 'Try exact name. Titles: '
                    + '; '.join(f'[{p.get("name")}] {self.profile_title(p) or "N/A"}' for p in self.get_all_profiles())
                )
            if len(hits) > 1:
                raise ValueError(
                    f"Multiple profiles matched title query '{title_query}'. "
                    + 'Disambiguate with exact name. Matches: '
                    + '; '.join(f'[{p.get("name")}] {self.profile_title(p) or "N/A"}' for p in hits)
                )
            return hits[0]

        raise ValueError('You must specify either exact_name or title_query.')

    # ---------------------------- command execution ----------------------------

    def execute_command(
        self,
        profile: dict,
        command_name: str,
        extra_args: Optional[List[str]] = None,
        build_dir: Optional[Path] = None,
        dry_run: bool = False,
        quiet: bool = False,
    ) -> Tuple[int, str, str]:
        """
        Execute a command from a profile.

        Args:
            profile: Profile configuration
            command_name: Name of the command/API to execute
            extra_args: Additional arguments to append to command
            build_dir: Build directory (defaults to self.build_base)
            dry_run: If True, validate but don't execute
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)

        Raises:
            ValueError: If command not found
            RuntimeError: If execution strategy not set
        """
        if build_dir is None:
            build_dir = self.build_base

        # Find the command
        command_info = self.find_command_in_profile(profile, command_name)
        if not command_info:
            raise ValueError(f"Command '{command_name}' not found in profile '{profile.get('name')}'")

        # Validate configuration before proceeding
        self.validate_configuration(profile, build_dir, dry_run)

        # Setup environment
        env = self.setup_environment(profile, build_dir)

        # Compose command; replace simple placeholders
        command = command_info['command']
        if extra_args:
            command = f'{command} {" ".join(extra_args)}'
        command = command.replace('$HAGENT_BUILD_DIR', str(build_dir)).replace('$HAGENT_REPO_DIR', str(self.repo_dir))

        # Determine working directory
        cwd = command_info.get('cwd', str(self.repo_dir))
        cwd = cwd.replace('$HAGENT_BUILD_DIR', str(build_dir)).replace('$HAGENT_REPO_DIR', str(self.repo_dir))
        cwd_path = Path(cwd).resolve()

        # Validate working directory exists (skip for Docker execution strategies)
        # Docker strategies handle their own path validation inside containers
        if not hasattr(self.execution_strategy, 'container_manager'):
            if not cwd_path.exists():
                raise FileNotFoundError(f'Working directory does not exist: {cwd_path}')
            if not cwd_path.is_dir():
                raise NotADirectoryError(f'Working directory path is not a directory: {cwd_path}')

        if dry_run:
            return 0, f'Would execute: {command} in {cwd_path}', ''

        # Create build directory for real runs (skip for Docker execution strategies)
        if not hasattr(self.execution_strategy, 'container_manager'):
            build_dir.mkdir(parents=True, exist_ok=True)

        # Execute using the strategy
        if not self.execution_strategy:
            raise RuntimeError('No execution strategy set')

        return self.execution_strategy.run(command, str(cwd_path), env, quiet)

    # ---------------------------- convenience methods ----------------------------

    def execute(
        self,
        exact_name: Optional[str] = None,
        title_query: Optional[str] = None,
        command_name: str = '',
        extra_args: Optional[List[str]] = None,
        build_dir: Optional[Path] = None,
        dry_run: bool = False,
        quiet: bool = False,
    ) -> Tuple[int, str, str]:
        """
        Convenience method to select profile and execute command in one call.

        Args:
            exact_name: Exact profile name match
            title_query: Title substring match
            command_name: Name of the command/API to execute
            extra_args: Additional arguments to append to command
            build_dir: Build directory (defaults to self.build_base)
            dry_run: If True, validate but don't execute
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        profile = self.select_profile(exact_name, title_query)
        return self.execute_command(profile, command_name, extra_args, build_dir, dry_run, quiet)
