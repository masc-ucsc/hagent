"""
Builder for HAgent - Unified YAML-based build system

Provides a unified interface for managing YAML configurations, profiles,
and build operations. Integrates with the Runner infrastructure for
execution, file tracking, and path management.
"""

import os
import sys
import yaml
from pathlib import Path
from typing import Dict, List, Optional, Tuple

from .runner import Runner
from .path_manager import PathManager
from .filesystem import FileSystemFactory, FileSystem


class Builder:
    """
    Unified build system for HAgent.

    Handles YAML configuration loading, profile management, environment setup,
    and command execution through Runner integration. Provides both direct
    execution and file tracking capabilities.

    Works in two modes:
    - With hagent.yaml: Full profile-based API execution via run_api() + direct execution via run_cmd()
    - Without hagent.yaml: Direct execution via run_cmd() only, run_api() returns helpful error

    This eliminates the need to choose between Builder and Runner - always use Builder.
    """

    def __init__(self, config_path: Optional[str] = None, docker_image: Optional[str] = None):
        """
        Initialize Builder.

        Args:
            config_path: Path to the YAML configuration file (auto-discovered if None)
            docker_image: Docker image for container execution (if needed)
        """
        # Always initialize Runner first
        self.runner = Runner(docker_image)
        self.error_message = ''

        # Initialize FileSystem (will be set after Runner setup)
        self.filesystem: Optional[FileSystem] = None

        # Try to find config path, but defer loading until after setup()
        self.config_path = None
        self.config = {}
        self.has_config = False

        try:
            self.config_path = config_path or self._find_config()
            # Note: Config loading deferred until setup() when FileSystem is available
        except (FileNotFoundError, ValueError):
            # Config not found or invalid - Builder can still work without it
            pass

    @staticmethod
    def _find_config() -> str:
        """
        Locate hagent.yaml via the standard search path.

        Returns:
            Path to the first existing configuration file

        Raises:
            FileNotFoundError: If no configuration file is found
        """
        return PathManager.find_config()

    def _load_config(self) -> dict:
        """
        Load YAML configuration from file using FileSystem.

        This now works in both local and Docker execution modes!
        """
        if not self.filesystem:
            raise RuntimeError('FileSystem not initialized - call setup() first')

        try:
            # For Docker mode, translate host paths to container paths
            config_path_for_fs = self.config_path
            if hasattr(self.filesystem, 'container_manager') and self.runner:
                # This is DockerFileSystem - translate host path to container path
                path_manager = self.runner.path_manager
                if hasattr(path_manager, '_repo_dir') and path_manager._repo_dir:
                    host_repo_dir = str(path_manager._repo_dir)
                    container_repo_dir = '/code/workspace/repo'
                    if self.config_path.startswith(host_repo_dir):
                        # Replace host repo path with container repo path
                        import os
                        import posixpath

                        relative_path = os.path.relpath(self.config_path, host_repo_dir)
                        # Join using POSIX semantics for container path
                        config_path_for_fs = posixpath.join(container_repo_dir, relative_path)

            # Use FileSystem to read config - works in both local and Docker!
            content = self.filesystem.read_text(config_path_for_fs)
            data = yaml.safe_load(content) or {}
            assert isinstance(data, dict), 'Top-level YAML must be a mapping'
            return data
        except Exception as e:
            raise ValueError(f'Failed to load config from {self.config_path}: {e}')

    def set_error(self, message: str) -> None:
        """Set error message following Tool pattern."""
        self.error_message = message

    def get_error(self) -> str:
        """Get current error message following Tool pattern."""
        return self.error_message

    def setup(self) -> bool:
        """
        Setup the execution environment and initialize FileSystem.

        Returns:
            True if setup successful, False otherwise
        """
        if not self.runner:
            self.set_error('Runner not initialized')
            return False

        success = self.runner.setup()

        # Initialize FileSystem after Runner is setup (or try local fallback)
        if success:
            try:
                self.filesystem = FileSystemFactory.create_for_builder(self)
            except Exception as e:
                self.set_error(f'FileSystem initialization failed: {e}')
                success = False

        # Try to load config - if Runner setup failed, try local file reading for dry run compatibility
        if self.config_path:
            try:
                if success:
                    # Use FileSystem for config loading (works in both local and Docker)
                    self.config = self._load_config()
                else:
                    # Fallback: try direct file reading for local files (dry run compatibility)
                    import os

                    if os.path.exists(self.config_path):
                        import yaml

                        with open(self.config_path, 'r') as f:
                            self.config = yaml.safe_load(f) or {}
                        assert isinstance(self.config, dict), 'Top-level YAML must be a mapping'
                    else:
                        raise FileNotFoundError(f'Config file not found: {self.config_path}')

                self.has_config = True
            except (FileNotFoundError, ValueError):
                # Config not found or invalid - continue without it, but preserve the Runner setup error
                self.config_path = None
                if not success:
                    self.set_error(f'Runner setup failed: {self.runner.get_error()}')
                pass

        # Return success if either Runner setup succeeded OR we have config for dry run mode
        if not success and not self.has_config:
            self.set_error(f'Runner setup failed: {self.runner.get_error()}')
            return False

        return True

    # ---------------------------- helpers ----------------------------

    @staticmethod
    def profile_title(p: dict) -> str:
        """Get profile title, preferring 'title' over 'description' for backward compatibility."""
        return (p.get('title') or p.get('description') or '').strip()

    def get_all_profiles(self) -> List[dict]:
        """Get all profiles from configuration."""
        if not self.has_config:
            return []
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

    # ---------------------------- environment setup ----------------------------

    def _setup_environment(self, profile: dict, build_dir: Optional[Path] = None) -> Dict[str, str]:
        """
        Setup environment variables for a profile.

        Args:
            profile: Profile configuration
            build_dir: Build directory (defaults to PathManager's build_dir)

        Returns:
            Environment dictionary
        """
        # Get PathManager (either from Runner or create new one)
        if self.runner:
            path_manager = self.runner.path_manager
        else:
            path_manager = PathManager()

        if build_dir is None:
            build_dir = path_manager.build_dir

        env = os.environ.copy()
        cfg = profile.get('configuration', {})

        if isinstance(cfg, dict):
            for k, v in (cfg.get('environment') or {}).items():
                # Allow $VAR expansion in YAML values
                env[k] = os.path.expandvars(v)

        # Use PathManager for consistent path handling
        env['HAGENT_REPO_DIR'] = str(path_manager.repo_dir)
        env['HAGENT_BUILD_DIR'] = str(build_dir)
        env['HAGENT_CACHE_DIR'] = str(path_manager.cache_dir)
        env['HAGENT_EXECUTION_MODE'] = path_manager.execution_mode
        return env

    # ---------------------------- track directive parsing ----------------------------

    def _parse_track_directive(self, directive: str, build_dir: Optional[Path] = None) -> Tuple[str, str, Optional[str]]:
        """
        Parse track_repo_dir() or track_build_dir() directives.

        Args:
            directive: The directive string (e.g., "track_repo_dir('src/main/scala', ext='.scala')")
            build_dir: The build directory for this profile

        Returns:
            Tuple of (resolved_path, func_type, ext) where:
            - resolved_path: Computed path
            - func_type: "repo_dir", "build_dir", or "unknown"
            - ext: The extension filter (if specified)
        """
        # Get PathManager (either from Runner or create new one)
        if self.runner:
            path_manager = self.runner.path_manager
        else:
            path_manager = PathManager()

        if build_dir is None:
            build_dir = path_manager.build_dir

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

        # Compute paths
        if func_type == 'repo_dir':
            resolved_path = str((path_manager.repo_dir / path).resolve())
        elif func_type == 'build_dir':
            resolved_path = str((build_dir / path).resolve())
        else:
            resolved_path = path

        return resolved_path, func_type, ext

    def _setup_file_tracking(self, profile: dict, build_dir: Optional[Path] = None) -> None:
        """
        Setup file tracking based on profile configuration.

        Args:
            profile: Profile configuration dictionary
            build_dir: Build directory for this profile
        """
        # Only setup file tracking if Runner is available
        if not self.runner:
            return

        if build_dir is None:
            build_dir = self.runner.path_manager.build_dir

        cfg = profile.get('configuration', {})
        if not isinstance(cfg, dict):
            return

        # Parse source and output directives
        for key in ['source', 'output']:
            if key in cfg:
                directive = cfg[key]
                if isinstance(directive, str) and ('track_repo_dir(' in directive or 'track_build_dir(' in directive):
                    resolved_path, func_type, ext = self._parse_track_directive(directive, build_dir)
                    if func_type in ['repo_dir', 'build_dir']:
                        # Use Runner's file tracking
                        if Path(resolved_path).is_file():
                            self.runner.track_file(resolved_path)
                        else:
                            self.runner.track_dir(resolved_path, ext)

    def _validate_configuration(self, profile: dict, build_dir: Optional[Path] = None, dry_run: bool = False) -> None:
        """
        Parse and validate track directives in the configuration.

        Args:
            profile: Profile configuration dictionary
            build_dir: Build directory for this profile
            dry_run: If True, skip parsing (currently unused)

        Raises:
            ValueError: If configuration directive syntax is invalid
        """
        if build_dir is None:
            build_dir = self.runner.path_manager.build_dir

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

    def _select_profile(self, exact_name: Optional[str] = None, title_query: Optional[str] = None) -> dict:
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

    def _run_api(
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
            build_dir: Build directory
            dry_run: If True, validate but don't execute
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)

        Raises:
            ValueError: If command not found
        """
        # For dry run, use PathManager directly to avoid Runner dependency
        if dry_run:
            path_manager = PathManager()
            if build_dir is None:
                build_dir = path_manager.build_dir
        elif self.runner:
            if build_dir is None:
                build_dir = self.runner.path_manager.build_dir
        else:
            raise RuntimeError('Runner not available and not in dry run mode')

        # Find the command
        command_info = self.find_command_in_profile(profile, command_name)
        if not command_info:
            raise ValueError(f"Command '{command_name}' not found in profile '{profile.get('name')}'")

        # Validate configuration before proceeding
        self._validate_configuration(profile, build_dir, dry_run)

        # Setup file tracking (only for non-dry runs with Runner)
        if not dry_run and self.runner:
            self._setup_file_tracking(profile, build_dir)

        # Setup environment
        env = self._setup_environment(profile, build_dir)

        # Compose command; replace simple placeholders
        command = command_info['command']
        if extra_args:
            command = f'{command} {" ".join(extra_args)}'

        # For dry run, use PathManager directly
        if dry_run:
            path_manager = PathManager()
            repo_dir = path_manager.repo_dir
        else:
            repo_dir = self.runner.path_manager.repo_dir

        command = command.replace('$HAGENT_BUILD_DIR', str(build_dir)).replace('$HAGENT_REPO_DIR', str(repo_dir))

        # Determine working directory
        cwd = command_info.get('cwd', str(repo_dir))
        cwd = cwd.replace('$HAGENT_BUILD_DIR', str(build_dir)).replace('$HAGENT_REPO_DIR', str(repo_dir))

        if dry_run:
            return 0, f'Would execute: {command} in {cwd}', ''

        # Execute using Runner
        if not self.runner:
            raise RuntimeError('Runner not available for non-dry run execution')
        return self.runner.run_cmd(command, cwd, env, quiet)

    # ---------------------------- convenience methods ----------------------------

    def run_api(
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
            build_dir: Build directory
            dry_run: If True, validate but don't execute
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        if not self.has_config:
            error_msg = 'No hagent.yaml configuration found. Use run_cmd() for direct command execution.'
            self.set_error(error_msg)
            return -1, '', error_msg

        profile = self._select_profile(exact_name, title_query)
        return self._run_api(profile, command_name, extra_args, build_dir, dry_run, quiet)

    # Backward-compatible aliases (deprecated). Prefer run_api().
    def _execute_command(
        self,
        profile: dict,
        command_name: str,
        extra_args: Optional[List[str]] = None,
        build_dir: Optional[Path] = None,
        dry_run: bool = False,
        quiet: bool = False,
    ) -> Tuple[int, str, str]:
        return self._run_api(profile, command_name, extra_args, build_dir, dry_run, quiet)

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
        """Backward-compatible alias for run_api()."""
        return self.run_api(exact_name, title_query, command_name, extra_args, build_dir, dry_run, quiet)

    # ---------------------------- listing methods ----------------------------

    def list_profiles(self):
        """List all available profiles."""
        if not self.has_config:
            print('\nNo hagent.yaml configuration found.')
            print('Available operations:')
            print('  - Use run_cmd() for direct command execution')
            print('  - File tracking: track_file(), track_dir(), get_diffs()')
            print('  - Add hagent.yaml configuration to enable profile-based APIs')
            return

        profiles = self.get_all_profiles()
        if not profiles:
            print('\nNo profiles found in configuration.')
            return

        print('\nAvailable profiles:')
        print('-' * 60)
        for p in profiles:
            print(f'\nname: {p.get("name", "<unnamed>")}')
            print(f'  title: {self.profile_title(p) or "N/A"}')
            print('  APIs:')
            for api in p.get('apis', []):
                print(f'    - {api.get("name", "<noname>")}: {api.get("description", "N/A")}')

    def list_apis_for_profile(self, exact_name: Optional[str], title_query: Optional[str]):
        """List APIs for given profile selection."""
        if not self.has_config:
            print('Error: No hagent.yaml configuration found. Cannot list profile APIs.', file=sys.stderr)
            return False

        if exact_name:
            hits = self.find_profile_by_name(exact_name)
            if not hits:
                # Exact error text required by user.
                avail = ', '.join(p.get('name', '<unnamed>') for p in self.get_all_profiles())
                print(f"Error: No profile matched --name '{exact_name}'. Available names: {avail}", file=sys.stderr)
                return False
            if len(hits) > 1:
                print(
                    f"Error: --name '{exact_name}' matched multiple profiles: " + ', '.join(p.get('name') for p in hits),
                    file=sys.stderr,
                )
                return False
        elif title_query:
            hits = self.find_profile_by_title(title_query)
            if not hits:
                print(f"Error: --profile '{title_query}' did not match any profile titles.", file=sys.stderr)
                self.list_profiles()
                return False
            if len(hits) > 1:
                print('Error: Multiple profiles matched --profile. Disambiguate with --name.\nMatches:', file=sys.stderr)
                for p in hits:
                    print(f'  {p.get("name")} : {self.profile_title(p) or "N/A"}', file=sys.stderr)
                return False
        else:
            print('Error: list_apis_for_profile requires either exact_name or title_query.', file=sys.stderr)
            return False

        # List APIs for the matched profile
        for p in hits:
            print(f'\nAPIs for {p.get("name", "<unnamed>")} [{self.profile_title(p) or "N/A"}]:')
            for api in p.get('apis', []):
                line = f'  {api.get("name", "<noname>")}: {api.get("description", "N/A")}'
                if 'command' in api:
                    line += f'\n    Command: {api["command"]}'
                print(line)

        return True

    # ---------------------------- direct runner delegation ----------------------------

    def run_cmd(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = False
    ) -> Tuple[int, str, str]:
        """Execute a command using the underlying Runner (direct delegation)."""
        if not self.runner:
            self.set_error('Runner not initialized')
            return -1, '', 'Runner not initialized'
        return self.runner.run_cmd(command, cwd, env, quiet)

    def run(
        self, command: str, cwd: str = '.', env: Optional[Dict[str, str]] = None, quiet: bool = False
    ) -> Tuple[int, str, str]:
        """Backward-compatible alias for run_cmd."""
        return self.run_cmd(command, cwd, env, quiet)

    def set_cwd(self, new_workdir: str) -> bool:
        """
        Change the working directory with validation and path translation.

        If in local mode and the path starts with Docker container paths
        (/code/workspace/repo, /code/workspace/build, /code/workspace/cache),
        translates them to the corresponding local paths from PathManager.
        """
        if not self.runner:
            self.set_error('Runner not initialized')
            return False

        # Translate Docker container paths to local paths when in local mode
        translated_path = new_workdir
        if self.runner.is_local_mode():
            path_manager = self.runner.path_manager

            # Define container-to-local path mappings
            container_mappings = {
                '/code/workspace/repo': str(path_manager.repo_dir),
                '/code/workspace/build': str(path_manager.build_dir),
                '/code/workspace/cache': str(path_manager.cache_dir),
            }

            # Check if path starts with any container path
            for container_prefix, local_base in container_mappings.items():
                if new_workdir.startswith(container_prefix):
                    # Replace container prefix with local base
                    if new_workdir == container_prefix:
                        translated_path = local_base
                    else:
                        # Handle subdirectories: /code/workspace/repo/foo/bar -> /local/repo/foo/bar
                        suffix = new_workdir[len(container_prefix) :]
                        if suffix.startswith('/'):
                            suffix = suffix[1:]  # Remove leading slash
                        translated_path = str(Path(local_base) / suffix)
                    break

        return self.runner.set_cwd(translated_path)

    def translate_path_to_container(self, path: str) -> str:
        """
        Translate local paths to Docker container paths when in local mode.
        In Docker mode, paths are already container paths so no translation needed.

        Args:
            path: Local path to translate

        Returns:
            Container path string
        """
        if not self.runner:
            return path

        # In Docker mode, paths are already container paths
        if self.runner.is_docker_mode():
            return path

        # In local mode, translate local paths to container paths for compatibility
        path_manager = self.runner.path_manager

        # Define path mappings
        local_to_container = {
            str(path_manager.repo_dir): '/code/workspace/repo',
            str(path_manager.build_dir): '/code/workspace/build',
            str(path_manager.cache_dir): '/code/workspace/cache',
        }

        for local_prefix, container_prefix in local_to_container.items():
            if path.startswith(local_prefix):
                if path == local_prefix:
                    return container_prefix
                else:
                    suffix = path[len(local_prefix) :]
                    if suffix.startswith('/'):
                        suffix = suffix[1:]
                    return f'{container_prefix}/{suffix}' if suffix else container_prefix

        # No mapping found - return original path (might be a container-only path)
        return path

    def translate_path_to_local(self, path: str) -> Optional[str]:
        """
        Translate Docker container paths to local paths when in Docker mode.
        In local mode, paths are already local paths.

        Args:
            path: Container path to translate

        Returns:
            Local path string if translation exists, None if no local equivalent
        """
        if not self.runner:
            return path

        # In local mode, paths are already local paths
        if self.runner.is_local_mode():
            return path

        # In Docker mode, translate container paths to local paths
        path_manager = self.runner.path_manager

        container_to_local = {
            '/code/workspace/repo': str(path_manager.repo_dir),
            '/code/workspace/build': str(path_manager.build_dir),
            '/code/workspace/cache': str(path_manager.cache_dir),
        }

        for container_prefix, local_prefix in container_to_local.items():
            if path.startswith(container_prefix):
                if path == container_prefix:
                    return local_prefix
                else:
                    suffix = path[len(container_prefix) :]
                    if suffix.startswith('/'):
                        suffix = suffix[1:]
                    return str(Path(local_prefix) / suffix) if suffix else local_prefix

        # No local equivalent (e.g., container-only paths like /tmp, /usr/bin, etc.)
        return None

    def track_file(self, file_path: str) -> bool:
        """Track individual file for changes."""
        if not self.runner:
            self.set_error('Runner not initialized')
            return False
        return self.runner.track_file(file_path)

    def track_dir(self, dir_path: str, ext_filter: Optional[str] = None) -> bool:
        """Track directory with optional extension filter."""
        if not self.runner:
            self.set_error('Runner not initialized')
            return False
        return self.runner.track_dir(dir_path, ext_filter)

    def get_tracked_files(self, ext_filter: Optional[str] = None):
        """Get set of currently tracked files."""
        if not self.runner:
            return set()
        return self.runner.get_tracked_files(ext_filter)

    def get_diff(self, file_path: str) -> str:
        """Get unified diff for specific tracked file."""
        if not self.runner:
            return ''
        return self.runner.get_diff(file_path)

    def get_all_diffs(self, ext_filter: Optional[str] = None):
        """Get diffs for all tracked files with optional filtering."""
        if not self.runner:
            return {}
        return self.runner.get_all_diffs(ext_filter)

    def get_patch_dict(self):
        """Generate patch dictionary compatible with YAML export."""
        if not self.runner:
            return {'full': [], 'patch': []}
        return self.runner.get_patch_dict()

    def is_docker_mode(self) -> bool:
        """Check if running in Docker execution mode."""
        if not self.runner:
            return False
        return self.runner.is_docker_mode()

    def is_local_mode(self) -> bool:
        """Check if running in local execution mode."""
        if not self.runner:
            return False
        return self.runner.is_local_mode()

    def has_configuration(self) -> bool:
        """Check if Builder has loaded YAML configuration."""
        return self.has_config

    def get_config_path(self) -> Optional[str]:
        """Get path to loaded configuration file, or None if no config."""
        return self.config_path if self.has_config else None

    def create_file(self, file_path: str, content: str, encoding: str = 'utf-8') -> bool:
        """
        Create a file with the given content.

        This method delegates to the unified filesystem interface,
        replacing the need for separate create_file implementations.

        Args:
            file_path: Path where the file should be created
            content: Content to write to the file
            encoding: Text encoding to use (default: utf-8)

        Returns:
            True if file was created successfully, False otherwise
        """
        if not self.filesystem:
            self.set_error('FileSystem not initialized - call setup() first')
            return False

        return self.filesystem.write_file(file_path, content, encoding)

    def cleanup(self) -> None:
        """
        Clean up all resources including Runner.

        This method is idempotent and safe to call multiple times.
        """
        if self.runner:
            self.runner.cleanup()
        self.error_message = ''

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
            # Ignore any errors during destruction cleanup
            pass
