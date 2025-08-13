#!/usr/bin/env python3
"""
Image Configuration Tool for HAgent

Provides a simple API for reading YAML configuration files and executing
commands through file_manager instances. Designed for integration with
hagent/tool/file_manager.py for setting up tracked directories/files and environment.

Now uses the shared HagentBuildCore for configuration management.
"""

import os
from typing import Dict, List, Optional, Tuple
from hagent.tool.tool import Tool
from hagent.tool.file_manager import File_manager
from hagent.core.hagent_build import HagentBuildCore


class DockerExecutionStrategy:
    """Execution strategy that runs commands via File_manager (Docker)."""

    def __init__(self, file_manager: File_manager):
        self.file_manager = file_manager

    def run(self, command: str, cwd: str, env: Dict[str, str], quiet: bool = False) -> Tuple[int, str, str]:
        """
        Execute command using File_manager.run.

        Args:
            command: The command to execute
            cwd: Working directory (absolute path, will be converted for container)
            env: Environment variables (set in the host environment)
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr)
        """
        # Set environment variables in the current process
        # (they'll be inherited by file_manager.run)
        old_env = {}
        for key, value in env.items():
            old_env[key] = os.environ.get(key)
            os.environ[key] = value

        try:
            return self.file_manager.run(command, cwd, quiet)
        finally:
            # Restore previous environment
            for key, old_value in old_env.items():
                if old_value is None:
                    os.environ.pop(key, None)
                else:
                    os.environ[key] = old_value


class Image_conf(Tool):
    """
    Tool for reading and managing YAML configuration files that define
    profiles with APIs, track_dir/track_file specifications, and environment setup.
    Works in conjunction with File_manager to execute commands.
    """

    def __init__(self):
        """Initialize the Image_conf tool."""
        super().__init__()
        self.core: Optional[HagentBuildCore] = None
        self.file_manager: Optional[File_manager] = None

    def setup(self, file_manager: File_manager, yaml_filename: Optional[str] = None) -> bool:
        """
        Setup the tool by loading YAML configuration through file_manager.

        Args:
            file_manager: Instance of hagent.tool.file_manager.File_manager
            yaml_filename: Container path to the YAML configuration file (optional, will search if not provided)

        Returns:
            True if setup was successful, False otherwise.
        """
        if not file_manager:
            self.set_error('file_manager instance is required')
            return False

        self.file_manager = file_manager

        # Find YAML configuration file if not provided
        if yaml_filename is None:
            for container_path in HagentBuildCore.possible_config_paths():
                yaml_content = file_manager.get_file_content(container_path)
                if yaml_content:
                    yaml_filename = container_path
                    break
            else:
                self.set_error('No hagent.yaml found in container search paths')
                return False
        else:
            # Read specified YAML file content from container
            yaml_content = file_manager.get_file_content(yaml_filename)
            if not yaml_content:
                error_msg = file_manager.get_error()
                self.set_error(f"Failed to read YAML file '{yaml_filename}': {error_msg}")
                return False

        try:
            # Create a temporary YAML file on the host for HagentBuildCore to read
            import tempfile
            from pathlib import Path

            with tempfile.NamedTemporaryFile(mode='w', suffix='.yaml', delete=False) as f:
                f.write(yaml_content)
                temp_yaml_path = f.name

            try:
                # Initialize the core with Docker execution strategy
                execution_strategy = DockerExecutionStrategy(file_manager)
                self.core = HagentBuildCore(temp_yaml_path, execution_strategy)

                # Override paths for Docker environment
                # Check for standard Docker paths first
                if file_manager.path_exists('/code/workspace/repo'):
                    self.core.repo_dir = Path('/code/workspace/repo')
                    if file_manager.path_exists('/code/workspace/build'):
                        self.core.build_base = Path('/code/workspace/build')
                    else:
                        self.core.build_base = Path('/code/workspace/repo/build')
                else:
                    # Fallback: use yaml location as repo dir
                    yaml_dir = Path(yaml_filename).parent if yaml_filename else Path('.')
                    if file_manager.path_exists(str(yaml_dir / '../build')):
                        self.core.repo_dir = yaml_dir
                        self.core.build_base = yaml_dir / '../build'
                    elif file_manager.path_exists(str(yaml_dir / 'build')):
                        self.core.repo_dir = yaml_dir
                        self.core.build_base = yaml_dir / 'build'
                    else:
                        self.set_error(
                            'Docker container should have known repo and build directories. '
                            'Expected /code/workspace/repo and /code/workspace/build, or '
                            'build directory relative to hagent.yaml location.'
                        )
                        return False

                self._is_ready = True
                return True

            finally:
                # Clean up temporary file
                os.unlink(temp_yaml_path)

        except Exception as e:
            self.set_error(f'Failed to setup HagentBuildCore: {e}')
            return False

    def get_commands(self) -> List[Dict[str, str]]:
        """
        Get list of all available commands with their IDs.

        Returns:
            List of dictionaries with command information
        """
        if not self._is_ready or not self.core:
            return []

        result = []
        for profile in self.core.get_all_profiles():
            profile_name = profile.get('name', 'unknown')
            profile_description = profile.get('description', '')

            for api in self.core.get_profile_commands(profile):
                api_name = api.get('name', 'unknown')
                command_id = f'{profile_name}.{api_name}'

                result.append(
                    {
                        'id': command_id,
                        'profile_name': profile_name,
                        'profile_description': profile_description,
                        'api_name': api_name,
                        'api_command': api.get('command', ''),
                        'api_description': api.get('description', ''),
                    }
                )

        return result

    def get_profiles(self) -> List[Dict]:
        """
        Get all profiles from the configuration.

        Returns:
            List of profile dictionaries
        """
        if not self._is_ready or not self.core:
            return []
        return self.core.get_all_profiles()

    def get_profile(self, profile_name: str) -> Optional[Dict]:
        """
        Get a specific profile by name.

        Args:
            profile_name: Name of the profile to retrieve

        Returns:
            Profile dictionary if found, None otherwise
        """
        if not self._is_ready or not self.core:
            return None

        try:
            return self.core.select_profile(exact_name=profile_name)
        except ValueError:
            self.set_error(f"Profile '{profile_name}' not found")
            return None

    def parse_track_directive(self, directive: str) -> Tuple[str, str, Optional[str]]:
        """
        Parse track_repo_dir() or track_build_dir() directives.

        Args:
            directive: The directive string to parse

        Returns:
            Tuple of (path, func_type, ext) where:
            - path: The directory or file path (relative for compatibility)
            - func_type: "repo_dir", "build_dir", or "unknown"
            - ext: The extension filter (if specified)
        """
        if not self.core:
            return directive, 'unknown', None

        try:
            path, func_type, ext = self.core.parse_track_directive(directive)
            return path, func_type, ext
        except Exception:
            return directive, 'unknown', None

    def setup_tracking_for_profile(self, profile_name: str) -> bool:
        """
        Setup file tracking for a specific profile using file_manager.

        Args:
            profile_name: Name of the profile to setup tracking for

        Returns:
            True if setup was successful, False otherwise
        """
        if not self._is_ready or not self.file_manager or not self.core:
            self.set_error('Image_conf not properly initialized')
            return False

        profile = self.get_profile(profile_name)
        if not profile:
            return False

        try:
            configuration = profile.get('configuration', {})

            # Setup source tracking
            source = configuration.get('source')
            if source:
                path, func_type, ext = self.core.parse_track_directive(source)
                if func_type in ('repo_dir', 'build_dir'):
                    if not self.file_manager.track_dir(path, ext):
                        self.set_error(f'Failed to track source directory: {self.file_manager.get_error()}')
                        return False

            # Setup output tracking
            output = configuration.get('output')
            if output:
                path, func_type, ext = self.core.parse_track_directive(output)
                if func_type in ('repo_dir', 'build_dir'):
                    if not self.file_manager.track_dir(path, ext):
                        self.set_error(f'Failed to track output directory: {self.file_manager.get_error()}')
                        return False

            # Environment variables are now handled by the execution strategy
            return True

        except Exception as e:
            self.set_error(f"Failed to setup tracking for profile '{profile_name}': {e}")
            return False

    def run_command(self, command_id: str, container_path: Optional[str] = '.', quiet: bool = False) -> Tuple[int, str, str]:
        """
        Execute a command by its ID using the file_manager.

        Args:
            command_id: ID of the command to execute (format: "profile_name.api_name")
            container_path: Optional working directory for the command
            quiet: Whether to run in quiet mode

        Returns:
            Tuple of (exit_code, stdout, stderr) from file_manager.run
        """
        if not self._is_ready or not self.file_manager or not self.core:
            error_msg = 'Image_conf not properly initialized'
            self.set_error(error_msg)
            return -1, '', error_msg

        # Parse command_id to extract profile_name and api_name
        try:
            profile_name, api_name = command_id.split('.', 1)
        except ValueError:
            error_msg = f"Invalid command ID format '{command_id}'. Expected 'profile_name.api_name'"
            self.set_error(error_msg)
            return -1, '', error_msg

        # Verify the command exists
        try:
            profile = self.core.select_profile(exact_name=profile_name)
            if not self.core.find_command_in_profile(profile, api_name):
                error_msg = f"Command '{command_id}' not found"
                self.set_error(error_msg)
                return -1, '', error_msg
        except ValueError as e:
            error_msg = f"Command '{command_id}' not found: {e}"
            self.set_error(error_msg)
            return -1, '', error_msg

        # Setup tracking for the profile if not already done
        # Note: This is idempotent - tracking the same path multiple times is safe
        if not self.setup_tracking_for_profile(profile_name):
            error_msg = f"Failed to setup tracking for profile '{profile_name}': {self.get_error()}"
            return -1, '', error_msg

        # Use the core to execute the command
        try:
            exit_code, stdout, stderr = self.core.execute_command(
                profile=profile,
                command_name=api_name,
                build_dir=None,  # Use default
                dry_run=False,
                quiet=quiet,
            )
            return exit_code, stdout, stderr

        except Exception as e:
            error_msg = f"Failed to execute command '{command_id}': {e}"
            self.set_error(error_msg)
            return -1, '', error_msg

    def get_command_info(self, command_id: str) -> Optional[Dict]:
        """
        Get detailed information about a specific command.

        Args:
            command_id: ID of the command

        Returns:
            Dictionary with command information, or None if not found
        """
        if not self._is_ready or not self.core:
            return None

        # Parse command_id to extract profile_name and api_name
        try:
            profile_name, api_name = command_id.split('.', 1)
        except ValueError:
            return None

        try:
            profile = self.core.select_profile(exact_name=profile_name)
            api = self.core.find_command_in_profile(profile, api_name)
            if not api:
                return None

            return {
                'profile_name': profile_name,
                'profile_description': profile.get('description', ''),
                'api_name': api_name,
                'api_command': api.get('command', ''),
                'api_description': api.get('description', ''),
                'profile': profile,
            }
        except ValueError:
            return None

    def get_profile_commands(self, profile_name: str) -> List[Dict[str, str]]:
        """
        Get all commands for a specific profile.

        Args:
            profile_name: Name of the profile

        Returns:
            List of command dictionaries for the profile
        """
        if not self._is_ready or not self.core:
            return []

        try:
            profile = self.core.select_profile(exact_name=profile_name)
            result = []

            for api in self.core.get_profile_commands(profile):
                api_name = api.get('name', 'unknown')
                command_id = f'{profile_name}.{api_name}'

                result.append(
                    {
                        'id': command_id,
                        'api_name': api_name,
                        'api_command': api.get('command', ''),
                        'api_description': api.get('description', ''),
                    }
                )

            return result
        except ValueError:
            return []

    def get_command(self, profile_name: str, api_name: str) -> Optional[Dict[str, str]]:
        """
        Get a specific command by profile and API names.

        Args:
            profile_name: Name of the profile
            api_name: Name of the API/command

        Returns:
            Command dictionary if found, None otherwise
        """
        if not self._is_ready or not self.core:
            return None

        try:
            profile = self.core.select_profile(exact_name=profile_name)
            api = self.core.find_command_in_profile(profile, api_name)
            if not api:
                return None

            command_id = f'{profile_name}.{api_name}'
            return {
                'id': command_id,
                'profile_name': profile_name,
                'profile_description': profile.get('description', ''),
                'api_name': api_name,
                'api_command': api.get('command', ''),
                'api_description': api.get('description', ''),
            }
        except ValueError:
            return None

    def get_memory_requirement(self, profile_name: str) -> int:
        """
        Get the memory requirement for a profile in GB.

        Args:
            profile_name: Name of the profile

        Returns:
            Memory requirement in GB, 0 if not specified
        """
        if not self._is_ready or not self.core:
            return 0

        try:
            profile = self.core.select_profile(exact_name=profile_name)
            return self.core.get_memory_requirement(profile)
        except ValueError:
            return 0
