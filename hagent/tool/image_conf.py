#!/usr/bin/env python3
"""
Image Configuration Tool for HAgent

Provides a simple API for reading YAML configuration files and executing
commands through file_manager instances. Designed for integration with
hagent/tool/file_manager.py for setting up tracked directories/files and environment.
"""

import os
import yaml
from typing import Dict, List, Optional, Tuple
from hagent.tool.tool import Tool
from hagent.tool.file_manager import File_manager


class Image_conf(Tool):
    """
    Tool for reading and managing YAML configuration files that define
    profiles with APIs, track_dir/track_file specifications, and environment setup.
    Works in conjunction with File_manager to execute commands.
    """

    def __init__(self):
        """Initialize the Image_conf tool."""
        super().__init__()
        self.config: Optional[Dict] = None
        self.file_manager: File_manager = None
        self.profiles: List[Dict] = []
        self.commands: Dict[str, Dict] = {}  # command_id -> command info

    def setup(self, file_manager: File_manager, yaml_filename: str) -> bool:
        """
        Setup the tool by loading YAML configuration through file_manager.

        Args:
            file_manager: Instance of hagent.tool.file_manager.File_manager
            yaml_filename: Container path to the YAML configuration file

        Returns:
            True if setup was successful, False otherwise.
        """
        if not file_manager:
            self.set_error('file_manager instance is required')
            return False

        self.file_manager = file_manager

        # Read YAML file content from container
        yaml_content = file_manager.get_file_content(yaml_filename)
        if not yaml_content:
            error_msg = file_manager.get_error()
            self.set_error(f"Failed to read YAML file '{yaml_filename}': {error_msg}")
            return False

        try:
            self.config = yaml.safe_load(yaml_content)

            if not self.config:
                self.set_error('YAML file is empty or invalid')
                return False

            self.profiles = self.config.get('profiles', [])

            if not self.profiles:
                self.set_error('No profiles found in YAML configuration')
                return False

            # Build command registry from all profiles
            self._build_command_registry()

            self._is_ready = True
            return True

        except yaml.YAMLError as e:
            self.set_error(f'YAML parsing error: {e}')
            return False
        except Exception as e:
            self.set_error(f'Failed to parse YAML content: {e}')
            return False

    def _build_command_registry(self) -> None:
        """Build a registry of all commands across all profiles with unique IDs."""
        self.commands = {}

        for profile in self.profiles:
            profile_name = profile.get('name', 'unknown')
            apis = profile.get('apis', [])

            for api in apis:
                api_name = api.get('name', 'unknown')
                command_id = f'{profile_name}.{api_name}'

                self.commands[command_id] = {
                    'profile_name': profile_name,
                    'api_name': api_name,
                    'command': api.get('command', ''),
                    'description': api.get('description', ''),
                    'profile': profile,
                }

    def get_commands(self) -> List[Dict[str, str]]:
        """
        Get list of all available commands with their IDs.

        Returns:
            List of dictionaries with command information
        """
        if not self._is_ready:
            return []

        result = []
        for command_id, cmd_info in self.commands.items():
            result.append(
                {
                    'id': command_id,
                    'profile': cmd_info['profile_name'],
                    'name': cmd_info['api_name'],
                    'command': cmd_info['command'],
                    'description': cmd_info['description'],
                }
            )

        return result

    def get_profiles(self) -> List[Dict]:
        """
        Get all profiles from the configuration.

        Returns:
            List of profile dictionaries
        """
        if not self._is_ready:
            return []
        return self.profiles

    def get_profile(self, profile_name: str) -> Optional[Dict]:
        """
        Get a specific profile by name.

        Args:
            profile_name: Name of the profile to retrieve

        Returns:
            Profile dictionary if found, None otherwise
        """
        if not self._is_ready:
            return None

        for profile in self.profiles:
            if profile.get('name') == profile_name:
                return profile

        self.set_error(f"Profile '{profile_name}' not found")
        return None

    def parse_track_directive(self, directive: str) -> Tuple[str, str, Optional[str]]:
        """
        Parse track_dir() or track_file() directives.

        Args:
            directive: The directive string to parse

        Returns:
            Tuple of (path, func_type, ext) where:
            - path: The directory or file path
            - func_type: "dir", "file", or "unknown"
            - ext: The extension filter (if specified)
        """
        if directive.startswith('track_dir('):
            func_type = 'dir'
            content = directive[10:-1]  # Remove "track_dir(" and ")"
        elif directive.startswith('track_file('):
            func_type = 'file'
            content = directive[11:-1]  # Remove "track_file(" and ")"
        else:
            return directive, 'unknown', None

        # Parse parameters
        parts = [p.strip().strip('\'"') for p in content.split(',')]
        path = parts[0]
        ext = None

        for part in parts[1:]:
            if part.startswith('ext='):
                ext = part[4:].strip('\'"')

        return path, func_type, ext

    def setup_tracking_for_profile(self, profile_name: str) -> bool:
        """
        Setup file tracking for a specific profile using file_manager.

        Args:
            profile_name: Name of the profile to setup tracking for

        Returns:
            True if setup was successful, False otherwise
        """
        if not self._is_ready or not self.file_manager:
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
                path, func_type, ext = self.parse_track_directive(source)
                if func_type == 'dir':
                    if not self.file_manager.track_dir(path, ext):
                        self.set_error(f'Failed to track source directory: {self.file_manager.get_error()}')
                        return False
                elif func_type == 'file':
                    if not self.file_manager.track_file(path):
                        self.set_error(f'Failed to track source file: {self.file_manager.get_error()}')
                        return False

            # Setup output tracking
            output = configuration.get('output')
            if output:
                path, func_type, ext = self.parse_track_directive(output)
                if func_type == 'dir':
                    if not self.file_manager.track_dir(path, ext):
                        self.set_error(f'Failed to track output directory: {self.file_manager.get_error()}')
                        return False
                elif func_type == 'file':
                    if not self.file_manager.track_file(path):
                        self.set_error(f'Failed to track output file: {self.file_manager.get_error()}')
                        return False

            # Setup environment variables
            env_vars = configuration.get('environment', {})
            if env_vars:
                expanded_vars = self._expand_environment_vars(env_vars)
                # Set environment variables in the current process (they'll be inherited by file_manager.run)
                for key, value in expanded_vars.items():
                    os.environ[key] = value

            return True

        except Exception as e:
            self.set_error(f"Failed to setup tracking for profile '{profile_name}': {e}")
            return False

    def _expand_environment_vars(self, env_vars: Dict[str, str]) -> Dict[str, str]:
        """
        Expand environment variables (similar to check_yaml.py).

        Args:
            env_vars: Dictionary of environment variables

        Returns:
            Dictionary of expanded environment variables
        """
        expanded_vars = {}

        for key, value in env_vars.items():
            # Handle PATH expansion
            if key == 'PATH' and value.startswith('$PATH:'):
                expanded_value = os.environ.get('PATH', '') + ':' + value[6:]
                expanded_vars[key] = expanded_value
            else:
                # Handle other variable expansions
                expanded_value = os.path.expandvars(value)
                expanded_vars[key] = expanded_value

        return expanded_vars

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
        if not self._is_ready or not self.file_manager:
            error_msg = 'Image_conf not properly initialized'
            self.set_error(error_msg)
            return -1, '', error_msg

        if command_id not in self.commands:
            error_msg = f"Command '{command_id}' not found"
            self.set_error(error_msg)
            return -1, '', error_msg

        cmd_info = self.commands[command_id]
        command = cmd_info['command']
        profile_name = cmd_info['profile_name']

        # Setup tracking for the profile if not already done
        # Note: This is idempotent - tracking the same path multiple times is safe
        if not self.setup_tracking_for_profile(profile_name):
            error_msg = f"Failed to setup tracking for profile '{profile_name}': {self.get_error()}"
            return -1, '', error_msg

        # Execute the command using file_manager
        try:
            return self.file_manager.run(command, container_path, quiet)
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
        if not self._is_ready:
            return None

        return self.commands.get(command_id)

    def get_profile_commands(self, profile_name: str) -> List[Dict[str, str]]:
        """
        Get all commands for a specific profile.

        Args:
            profile_name: Name of the profile

        Returns:
            List of command dictionaries for the profile
        """
        if not self._is_ready:
            return []

        result = []
        for command_id, cmd_info in self.commands.items():
            if cmd_info['profile_name'] == profile_name:
                result.append(
                    {
                        'id': command_id,
                        'name': cmd_info['api_name'],
                        'command': cmd_info['command'],
                        'description': cmd_info['description'],
                    }
                )

        return result

    def get_memory_requirement(self, profile_name: str) -> int:
        """
        Get the memory requirement for a profile in GB.

        Args:
            profile_name: Name of the profile

        Returns:
            Memory requirement in GB, 0 if not specified
        """
        profile = self.get_profile(profile_name)
        if not profile:
            return 0

        return profile.get('memory', 0)
