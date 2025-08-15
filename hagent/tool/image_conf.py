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
from hagent.inou.executor import DockerExecutor


class DockerExecutionStrategy:
    """
    DEPRECATED: Execution strategy that runs commands via File_manager (Docker).
    Use hagent.inou.executor.DockerExecutor instead.
    """

    def __init__(self, file_manager: File_manager):
        """
        Initialize with File_manager instance.

        This is a deprecated wrapper around DockerExecutor for backward compatibility.
        """
        self.file_manager = file_manager
        # Create new DockerExecutor instance to delegate to
        self._executor = DockerExecutor(file_manager)



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





