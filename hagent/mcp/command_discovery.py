#!/usr/bin/env python3
"""
Command Discovery Module for HAgent MCP Server

Simple file scanner that discovers mcp_*.py files in the hagent/hagent/ directory
and dynamically imports them for use by the MCP server.
"""

import os
import sys
import glob
import importlib.util
from typing import Dict, Any


def get_hagent_root_dir() -> str:
    """Get the hagent/ root directory path relative to this file"""
    # This file is in hagent/mcp/command_discovery.py
    # We want hagent/ directory to search for mcp_*.py files recursively
    current_dir = os.path.dirname(__file__)  # hagent/mcp/
    hagent_dir = os.path.dirname(current_dir)  # hagent/
    return hagent_dir


def discover_mcp_commands(hagent_root_dir: str = None) -> Dict[str, Any]:
    """
    Discover and load all mcp_*.py command modules from the hagent/ directory tree.

    Args:
        hagent_root_dir: Optional path to hagent/ root directory. If None, auto-detect.

    Returns:
        Dictionary mapping command names to loaded modules
    """
    if hagent_root_dir is None:
        hagent_root_dir = get_hagent_root_dir()

    commands = {}

    # Find all mcp_*.py files recursively in the hagent directory tree
    pattern = os.path.join(hagent_root_dir, '**', 'mcp_*.py')
    mcp_files = glob.glob(pattern, recursive=True)

    for file_path in mcp_files:
        try:
            # Extract command name from filename (remove mcp_ prefix and .py suffix)
            filename = os.path.basename(file_path)
            cmd_name = filename[4:-3]  # Remove 'mcp_' prefix and '.py' suffix

            # Load the module dynamically
            spec = importlib.util.spec_from_file_location(f'mcp_{cmd_name}', file_path)
            if spec and spec.loader:
                module = importlib.util.module_from_spec(spec)
                spec.loader.exec_module(module)

                # Verify the module has the required MCP interface
                if hasattr(module, 'get_mcp_schema') and hasattr(module, 'mcp_execute'):
                    commands[cmd_name] = module
                    print(f'Loaded MCP command: {cmd_name}', file=sys.stderr)
                else:
                    print(f'Warning: {filename} missing required MCP interface (get_mcp_schema, mcp_execute)', file=sys.stderr)

        except Exception as e:
            print(f'Error loading {file_path}: {e}', file=sys.stderr)

    return commands


def get_command_info(hagent_root_dir: str = None) -> Dict[str, Dict[str, Any]]:
    """
    Get information about available MCP commands without loading them.

    Args:
        hagent_root_dir: Optional path to hagent/ root directory. If None, auto-detect.

    Returns:
        Dictionary with command information
    """
    if hagent_root_dir is None:
        hagent_root_dir = get_hagent_root_dir()

    info = {}
    pattern = os.path.join(hagent_root_dir, '**', 'mcp_*.py')
    mcp_files = glob.glob(pattern, recursive=True)

    for file_path in mcp_files:
        filename = os.path.basename(file_path)
        cmd_name = filename[4:-3]  # Remove 'mcp_' prefix and '.py' suffix

        info[cmd_name] = {'file_path': file_path, 'filename': filename, 'exists': os.path.exists(file_path)}

    return info


if __name__ == '__main__':
    # Simple test when run directly
    hagent_root_dir = get_hagent_root_dir()
    print(f'Scanning for MCP commands in: {hagent_root_dir}')
    commands = discover_mcp_commands()
    print(f'Found {len(commands)} MCP commands: {list(commands.keys())}')
