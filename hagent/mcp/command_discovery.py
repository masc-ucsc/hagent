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
                    # Don't print to stderr - breaks MCP stdio protocol
                    # Logging happens in hagent-mcp-server.py instead
                else:
                    # Skip files without MCP interface (like mcp_message_handlers.py)
                    pass

        except Exception:
            # Don't print to stderr - breaks MCP stdio protocol
            # Log via hagent-mcp-server.py if needed
            pass

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


def get_command_schemas_subprocess(hagent_root_dir: str = None) -> Dict[str, Dict[str, Any]]:
    """
    Get MCP schemas by calling each command's --schema option via subprocess.

    Args:
        hagent_root_dir: Optional path to hagent/ root directory. If None, auto-detect.

    Returns:
        Dictionary mapping command names to their MCP schemas
    """
    import subprocess
    import json

    if hagent_root_dir is None:
        hagent_root_dir = get_hagent_root_dir()

    schemas = {}

    # Find all mcp_*.py files
    pattern = os.path.join(hagent_root_dir, '**', 'mcp_*.py')
    mcp_files = glob.glob(pattern, recursive=True)

    for file_path in mcp_files:
        try:
            filename = os.path.basename(file_path)
            cmd_name = filename[4:-3]  # Remove 'mcp_' prefix and '.py' suffix

            # Call the command with --schema option
            result = subprocess.run([sys.executable, file_path, '--schema'], capture_output=True, text=True, timeout=30)

            if result.returncode == 0:
                schema = json.loads(result.stdout)
                schemas[cmd_name] = schema
                # Don't print to stderr - breaks MCP stdio protocol
            else:
                # Don't print to stderr - breaks MCP stdio protocol
                pass

        except subprocess.TimeoutExpired:
            # Don't print to stderr - breaks MCP stdio protocol
            pass
        except json.JSONDecodeError:
            # Don't print to stderr - breaks MCP stdio protocol
            pass
        except Exception:
            # Don't print to stderr - breaks MCP stdio protocol
            pass

    return schemas


def get_command_schemas(hagent_root_dir: str = None) -> Dict[str, Dict[str, Any]]:
    """
    Get MCP schemas for all discovered commands by calling their get_mcp_schema function.

    Args:
        hagent_root_dir: Optional path to hagent/ root directory. If None, auto-detect.

    Returns:
        Dictionary mapping command names to their MCP schemas
    """
    if hagent_root_dir is None:
        hagent_root_dir = get_hagent_root_dir()

    schemas = {}
    commands = discover_mcp_commands(hagent_root_dir)

    for cmd_name, module in commands.items():
        try:
            if hasattr(module, 'get_mcp_schema'):
                schema = module.get_mcp_schema()
                schemas[cmd_name] = schema
                # Don't print to stderr - breaks MCP stdio protocol
            else:
                # Don't print to stderr - breaks MCP stdio protocol
                pass
        except Exception:
            # Don't print to stderr - breaks MCP stdio protocol
            pass

    return schemas


def get_command_capabilities(hagent_root_dir: str = None) -> Dict[str, Any]:
    """
    Get detailed capabilities for all MCP commands including available options.

    For commands like mcp_build.py, this will call --list to get available profiles/APIs.

    Args:
        hagent_root_dir: Optional path to hagent/ root directory. If None, auto-detect.

    Returns:
        Dictionary with command capabilities and available options
    """
    if hagent_root_dir is None:
        hagent_root_dir = get_hagent_root_dir()

    capabilities = {}
    commands = discover_mcp_commands(hagent_root_dir)

    for cmd_name, module in commands.items():
        try:
            schema = module.get_mcp_schema() if hasattr(module, 'get_mcp_schema') else {}
            capabilities[cmd_name] = {
                'schema': schema,
                'name': schema.get('name', f'hagent_{cmd_name}'),
                'description': schema.get('description', ''),
                'parameters': schema.get('inputSchema', {}).get('properties', {}),
                'required': schema.get('inputSchema', {}).get('required', []),
            }

            # For build command, try to get available profiles/APIs
            if cmd_name == 'build' and hasattr(module, 'mcp_execute'):
                try:
                    # Get list of profiles
                    profiles_result = module.mcp_execute({'list': True})
                    if profiles_result.get('success'):
                        capabilities[cmd_name]['available_profiles'] = profiles_result.get('stdout', '')
                except Exception:
                    # Don't print to stderr - breaks MCP stdio protocol
                    pass

        except Exception:
            # Don't print to stderr - breaks MCP stdio protocol
            pass

    return capabilities


if __name__ == '__main__':
    # Simple test when run directly
    import argparse

    parser = argparse.ArgumentParser(description='HAgent MCP Command Discovery')
    parser.add_argument('--schemas', action='store_true', help='Show detailed schemas for all commands')
    parser.add_argument('--subprocess', action='store_true', help='Get schemas via subprocess --schema calls')
    parser.add_argument('--capabilities', action='store_true', help='Show capabilities including available options')
    args = parser.parse_args()

    hagent_root_dir = get_hagent_root_dir()
    print(f'Scanning for MCP commands in: {hagent_root_dir}')

    if args.schemas:
        if args.subprocess:
            schemas = get_command_schemas_subprocess()
            print(f'Found {len(schemas)} MCP command schemas via subprocess:')
        else:
            schemas = get_command_schemas()
            print(f'Found {len(schemas)} MCP command schemas:')

        for cmd_name, schema in schemas.items():
            print(f'\n=== {cmd_name} ===')
            print(f'Name: {schema.get("name", "unnamed")}')
            print(f'Description: {schema.get("description", "No description")}')
            properties = schema.get('inputSchema', {}).get('properties', {})
            if properties:
                print('Parameters:')
                for param_name, param_info in properties.items():
                    print(f'  - {param_name}: {param_info.get("description", param_info.get("type", "unknown"))}')

    elif args.capabilities:
        capabilities = get_command_capabilities()
        print(f'Found {len(capabilities)} MCP command capabilities:')
        for cmd_name, cap in capabilities.items():
            print(f'\n=== {cmd_name} ===')
            print(f'Name: {cap.get("name", "unnamed")}')
            print(f'Description: {cap.get("description", "No description")}')
            if 'available_profiles' in cap:
                print('Available Profiles:')
                print(
                    cap['available_profiles'][:500] + '...' if len(cap['available_profiles']) > 500 else cap['available_profiles']
                )

    else:
        commands = discover_mcp_commands()
        print(f'Found {len(commands)} MCP commands: {list(commands.keys())}')
