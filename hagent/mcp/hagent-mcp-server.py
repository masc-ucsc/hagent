#!/usr/bin/env python3
"""
HAgent MCP Server - MCP server implementation using FastMCP

This is a FastMCP-based server that exposes HAgent tools and utilities.
"""

from __future__ import annotations

import sys
import os
import logging
import subprocess
from typing import Dict, Any, Optional
from pathlib import Path

# Add the hagent root to Python path for imports
HAGENT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, HAGENT_ROOT)

# Import FastMCP
from mcp.server.fastmcp import FastMCP

# Import command discovery
from hagent.mcp.command_discovery import discover_mcp_commands

# Setup logging
def setup_logging():
    """Setup logging for MCP server debugging"""
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        handlers=[logging.FileHandler('/tmp/hagent-mcp-server.log'), logging.StreamHandler(sys.stderr)],
    )
    return logging.getLogger('hagent-mcp-server')

# Initialize FastMCP and logger
logger = setup_logging()
mcp = FastMCP("HAgentMCPServer")

# Forward declaration of functions
register_mcp_module = None

# Function to register MCP modules as FastMCP tools
def register_mcp_module_impl(module, mcp_instance):
    """Register an MCP module as a FastMCP tool"""
    try:
        if not hasattr(module, 'get_mcp_schema') or not hasattr(module, 'mcp_execute'):
            logger.warning(f"Module {module.__name__} missing required MCP interface")
            return False
        
        schema = module.get_mcp_schema()
        tool_name = schema.get('name')
        
        if not tool_name:
            logger.warning(f"Module {module.__name__} schema missing 'name' field")
            return False
        
        # Ensure consistent naming convention (all tools use hagent. prefix)
        if not tool_name.startswith('hagent.'):
            # If it starts with hagent_ (old style), replace with hagent.
            if tool_name.startswith('hagent_'):
                new_tool_name = 'hagent.' + tool_name[7:]  # Replace hagent_ with hagent.
                logger.info(f"Standardizing tool name from {tool_name} to {new_tool_name}")
                tool_name = new_tool_name
        
        logger.info(f"Registering MCP module as tool: {tool_name}")
        
        # Create a wrapper function that calls mcp_execute
        def tool_wrapper(**kwargs):
            return module.mcp_execute(kwargs)
        
        # Set function name and docstring
        tool_wrapper.__name__ = tool_name
        tool_wrapper.__doc__ = schema.get('description', f"HAgent MCP tool: {tool_name}")
        
        # Register with FastMCP
        mcp_instance.tool(name=tool_name)(tool_wrapper)
        return True
    except Exception as e:
        logger.error(f"Error registering MCP module: {e}")
        return False

# Set the implementation
register_mcp_module = register_mcp_module_impl

# Function to discover and register MCP modules
def discover_and_register_mcp_modules(mcp_instance):
    """Discover all available MCP modules and register them as FastMCP tools"""
    logger.info("Discovering and registering MCP modules")
    registered_tools = []
    
    try:
        # Discover available modules
        discovered_modules = discover_mcp_commands()
        module_names = list(discovered_modules.keys())
        logger.info(f"Discovered {len(discovered_modules)} MCP modules: {module_names}")
        
        # Register each discovered module
        for module_name, module in discovered_modules.items():
            try:
                if register_mcp_module(module, mcp_instance):
                    # Get the actual tool name from schema
                    schema = module.get_mcp_schema()
                    tool_name = schema.get('name', '')
                    
                    # Standardize tool name if needed
                    if tool_name.startswith('hagent_'):
                        tool_name = 'hagent.' + tool_name[7:]  # Replace hagent_ with hagent.
                    
                    registered_tools.append(tool_name)
            except Exception as e:
                logger.error(f"Error registering {module_name} module: {e}")
        
        logger.info(f"Successfully registered {len(registered_tools)} MCP tools: {registered_tools}")
        return registered_tools
    
    except Exception as e:
        logger.error(f"Error discovering MCP modules: {e}")
        print(f"Error discovering MCP modules: {e}", file=sys.stderr)
        return []

# Discover and register available MCP modules
registered_mcp_modules = discover_and_register_mcp_modules(mcp)


class EnvironmentSetup:
    """Environment setup utilities for HAgent"""
    
    @staticmethod
    def setup_environment():
        """Setup proper HAgent environment variables with intelligent defaults"""
        logger.info('Setting up HAgent environment variables')
        
        # First check we're in a safe location
        EnvironmentSetup._check_safe_working_directory()
        
        # Get or set HAGENT_ROOT
        if 'HAGENT_ROOT' not in os.environ:
            os.environ['HAGENT_ROOT'] = HAGENT_ROOT
            logger.info(f'Set HAGENT_ROOT={HAGENT_ROOT}')
        
        # Setup HAGENT_DOCKER with default
        if 'HAGENT_DOCKER' not in os.environ:
            os.environ['HAGENT_DOCKER'] = 'mascucsc/hagent-builder:2025.08'
            logger.info('Set HAGENT_DOCKER=mascucsc/hagent-builder:2025.08')
        
        # Setup HAGENT_REPO_DIR with intelligent fallbacks
        if 'HAGENT_REPO_DIR' not in os.environ:
            EnvironmentSetup._setup_repo_directory()
        
        # Setup HAGENT_BUILD_DIR (relative to repo)
        if 'HAGENT_BUILD_DIR' not in os.environ:
            os.environ['HAGENT_BUILD_DIR'] = './build'
            logger.info('Set HAGENT_BUILD_DIR=./build')
        
        # Setup HAGENT_CACHE_DIR (relative to repo)
        if 'HAGENT_CACHE_DIR' not in os.environ:
            os.environ['HAGENT_CACHE_DIR'] = './cache'
            logger.info('Set HAGENT_CACHE_DIR=./cache')
        
        # Log the final environment setup
        logger.info('Environment setup complete:')
        for var in ['HAGENT_ROOT', 'HAGENT_DOCKER', 'HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR']:
            logger.info(f'  {var}={os.environ.get(var, "NOT_SET")}')
        
        return True

    @staticmethod
    def _check_safe_working_directory():
        """Ensure we're not running inside core hagent source directories to avoid pollution"""
        current_dir = Path(os.getcwd()).resolve()
        hagent_root = Path(HAGENT_ROOT).resolve()
        
        # Define specific directories to avoid (source code areas)
        # Note: this does NOT exclude the root directory itself, only specific subdirectories
        unsafe_dirs = [
            hagent_root / 'hagent',  # Core hagent package
            hagent_root / 'scripts',  # Scripts directory
            hagent_root / 'docs',  # Documentation
            hagent_root / '.git',  # Git directory
        ]

        # Check if current directory is inside one of the unsafe directories
        for unsafe_dir in unsafe_dirs:
            try:
                current_dir.relative_to(unsafe_dir)
                # If we get here, current_dir is inside an unsafe directory
                logger.error('SAFETY ERROR: Running MCP server inside protected hagent directory!')
                logger.error(f'Current dir: {current_dir}')
                logger.error(f'Protected dir: {unsafe_dir}')
                logger.error('This would pollute the source code. Please run from a clean directory.')
                logger.error(f'Recommended: cd to {hagent_root}/potato or {hagent_root}/output/local')

                # Print to stderr for immediate visibility
                print('ERROR: Running MCP server inside protected hagent directory!', file=sys.stderr)
                print(f'Current: {current_dir}', file=sys.stderr)
                print(f'Protected: {unsafe_dir}', file=sys.stderr)
                print(f'Please run from: {hagent_root}/potato or {hagent_root}/output/local', file=sys.stderr)

                sys.exit(1)
            except ValueError:
                # current_dir is not inside this unsafe_dir, continue checking
                continue

        # If we get here, current directory is safe
        logger.info(f'Safe working directory: {current_dir}')

    @staticmethod
    def _setup_repo_directory():
        """Setup HAGENT_REPO_DIR with intelligent defaults and repo extraction"""

        # Check if hagent.yaml exists in current directory
        if os.path.exists('hagent.yaml'):
            os.environ['HAGENT_REPO_DIR'] = os.getcwd()
            logger.info(f'Found hagent.yaml in current directory, set HAGENT_REPO_DIR={os.getcwd()}')
            return

        # Try standard locations
        hagent_root = os.environ['HAGENT_ROOT']
        candidate_dirs = [
            os.path.join(hagent_root, 'output', 'local', 'repo'),
            os.path.join(hagent_root, 'test', 'local', 'repo'),
        ]

        for repo_dir in candidate_dirs:
            if os.path.exists(repo_dir) and os.path.exists(os.path.join(repo_dir, 'hagent.yaml')):
                os.environ['HAGENT_REPO_DIR'] = repo_dir
                logger.info(f'Found existing repo at {repo_dir}')
                return

        # Setup repo directory (use output/local/repo as primary)
        repo_dir = candidate_dirs[0]
        EnvironmentSetup._setup_local_directory(repo_dir)
        os.environ['HAGENT_REPO_DIR'] = repo_dir

    @staticmethod
    def _setup_local_directory(repo_dir):
        """Setup local directory structure similar to test_container_manager.py"""
        repo_path = Path(repo_dir)
        local_dir = repo_path.parent
        build_dir = local_dir / 'build'
        cache_dir = local_dir / 'cache'

        # Create local directory if it doesn't exist
        if not local_dir.exists():
            logger.info(f'Creating {local_dir} directory...')
            local_dir.mkdir(parents=True, exist_ok=True)

        # Setup repo directory with git clone if it doesn't exist or is empty
        if not repo_path.exists() or not any(repo_path.iterdir()):
            logger.warning(
                f'HAGENT_REPO_DIR not set, extracting to {repo_path} the repo from docker. '
                f'If hagent.yaml exists in the current directory, no need to copy the repo.'
            )

            # Clone the repository
            try:
                subprocess.run(
                    ['git', 'clone', 'https://github.com/masc-ucsc/simplechisel.git', str(repo_path)],
                    check=True,
                    capture_output=True,
                    text=True,
                )
                logger.info(f'Successfully cloned simplechisel to {repo_path}')
            except subprocess.CalledProcessError as e:
                logger.warning(f'Failed to clone repository: {e}')
                # Create a basic directory structure as fallback
                repo_path.mkdir(exist_ok=True)
                (repo_path / 'README.md').write_text('# Test Repository\n')

        # Create build directory
        if not build_dir.exists():
            logger.info(f'Creating {build_dir} directory...')
            build_dir.mkdir(exist_ok=True)

        # Create cache directory
        if not cache_dir.exists():
            logger.info(f'Creating {cache_dir} directory...')
            cache_dir.mkdir(exist_ok=True)


# This function is now defined earlier in the file


# MCP modules are registered by discover_and_register_mcp_modules above


# Define FastMCP tools

@mcp.tool(name="hagent.info")
def hagent_info() -> Dict[str, str]:
    """
    Return HAgent environment information
    
    Returns:
        Dictionary with environment variables and settings
    """
    # Ensure environment is set up
    EnvironmentSetup.setup_environment()
    
    # Get environment variables
    env_vars = {
        'HAGENT_ROOT': os.environ.get('HAGENT_ROOT', 'NOT_SET'),
        'HAGENT_DOCKER': os.environ.get('HAGENT_DOCKER', 'NOT_SET'),
        'HAGENT_REPO_DIR': os.environ.get('HAGENT_REPO_DIR', 'NOT_SET'),
        'HAGENT_BUILD_DIR': os.environ.get('HAGENT_BUILD_DIR', 'NOT_SET'),
        'HAGENT_CACHE_DIR': os.environ.get('HAGENT_CACHE_DIR', 'NOT_SET'),
        'working_directory': os.getcwd()
    }
    
    return env_vars


@mcp.tool(name="hagent.setup_environment")
def setup_hagent_environment() -> Dict[str, Any]:
    """
    Setup HAgent environment variables with intelligent defaults
    
    Returns:
        Dictionary with environment setup results
    """
    try:
        EnvironmentSetup.setup_environment()
        return {
            'success': True,
            'environment': {
                'HAGENT_ROOT': os.environ.get('HAGENT_ROOT', 'NOT_SET'),
                'HAGENT_DOCKER': os.environ.get('HAGENT_DOCKER', 'NOT_SET'),
                'HAGENT_REPO_DIR': os.environ.get('HAGENT_REPO_DIR', 'NOT_SET'),
                'HAGENT_BUILD_DIR': os.environ.get('HAGENT_BUILD_DIR', 'NOT_SET'),
                'HAGENT_CACHE_DIR': os.environ.get('HAGENT_CACHE_DIR', 'NOT_SET')
            }
        }
    except Exception as e:
        return {'success': False, 'error': str(e)}


# Setup environment when the module is imported
try:
    # Set up environment when the module is imported
    EnvironmentSetup.setup_environment()
    logger.info("Environment automatically set up on import")
except Exception as e:
    logger.error(f"Error setting up environment: {e}")
    print(f"Error setting up environment: {e}", file=sys.stderr)


if __name__ == "__main__":
    # Run this file as an MCP stdio server
    logger.info("Starting HAgent MCP Server with FastMCP")
    print("HAgent MCP Server running with FastMCP. Use 'uv run python hagent-mcp-server.py'", file=sys.stderr)
    mcp.run(transport="stdio")