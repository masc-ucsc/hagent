#!/usr/bin/env python3
"""
HAgent MCP Server - MCP server implementation using FastMCP

This is a FastMCP-based server that exposes HAgent tools and utilities.
"""

from __future__ import annotations

import sys
import os
import logging
import json
import datetime
import subprocess
from typing import Dict, Any
from pathlib import Path
from functools import wraps

# Add the hagent root to Python path for imports
HAGENT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, HAGENT_ROOT)

# Import FastMCP
from mcp.server.fastmcp import FastMCP

# Import command discovery
from hagent.mcp.command_discovery import discover_mcp_commands


# Transaction Logger
class TransactionLogger:
    """Logger for MCP transactions that creates command-specific log files"""

    def __init__(self, cache_dir: str = None):
        """Initialize the transaction logger with the given cache directory"""
        self.cache_dir = cache_dir or os.environ.get('HAGENT_CACHE_DIR', './cache')
        self.log_dir = Path(self.cache_dir) / 'mcp'
        self.log_dir.mkdir(parents=True, exist_ok=True)
        self.loggers = {}

    def get_logger(self, command_name: str) -> logging.Logger:
        """Get or create a logger for the specified command"""
        if command_name in self.loggers:
            return self.loggers[command_name]

        # Clean command_name for use in filename
        safe_name = command_name.replace('.', '_')
        log_file = self.log_dir / f'{safe_name}.log'

        # Create a new logger
        logger = logging.getLogger(f'hagent-mcp-{safe_name}')
        logger.setLevel(logging.DEBUG)

        # Clear any existing handlers
        logger.handlers = []

        # Add file handler
        handler = logging.FileHandler(log_file)
        handler.setLevel(logging.DEBUG)
        formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
        handler.setFormatter(formatter)
        logger.addHandler(handler)

        # Store and return logger
        self.loggers[command_name] = logger
        return logger

    def log_transaction(self, command_name: str, request: Any, response: Any):
        """Log a transaction for the given command"""
        logger = self.get_logger(command_name)
        timestamp = datetime.datetime.now().isoformat()

        logger.info(f'--- TRANSACTION BEGIN [{timestamp}] ---')
        logger.info(f'REQUEST: {json.dumps(request, indent=2, default=str)}')
        logger.info(f'RESPONSE: {json.dumps(response, indent=2, default=str)}')
        logger.info(f'--- TRANSACTION END [{timestamp}] ---\n')


# Setup logging
def setup_logging():
    """Setup logging for MCP server debugging"""
    logging.basicConfig(
        level=logging.INFO,
        format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
        handlers=[logging.FileHandler('/tmp/hagent-mcp-server.log'), logging.StreamHandler(sys.stderr)],
    )
    return logging.getLogger('hagent-mcp-server')


# Initialize FastMCP and loggers
logger = setup_logging()

# Create transaction logger
default_cache_dir = os.environ.get('HAGENT_CACHE_DIR', './cache')
txn_logger = TransactionLogger(default_cache_dir)

# Create FastMCP instance with request/response logging
mcp = FastMCP('HAgentMCPServer')


# Create wrapper for tool functions to log transactions
def log_transactions(func):
    """Decorator to log tool transactions"""

    @wraps(func)
    def wrapper(*args, **kwargs):
        command_name = getattr(func, '__name__', 'unknown')
        request = {'name': command_name, 'args': args, 'kwargs': kwargs}

        try:
            result = func(*args, **kwargs)
            txn_logger.log_transaction(command_name, request, result)
            return result
        except Exception as e:
            error_response = {'error': str(e), 'type': type(e).__name__}
            txn_logger.log_transaction(command_name, request, error_response)
            raise

    return wrapper


# Override FastMCP's tool decorator to add logging
original_tool = mcp.tool


def tool_with_logging(*args, **kwargs):
    """Wrapper around FastMCP's tool decorator to add transaction logging"""
    decorator = original_tool(*args, **kwargs)

    def wrapper(func):
        # Apply the original decorator
        decorated = decorator(func)

        # Add transaction logging
        decorated_with_logging = log_transactions(decorated)
        return decorated_with_logging

    return wrapper


# Replace FastMCP's tool decorator with our logging version
mcp.tool = tool_with_logging

# Forward declaration of functions
register_mcp_module = None


# Function to register MCP modules as FastMCP tools
def register_mcp_module_impl(module, mcp_instance):
    """Register an MCP module as a FastMCP tool"""
    try:
        if not hasattr(module, 'get_mcp_schema') or not hasattr(module, 'mcp_execute'):
            logger.warning(f'Module {module.__name__} missing required MCP interface')
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
                logger.info(f'Standardizing tool name from {tool_name} to {new_tool_name}')
                tool_name = new_tool_name

        logger.info(f'Registering MCP module as tool: {tool_name}')

        # Create a wrapper function that calls mcp_execute
        def tool_wrapper(**kwargs):
            return module.mcp_execute(kwargs)

        # Set function name and docstring
        tool_wrapper.__name__ = tool_name
        tool_wrapper.__doc__ = schema.get('description', f'HAgent MCP tool: {tool_name}')

        # Register with FastMCP
        mcp_instance.tool(name=tool_name)(tool_wrapper)
        return True
    except Exception as e:
        logger.error(f'Error registering MCP module: {e}')
        return False


# Set the implementation
register_mcp_module = register_mcp_module_impl


# Function to discover and register MCP modules
def discover_and_register_mcp_modules(mcp_instance):
    """Discover all available MCP modules and register them as FastMCP tools"""
    logger.info('Discovering and registering MCP modules')
    registered_tools = []

    try:
        # Discover available modules
        discovered_modules = discover_mcp_commands()
        module_names = list(discovered_modules.keys())
        logger.info(f'Discovered {len(discovered_modules)} MCP modules: {module_names}')

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
                logger.error(f'Error registering {module_name} module: {e}')

        logger.info(f'Successfully registered {len(registered_tools)} MCP tools: {registered_tools}')
        return registered_tools

    except Exception as e:
        logger.error(f'Error discovering MCP modules: {e}')
        print(f'Error discovering MCP modules: {e}', file=sys.stderr)
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


@mcp.tool(name='hagent.info')
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
        'working_directory': os.getcwd(),
    }

    return env_vars


@mcp.tool(name='hagent.setup_environment')
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
                'HAGENT_CACHE_DIR': os.environ.get('HAGENT_CACHE_DIR', 'NOT_SET'),
            },
        }
    except Exception as e:
        return {'success': False, 'error': str(e)}


# Setup environment when the module is imported
try:
    # Set up environment when the module is imported
    EnvironmentSetup.setup_environment()
    logger.info('Environment automatically set up on import')
except Exception as e:
    logger.error(f'Error setting up environment: {e}')
    print(f'Error setting up environment: {e}', file=sys.stderr)


# Create a raw_logger for all stdin/stdout regardless of command
def setup_raw_logger(cache_dir):
    """Setup a logger for raw stdin/stdout traffic"""
    log_dir = Path(cache_dir) / 'mcp'
    log_dir.mkdir(parents=True, exist_ok=True)

    raw_logger = logging.getLogger('hagent-mcp-raw')
    raw_logger.setLevel(logging.DEBUG)

    # Clear any existing handlers
    raw_logger.handlers = []

    # Add file handler
    raw_log_file = log_dir / 'raw_io.log'
    handler = logging.FileHandler(raw_log_file)
    handler.setLevel(logging.DEBUG)
    formatter = logging.Formatter('%(asctime)s - %(levelname)s - %(message)s')
    handler.setFormatter(formatter)
    raw_logger.addHandler(handler)

    # Also add stderr handler for immediate visibility
    console_handler = logging.StreamHandler(sys.stderr)
    console_handler.setLevel(logging.INFO)
    console_handler.setFormatter(formatter)
    raw_logger.addHandler(console_handler)

    return raw_logger


# Custom implementation of FastMCP's run method with raw logging and JSON-RPC 2.0 support
def run_with_logging(mcp_instance, transport='stdio'):
    """Run FastMCP with raw input/output logging and JSON-RPC 2.0 support"""
    cache_dir = os.environ.get('HAGENT_CACHE_DIR', './cache')
    raw_logger = setup_raw_logger(cache_dir)

    raw_logger.info('=== MCP SERVER STARTED ===')
    raw_logger.info(f'Using cache directory: {cache_dir}')

    # Prepare available tools (async to sync conversion)
    tools = None
    try:
        # For FastMCP 1.13.0+, list_tools is a coroutine
        import asyncio

        tools_coroutine = mcp_instance.list_tools()
        if asyncio.iscoroutine(tools_coroutine):
            # Run the coroutine in a new event loop
            loop = asyncio.new_event_loop()
            tools = loop.run_until_complete(tools_coroutine)
            loop.close()
        else:
            tools = tools_coroutine
    except Exception as e:
        raw_logger.error(f'Failed to get tools list: {e}')
        tools = []

    raw_logger.info(f'Available tools: {tools}')

    # JSON-RPC 2.0 support
    def create_jsonrpc_response(id, result=None, error=None):
        """Create a JSON-RPC 2.0 response"""
        response = {'jsonrpc': '2.0', 'id': id}

        if error is not None:
            response['error'] = error
        else:
            response['result'] = result

        return response

    def create_jsonrpc_error(code, message, data=None):
        """Create a JSON-RPC 2.0 error object"""
        error = {'code': code, 'message': message}
        if data is not None:
            error['data'] = data
        return error

    if transport == 'stdio':
        for line in sys.stdin:
            try:
                raw_line = line.strip()
                raw_logger.info(f'RECEIVED RAW INPUT: {raw_line}')

                # Parse JSON request
                try:
                    request = json.loads(raw_line)
                    raw_logger.info(f'PARSED REQUEST: {json.dumps(request, indent=2)}')
                except json.JSONDecodeError as e:
                    raw_logger.error(f'JSON PARSE ERROR: {e}')
                    error = create_jsonrpc_error(-32700, 'Parse error')
                    response = create_jsonrpc_response(None, error=error)
                    print(json.dumps(response), flush=True)
                    raw_logger.info('SENT ERROR RESPONSE: Parse error')
                    continue

                # Extract JSON-RPC fields
                method = request.get('method', '')
                params = request.get('params', {})
                id = request.get('id')
                jsonrpc = request.get('jsonrpc', '2.0')

                raw_logger.info(f'PROCESSING METHOD: {method} (ID: {id}, JSON-RPC: {jsonrpc})')

                try:
                    # Handle initialize method for Gemini compatibility
                    if method == 'initialize':
                        raw_logger.info('Handling initialize request')
                        # Return server capabilities
                        result = {
                            'serverInfo': {'name': 'hagent-mcp-server', 'version': '1.0.0'},
                            'capabilities': {'roots': {'listChanged': True}},
                            'serverName': 'HAgent MCP Server',
                        }
                        response = create_jsonrpc_response(id, result)

                    # Handle traditional FastMCP methods
                    elif method == 'tools/list':
                        raw_logger.info('Handling tools/list request')

                        # Convert to JSON-RPC 2.0 format
                        result = {'tools': tools}
                        response = create_jsonrpc_response(id, result)
                        raw_logger.info(f'TOOLS LIST RESPONSE: {len(tools)} tools')

                    elif method == 'tools/call':
                        name = params.get('name', '')
                        # For Gemini compatibility - handle both by id and by name
                        tool_id = params.get('id', name)
                        if not name and tool_id:
                            name = tool_id

                        arguments = params.get('arguments', {})

                        raw_logger.info(f'TOOL CALL: {name} with arguments {json.dumps(arguments)}')

                        try:
                            # For FastMCP 1.13.0+, call_tool might be a coroutine
                            tool_response_coroutine = mcp_instance.call_tool(name, arguments)

                            if asyncio.iscoroutine(tool_response_coroutine):
                                # Run the coroutine in a new event loop
                                loop = asyncio.new_event_loop()
                                tool_response = loop.run_until_complete(tool_response_coroutine)
                                loop.close()
                            else:
                                tool_response = tool_response_coroutine

                            # Format response for better Gemini compatibility
                            if isinstance(tool_response, dict):
                                # If there's a content field, keep it as is for Claude compatibility
                                if 'content' not in tool_response:
                                    # For Gemini, wrap in a result object with content
                                    formatted_result = {'result': tool_response}
                                else:
                                    formatted_result = tool_response
                            else:
                                # Handle non-dict responses
                                formatted_result = {'result': str(tool_response) if tool_response is not None else ''}

                            raw_logger.info(f'TOOL RESPONSE SUCCESS: {name}')
                            response = create_jsonrpc_response(id, formatted_result)
                        except Exception as e:
                            raw_logger.error(f'TOOL ERROR: {name} - {str(e)}\n{traceback.format_exc()}')
                            error_data = {'type': 'text', 'text': str(e)}
                            error = create_jsonrpc_error(-32603, f'Tool execution error: {name}', error_data)
                            response = create_jsonrpc_response(id, error=error)

                    # Handle Gemini-specific methods
                    elif method == 'roots/list':
                        raw_logger.info('Handling roots/list request')

                        # Create list of roots (tool categories)
                        # For HAgent, we'll define a single root called "HAgent Tools"
                        root_info = {'id': 'hagent', 'title': 'HAgent Tools', 'canCreateToolRoots': False}
                        result = {'roots': [root_info]}
                        response = create_jsonrpc_response(id, result)
                        raw_logger.info(f'ROOTS LIST RESPONSE: {json.dumps(result)}')

                    elif method == 'roots/get':
                        raw_logger.info('Handling roots/get request')
                        root_id = params.get('rootId')

                        if root_id == 'hagent':
                            # Convert the tools list to the format Gemini expects
                            gemini_tools = []
                            for tool in tools:
                                # Extract just the essential fields for Gemini
                                gemini_tool = {
                                    'id': tool.name,
                                    'title': tool.name.split('.')[-1].title(),
                                    'description': tool.description or '',
                                }
                                gemini_tools.append(gemini_tool)

                            result = {
                                'root': {
                                    'id': 'hagent',
                                    'title': 'HAgent Tools',
                                    'canCreateToolRoots': False,
                                    'tools': gemini_tools,
                                }
                            }
                            response = create_jsonrpc_response(id, result)
                            raw_logger.info(f'ROOTS GET RESPONSE: {len(gemini_tools)} tools')
                        else:
                            error = create_jsonrpc_error(-32602, f'Unknown root ID: {root_id}')
                            response = create_jsonrpc_response(id, error=error)

                    # Handle JSON-RPC 2.0 specific methods
                    elif method == 'shutdown':
                        raw_logger.info('Handling shutdown request')
                        response = create_jsonrpc_response(id, True)

                    elif method == 'exit':
                        raw_logger.info('Handling exit request')
                        response = create_jsonrpc_response(id, True)
                        # No need to send response for exit notification
                        if id is not None:
                            response_json = json.dumps(response)
                            print(response_json, flush=True)
                            raw_logger.info(f'SENT RESPONSE: {response_json}')
                        # Exit the server
                        raw_logger.info('=== MCP SERVER EXITING ===')
                        return

                    # Handle unknown methods
                    else:
                        raw_logger.error(f'UNKNOWN METHOD: {method}')
                        error = create_jsonrpc_error(-32601, f'Method not found: {method}')
                        response = create_jsonrpc_response(id, error=error)

                    # Send response if ID is present (per JSON-RPC 2.0 spec)
                    if id is not None:
                        response_json = json.dumps(response)
                        print(response_json, flush=True)
                        raw_logger.info(f'SENT RESPONSE: {response_json[:500]}{"..." if len(response_json) > 500 else ""}')

                except Exception as e:
                    raw_logger.error(f'PROCESSING ERROR: {str(e)}\n{traceback.format_exc()}')
                    error = create_jsonrpc_error(-32603, f'Internal error: {str(e)}')
                    response = create_jsonrpc_response(id, error=error)
                    print(json.dumps(response), flush=True)
                    raw_logger.info('SENT ERROR RESPONSE: Internal error')

            except Exception as outer_e:
                raw_logger.error(f'CRITICAL ERROR: {str(outer_e)}\n{traceback.format_exc()}')
                try:
                    error = create_jsonrpc_error(-32603, f'Critical error: {str(outer_e)}')
                    response = create_jsonrpc_response(None, error=error)
                    print(json.dumps(response), flush=True)
                except:
                    error = create_jsonrpc_error(-32603, 'Unknown critical error')
                    response = create_jsonrpc_response(None, error=error)
                    print(json.dumps(response), flush=True)
    else:
        raw_logger.error(f'Unsupported transport: {transport}')
        raise ValueError(f'Unsupported transport: {transport}')


if __name__ == '__main__':
    # Run this file as an MCP stdio server
    logger.info('Starting HAgent MCP Server with FastMCP')
    print("HAgent MCP Server running with FastMCP. Use 'uv run python hagent-mcp-server.py'", file=sys.stderr)

    # Use our custom run method with logging instead of mcp.run
    run_with_logging(mcp, transport='stdio')
