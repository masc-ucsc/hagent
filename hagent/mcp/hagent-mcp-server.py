#!/usr/bin/env python3
"""
HAgent MCP Server - MCP server implementation using FastMCP

This is a FastMCP-based server that exposes HAgent tools and utilities.
"""

from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import traceback
from pathlib import Path
from typing import Dict

# Add the hagent root to Python path for imports
HAGENT_ROOT = os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
sys.path.insert(0, HAGENT_ROOT)

# Import FastMCP
from mcp.server.fastmcp import FastMCP  # noqa: E402

# Import command discovery
from hagent.mcp.command_discovery import discover_mcp_commands  # noqa: E402

# Import MCP logging utilities
from hagent.mcp.log_mcp_server import (  # noqa: E402
    TransactionLogger,
    setup_mcp_server_logging,
    setup_raw_logger,
    create_transaction_logging_decorator,
)

# Import MCP message handlers
from hagent.mcp.mcp_message_handlers import (  # noqa: E402
    MCPMessageHandlers,
    handle_mcp_stdio_request,
)


# Initialize FastMCP and loggers
logger = setup_mcp_server_logging()

# Create transaction logger
txn_logger = TransactionLogger()

# Create FastMCP instance with request/response logging
mcp = FastMCP('HAgentMCPServer')


# Create transaction logging decorator
log_transactions = create_transaction_logging_decorator(txn_logger)


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

        # Create a wrapper function that calls mcp_execute with proper signature
        def tool_wrapper(name: str = None, profile: str = None, api: str = None, dry_run: bool = False, **extra_kwargs):
            # Handle both structured parameters and legacy kwargs format
            params = {}

            # Check if we got legacy kwargs format
            if 'kwargs' in extra_kwargs:
                kwargs_value = extra_kwargs['kwargs']
                if isinstance(kwargs_value, str):
                    import json

                    try:
                        # Try JSON parsing first
                        params = json.loads(kwargs_value)
                    except json.JSONDecodeError:
                        # If not JSON, try parsing as comma-separated key=value format
                        if '=' in kwargs_value:
                            params = {}
                            # Parse key=value,key=value format
                            pairs = kwargs_value.strip().split(',')
                            for pair in pairs:
                                if '=' in pair:
                                    key, value = pair.split('=', 1)
                                    params[key.strip()] = value.strip()
                        else:
                            # Try parsing as space-separated or dot-separated "name api" format
                            # Handle both "gcd compile" and "gcd.compile" formats
                            parts = kwargs_value.replace('.', ' ').strip().split()
                            if len(parts) >= 2:
                                # First arg is name, second is api
                                params = {'name': parts[0], 'api': parts[1]}
                                # Handle additional flags like dry_run
                                if '--dry-run' in parts or 'dry-run' in parts:
                                    params['dry_run'] = True
                            elif len(parts) == 1:
                                # Single argument, could be just name or api
                                params = {'name': parts[0]}
                            else:
                                params = {}
                else:
                    params = kwargs_value if isinstance(kwargs_value, dict) else {}
            else:
                # Use structured parameters
                if name is not None:
                    params['name'] = name
                if profile is not None:
                    params['profile'] = profile
                if api is not None:
                    params['api'] = api
                if dry_run:
                    params['dry_run'] = dry_run
                # Add any extra kwargs
                params.update(extra_kwargs)

            # Handle parameter name mapping: 'profile' -> 'name' for backward compatibility
            if 'profile' in params and 'name' not in params:
                params['name'] = params.pop('profile')

            # Call mcp_execute and ensure we return the structured output properly
            result = module.mcp_execute(params)

            # Check if the command failed and use the pre-formatted error message
            if isinstance(result, dict) and not result.get('success', True):
                # Use the error_message from mcp_execute if available
                if 'error_message' in result:
                    # Return a special error marker that our custom run_with_logging can detect
                    return {'_mcp_error': True, 'error_message': result['error_message']}
                else:
                    # Fallback if no error_message was provided
                    exit_code = result.get('exit_code', 'unknown')
                    stderr = result.get('stderr', '')
                    stdout = result.get('stdout', '')
                    fallback_msg = f'❌ COMMAND FAILED (exit code: {exit_code})\n\nSTDERR:\n{stderr}\n\nSTDOUT:\n{stdout}'
                    return {'_mcp_error': True, 'error_message': fallback_msg}

            # For successful executions, return just stdout as a plain string
            # (FastMCP expects string return values for tool functions)
            if isinstance(result, dict):
                # Return a minimal success indicator
                exit_code = result.get('exit_code', 0)
                return f'✓ Command completed successfully (exit code: {exit_code})'

            # Fallback for other result types
            return str(result)

        # Set function name and docstring
        tool_wrapper.__name__ = tool_name
        tool_wrapper.__doc__ = schema.get('description', f'HAgent MCP tool: {tool_name}')

        # Register with FastMCP using dynamic function signature from custom schema
        # Create function with dynamic parameters based on the custom schema
        input_schema = schema.get('inputSchema', {})
        properties = input_schema.get('properties', {})

        # Build function signature dynamically from schema properties
        import inspect
        from typing import Optional

        # Create parameter annotations based on schema properties
        sig_params = []
        annotations = {}

        for prop_name, prop_info in properties.items():
            param_type = str  # Default type
            default_value = prop_info.get('default', None)

            # Handle different JSON Schema types
            if prop_info.get('type') == 'boolean':
                param_type = bool
                if default_value is None:
                    default_value = False
            elif prop_info.get('type') == 'integer':
                param_type = int
            elif prop_info.get('type') == 'number':
                param_type = float

            # Make parameter optional if not in required list
            required_props = input_schema.get('required', [])
            if prop_name not in required_props:
                param_type = Optional[param_type]
                if default_value is None:
                    default_value = None

            # Create parameter
            param = inspect.Parameter(prop_name, inspect.Parameter.KEYWORD_ONLY, default=default_value, annotation=param_type)
            sig_params.append(param)
            annotations[prop_name] = param_type

        # Create function with dynamic signature
        def create_dynamic_wrapper():
            def dynamic_wrapper(**kwargs):
                return tool_wrapper(**kwargs)

            # Set the signature
            dynamic_wrapper.__signature__ = inspect.Signature(sig_params)
            dynamic_wrapper.__annotations__ = annotations
            dynamic_wrapper.__name__ = tool_name
            dynamic_wrapper.__doc__ = schema.get('description', f'HAgent MCP tool: {tool_name}')

            return dynamic_wrapper

        annotated_tool_wrapper = create_dynamic_wrapper()

        # Register with FastMCP using the annotated wrapper
        tool_decorator = mcp_instance.tool(name=tool_name, description=schema.get('description', f'HAgent MCP tool: {tool_name}'))
        tool_decorator(annotated_tool_wrapper)

        # Post-process: Override the inputSchema with the original custom schema
        if tool_name in mcp_instance._tool_manager._tools:
            tool_obj = mcp_instance._tool_manager._tools[tool_name]
            # Override the parameters to use the original schema directly
            custom_input_schema = schema.get('inputSchema', {})
            if custom_input_schema and hasattr(tool_obj, 'parameters'):
                # Directly set the parameters to match the custom schema
                tool_obj.parameters = custom_input_schema

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
    def _setup_environment():
        """Setup proper HAgent environment variables with intelligent defaults"""
        logger.info('Setting up HAgent environment variables')

        # First check we're in a safe location
        EnvironmentSetup._check_safe_working_directory()

        # Get or set HAGENT_ROOT
        if 'HAGENT_ROOT' not in os.environ:
            os.environ['HAGENT_ROOT'] = HAGENT_ROOT
            logger.info(f'Set HAGENT_ROOT={HAGENT_ROOT}')

        # Log the final environment setup
        logger.info('Environment setup:')
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
    EnvironmentSetup._setup_environment()

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


# Removed hagent.setup_environment - redundant with hagent.info


# Setup environment when the module is imported
try:
    # Set up environment when the module is imported
    EnvironmentSetup._setup_environment()
    logger.info('Environment automatically set up on import')
except Exception as e:
    logger.error(f'Error setting up environment: {e}')
    print(f'Error setting up environment: {e}', file=sys.stderr)


# Custom implementation of FastMCP's run method with raw logging and JSON-RPC 2.0 support
def run_with_logging(mcp_instance, transport='stdio'):
    """Run FastMCP with raw input/output logging and JSON-RPC 2.0 support"""
    raw_logger = setup_raw_logger()

    raw_logger.info('=== MCP SERVER STARTED ===')
    raw_logger.info('Raw I/O logging enabled')

    # Prepare available tools (async to sync conversion)
    tools = _get_available_tools(mcp_instance, raw_logger)
    raw_logger.info(f'Available tools: {tools}')

    # Create message handlers
    handlers = MCPMessageHandlers(mcp_instance, raw_logger)
    handlers.set_tools(tools)

    if transport == 'stdio':
        _handle_stdio_communication(handlers, raw_logger)
    else:
        raw_logger.error(f'Unsupported transport: {transport}')
        raise ValueError(f'Unsupported transport: {transport}')


def _get_available_tools(mcp_instance, raw_logger):
    """Get available tools from MCP instance, handling async/sync conversion."""
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

    return tools


def _handle_stdio_communication(handlers, raw_logger):
    """Handle stdin/stdout communication loop for MCP server."""
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
                error_response = _create_parse_error_response()
                print(json.dumps(error_response), flush=True)
                raw_logger.info('SENT ERROR RESPONSE: Parse error')
                continue

            # Handle the request using our handlers
            try:
                response, should_exit = handle_mcp_stdio_request(request, handlers)

                # Send response if present
                if response is not None:
                    _send_response(response, raw_logger)

                # Exit if requested
                if should_exit:
                    raw_logger.info('=== MCP SERVER EXITING ===')
                    return

            except Exception as e:
                raw_logger.error(f'PROCESSING ERROR: {str(e)}\n{traceback.format_exc()}')
                error_response = _create_internal_error_response(request.get('id'), str(e))
                print(json.dumps(error_response), flush=True)
                raw_logger.info('SENT ERROR RESPONSE: Internal error')

        except Exception as outer_e:
            raw_logger.error(f'CRITICAL ERROR: {str(outer_e)}\n{traceback.format_exc()}')
            error_response = _create_critical_error_response(str(outer_e))
            print(json.dumps(error_response), flush=True)


def _create_parse_error_response():
    """Create JSON-RPC parse error response."""
    return {'jsonrpc': '2.0', 'id': None, 'error': {'code': -32700, 'message': 'Parse error'}}


def _create_internal_error_response(request_id, error_message):
    """Create JSON-RPC internal error response."""
    return {'jsonrpc': '2.0', 'id': request_id, 'error': {'code': -32603, 'message': f'Internal error: {error_message}'}}


def _create_critical_error_response(error_message):
    """Create JSON-RPC critical error response."""
    return {'jsonrpc': '2.0', 'id': None, 'error': {'code': -32603, 'message': f'Critical error: {error_message}'}}


def _send_response(response, raw_logger):
    """Send JSON-RPC response with logging."""
    response_json = json.dumps(response)
    print(response_json, flush=True)

    # Format response for better readability in logs
    try:
        if 'result' in response and 'result' in response['result']:
            content = response['result']['result']
            if isinstance(content, str) and '\\n' in content:
                # Replace \n with actual newlines for better readability
                readable_content = content.replace('\\n', '\n').replace('\\t', '\t')
                raw_logger.info(
                    f'SENT RESPONSE (formatted):\n{readable_content[:800]}{"..." if len(readable_content) > 800 else ""}'
                )
            else:
                raw_logger.info(f'SENT RESPONSE: {response_json[:500]}{"..." if len(response_json) > 500 else ""}')
        else:
            raw_logger.info(f'SENT RESPONSE: {response_json[:500]}{"..." if len(response_json) > 500 else ""}')
    except Exception:
        raw_logger.info(f'SENT RESPONSE: {response_json[:500]}{"..." if len(response_json) > 500 else ""}')


if __name__ == '__main__':
    # Parse command line arguments
    parser = argparse.ArgumentParser(description='HAgent MCP Server')
    parser.add_argument('--debug', action='store_true', help='Enable debug mode with detailed logging and raw I/O logging')
    args = parser.parse_args()

    # Run this file as an MCP stdio server
    logger.info('Starting HAgent MCP Server with FastMCP')
    print("HAgent MCP Server running with FastMCP. Use 'uv run python hagent-mcp-server.py'", file=sys.stderr)

    if args.debug:
        print('Debug mode enabled - using custom logging', file=sys.stderr)
        # Use our custom run method with logging for debug mode
        run_with_logging(mcp, transport='stdio')
    else:
        # Use FastMCP's built-in run method (same as working trivial time server)
        mcp.run(transport='stdio')
