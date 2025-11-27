#!/bin/sh
# fmt: off
''''
# Ensure uv discovers the hagent project even when invoked from a different cwd
if [ -n "$UV_PROJECT" ]; then
    PROJECT_ROOT="$UV_PROJECT"
else
    PROJECT_ROOT="$(cd "$(dirname "$0")"/../.. && pwd -P)"
fi

# Docker detection: if /code/workspace/cache exists, we're in Docker
if [ -d "/code/workspace/cache" ]; then
    # In Docker: /code/hagent is read-only, so use cache venv
    VENV_DIR="/code/workspace/cache/.venv"
    if [ -z "$UV_PROJECT_ENVIRONMENT" ]; then
        export UV_PROJECT_ENVIRONMENT="$VENV_DIR"
    fi

    # Ensure venv exists - if not, create it once
    if [ ! -f "$VENV_DIR/bin/python" ]; then
        cd "$PROJECT_ROOT" && uv venv "$VENV_DIR" && uv sync --frozen
    fi

    # Use the venv Python directly (no sync needed, much faster)
    exec "$VENV_DIR/bin/python" "$0" "$@"
else
    # Local: use uv run to manage environment (handles sync automatically)
    exec uv run --project "$PROJECT_ROOT" python "$0" "$@"
fi
'''
# fmt: on
# ruff: noqa: E402
"""
MCP Command: Build

HAgent build command with unified CLI and MCP interfaces.
Provides access to HAgent profile-based build operations through the Builder class.
"""

import os
import argparse
import sys
from typing import Dict, Any, Optional
from pathlib import Path
import re
import logging

# Ensure we can import hagent by adding project root to sys.path
script_path = Path(__file__).resolve()
project_root = script_path.parent.parent.parent
if str(project_root) not in sys.path:
    sys.path.insert(0, str(project_root))

from hagent.inou.builder import Builder


def _clean_ansi_codes(text: str) -> str:
    """Remove ANSI escape codes from text for better pattern matching."""
    ansi_escape = re.compile(r'\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])')
    return ansi_escape.sub('', text)


def _format_error_response(exit_code: int, stdout: str, stderr: str) -> Dict[str, Any]:
    """
    Format error response with intelligent error detection and helpful suggestions.

    Priority order for error detection:
    1. If stderr has content, use it as the primary error message
    2. Otherwise, search stdout/stderr for error/warning patterns
    3. Provide language-specific suggestions when patterns are detected

    Args:
        exit_code: Command exit code
        stdout: Standard output from command
        stderr: Standard error from command

    Returns:
        Dictionary with formatted error information including error_message and suggestions
    """
    combined_output = stderr + stdout
    clean_output = _clean_ansi_codes(combined_output)

    error_suggestions = []
    error_summary = None
    files_to_check = []

    # Priority 1: Use stderr if it has substantial content
    if stderr and len(stderr.strip()) > 10:
        error_summary = stderr.strip()
        # Still check for file references in stderr
        file_matches = re.findall(r'(/[^:\s]+\.(scala|v|sv|vhd|c|cpp|py|java))(?::(\d+))?', stderr)
        if file_matches:
            files_to_check = [f'{f}:{line}' if line else f for f, ext, line in file_matches[:3]]

    # Priority 2: Search for error/warning patterns if no stderr or for additional context
    else:
        # Look for common error patterns (case-insensitive)
        error_patterns = [
            (r'error[:\]]', 'error'),
            (r'warning[:\]]', 'warning'),
            (r'failed', 'failure'),
            (r'exception', 'exception'),
        ]

        found_errors = []
        for pattern, error_type in error_patterns:
            matches = re.finditer(pattern, clean_output, re.IGNORECASE)
            for match in matches:
                # Extract the line containing the error
                start = max(0, match.start() - 100)
                end = min(len(clean_output), match.end() + 100)
                context = clean_output[start:end].strip()
                # Get just the line with the error
                lines = context.split('\n')
                for line in lines:
                    if re.search(pattern, line, re.IGNORECASE):
                        found_errors.append(line.strip())
                        break

        if found_errors:
            # Use first few unique errors
            unique_errors = list(dict.fromkeys(found_errors))[:3]
            error_summary = '\n'.join(unique_errors)

    # Detect language-specific errors and provide suggestions
    if 'scala' in clean_output.lower() or '.scala' in clean_output:
        error_suggestions.append(
            '🔧 SUGGESTION: There appears to be a Scala compilation error. Please check and fix the Scala source files.'
        )

        # Extract Scala file references
        scala_matches = re.findall(r'(/[^:\s]+\.scala)(?::(\d+))?', clean_output)
        if scala_matches:
            files_to_check.extend([f'{f}:{line}' if line else f for f, line in scala_matches[:3]])

        # Look for specific Scala error patterns
        if 'not found: value' in clean_output or 'not found: type' in clean_output:
            not_found = re.findall(r'not found: (?:value|type) (\w+)', clean_output)
            if not_found:
                error_suggestions.append(f'❌ MISSING SYMBOLS: {", ".join(not_found[:3])}')

    elif '.v' in clean_output or 'verilog' in clean_output.lower():
        error_suggestions.append('🔧 SUGGESTION: There appears to be a Verilog error. Please check the Verilog source files.')
        verilog_matches = re.findall(r'(/[^:\s]+\.v)(?::(\d+))?', clean_output)
        if verilog_matches:
            files_to_check.extend([f'{f}:{line}' if line else f for f, line in verilog_matches[:3]])

    elif '.c' in clean_output or '.cpp' in clean_output or 'gcc' in clean_output.lower() or 'g++' in clean_output.lower():
        error_suggestions.append('🔧 SUGGESTION: There appears to be a C/C++ compilation error. Please check the source files.')
        c_matches = re.findall(r'(/[^:\s]+\.(?:c|cpp|h|hpp))(?::(\d+))?', clean_output)
        if c_matches:
            files_to_check.extend([f'{f}:{line}' if line else f for f, line in c_matches[:3]])

    # Add file references if found
    if files_to_check:
        unique_files = list(dict.fromkeys(files_to_check))[:3]
        error_suggestions.append(f'📁 FILES TO CHECK: {", ".join(unique_files)}')

    # Build formatted error message
    error_parts = [f'❌ COMPILATION FAILED (exit code: {exit_code})']

    if error_suggestions:
        error_parts.extend(error_suggestions)

    if error_summary:
        # Truncate if too long
        if len(error_summary) > 500:
            error_summary = error_summary[:500] + '...'
        error_parts.append(f'\n🔍 ERROR DETAILS:\n{error_summary}')

    formatted_error_message = '\n\n'.join(error_parts)

    return {
        'error_message': formatted_error_message,
        'has_errors': True,
    }


def get_mcp_schema(config_path: Optional[str] = None) -> Dict[str, Any]:
    """Return MCP tool schema for HAgent build command with dynamic profile/API information."""

    # Try to get actual available profiles and APIs from the current environment
    available_profiles = []
    available_apis = []
    profiles_description = 'No profiles found'

    try:
        # Check if environment is already properly set up
        required_env_vars = ['HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR']
        env_already_set = all(var in os.environ for var in required_env_vars)

        env_backup = {}
        temp_dir = None

        if not env_already_set:
            # For schema generation, temporarily set required environment variables if not set
            # This allows schema generation to work without a full project setup
            import tempfile

            temp_dir = tempfile.mkdtemp(prefix='hagent_schema_')

            env_defaults = {
                'HAGENT_REPO_DIR': temp_dir,
                'HAGENT_BUILD_DIR': temp_dir,
                'HAGENT_CACHE_DIR': temp_dir,
            }
            for var in required_env_vars:
                if var not in os.environ:
                    env_backup[var] = None
                    os.environ[var] = env_defaults[var]  # Set appropriate default for schema generation
                else:
                    env_backup[var] = os.environ[var]

        # Initialize profiles to empty list in case of failure
        profiles = []

        try:
            # Use Builder directly to get profiles in current environment
            # In Docker mode, we need to setup Docker to access mounted config files
            # Suppress all output during schema generation to avoid polluting JSON output
            from contextlib import redirect_stdout, redirect_stderr
            from io import StringIO

            # Capture all output during schema generation
            captured_output = StringIO()
            captured_errors = StringIO()

            docker_image = os.environ.get('HAGENT_DOCKER')
            builder = None
            try:
                with redirect_stdout(captured_output), redirect_stderr(captured_errors):
                    builder = Builder(config_path=config_path, docker_image=docker_image)
                    setup_success = builder.setup()

                if not setup_success:
                    # If setup fails, we can't get profiles - use empty list
                    profiles = []
                    profiles_description = 'No profiles found'
                else:
                    # Get profiles with output still suppressed
                    with redirect_stdout(captured_output), redirect_stderr(captured_errors):
                        profiles = builder.get_all_profiles()
                        # Get description from builder while it's still available
                        profiles_description = builder.list_profiles()
                        # Remove leading newline for schema description
                        if profiles_description and profiles_description.startswith('\n'):
                            profiles_description = profiles_description[1:]
            finally:
                # Always clean up the builder to avoid atexit warnings
                if builder:
                    with redirect_stdout(captured_output), redirect_stderr(captured_errors):
                        builder.cleanup()
                    builder = None

        finally:
            # Restore original environment if we modified it
            for var, original_value in env_backup.items():
                if original_value is None:
                    os.environ.pop(var, None)
                else:
                    os.environ[var] = original_value

            # Clean up temp directory if we created one
            if temp_dir:
                import shutil

                try:
                    shutil.rmtree(temp_dir)
                except Exception:
                    pass  # Ignore cleanup errors

        # Process the profiles we retrieved (with suppressed output)
        available_profiles = [p.get('name', '') for p in profiles if p.get('name')]

        # Collect unique API names across all profiles
        api_set = set()
        for profile in profiles:
            for api in profile.get('apis', []):
                if api.get('name'):
                    api_set.add(api.get('name'))
        available_apis = list(api_set)

        # profiles_description is already set in the try block above

    except Exception as e:
        profiles_description = f'ERROR: Invalid environment setup. {str(e)}'
        available_profiles = []
        available_apis = []

    # Use profiles description or fallback
    final_description = (
        profiles_description.strip()
        if profiles_description and not profiles_description.startswith('ERROR:')
        else 'Unified interface for HAGENT_REPO build profiles'
    )

    return {
        'name': 'hagent_build',
        'description': final_description,
        'inputSchema': {
            'type': 'object',
            'properties': {
                'name': {
                    'type': 'string',
                    'description': 'Design or profile name to perform the API command (exact match, case-insensitive)',
                    'enum': available_profiles,
                }
                if available_profiles
                else {'type': 'string', 'description': 'Profile or target name (exact match, case-insensitive)'},
                'profile': {
                    'type': 'string',
                    'description': 'Design or profile regex pattern to match in titles/descriptions to perform the API command',
                },
                'api': {
                    'type': 'string',
                    'description': 'API command to execute',
                    'enum': available_apis,
                }
                if available_apis
                else {'type': 'string', 'description': 'API command to execute'},
                'dry_run': {'type': 'boolean', 'description': 'Show what would be executed without running', 'default': False},
                'debug': {
                    'type': 'boolean',
                    'description': 'Enable debug mode: print commands and use verbose output',
                    'default': False,
                },
            },
            'required': [],
        },
    }


def mcp_execute(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    MCP execution entry point for HAgent build command.

    Args:
        params: Dictionary containing the input parameters from Claude Code

    Returns:
        Dictionary with execution results in a structured format
    """
    builder = None
    try:
        # Get config path from environment or params
        config_path = os.environ.get('HAGENT_CONFIG_PATH')

        # Initialize Builder with Docker configuration from environment
        docker_image = os.environ.get('HAGENT_DOCKER')
        builder = Builder(config_path=config_path, docker_image=docker_image)

        # Handle parameters
        exact_name = params.get('name')
        profile_query = params.get('profile')
        api_name = params.get('api')
        dry_run = params.get('dry_run', False)

        # If no API specified, this might be a listing request
        if not api_name:
            # Setup builder for listing operations (needs config)
            if not builder.setup():
                # For dry runs, allow operation if we at least have config
                if not (dry_run and builder.has_config):
                    return {
                        'success': False,
                        'exit_code': 1,
                        'stdout': '',
                        'stderr': f'Builder setup failed: {builder.get_error()}',
                        'params_used': params,
                    }

            # List APIs for specific profile(s)
            if exact_name or profile_query:
                try:
                    success = builder.list_apis_for_profile(exact_name, profile_query)
                    return {
                        'success': success,
                        'exit_code': 0 if success else 2,
                        'stdout': 'APIs listed successfully' if success else '',
                        'stderr': '' if success else 'Failed to list APIs',
                        'params_used': params,
                    }
                except Exception as e:
                    return {
                        'success': False,
                        'exit_code': 1,
                        'stdout': '',
                        'stderr': str(e),
                        'params_used': params,
                    }
            else:
                # List all profiles
                try:
                    profiles_output = builder.list_profiles()
                    return {
                        'success': True,
                        'exit_code': 0,
                        'stdout': profiles_output,
                        'stderr': '',
                        'params_used': params,
                    }
                except Exception as e:
                    return {
                        'success': False,
                        'exit_code': 1,
                        'stdout': '',
                        'stderr': str(e),
                        'params_used': params,
                    }

        # Setup builder - for dry run, allow operation if we at least have config
        if not builder.setup():
            # For dry runs, allow operation if we at least have config, even if Runner setup failed
            if not (dry_run and builder.has_config):
                error_msg = f'Builder setup failed: {builder.get_error()}'
                error_info = _format_error_response(1, '', error_msg)
                return {
                    'success': False,
                    'exit_code': 1,
                    'stdout': '',
                    'stderr': error_msg,
                    'error_message': error_info['error_message'],
                    'params_used': params,
                }

        # Execute the command
        try:
            # Handle debug mode
            debug = params.get('debug', False)
            quiet = not debug  # Use verbose output when debug is enabled

            # If debug mode and not already doing a dry run, first get the command to log it
            if debug and not dry_run:
                logging.debug('[DEBUG] Getting command for debugging...')
                try:
                    dry_exit_code, dry_stdout, dry_stderr = builder.run_api(
                        exact_name=exact_name,
                        title_query=None,
                        command_name=api_name,
                        dry_run=True,
                        quiet=True,
                    )
                    if dry_exit_code == 0 and dry_stdout:
                        logging.debug(f'[DEBUG] Command to execute:\n{dry_stdout}')
                except Exception as e:
                    logging.debug(f'[DEBUG] Could not get command preview: {e}')

            # First try with exact name if provided
            exit_code, stdout, stderr = builder.run_api(
                exact_name=exact_name,
                title_query=None,
                command_name=api_name,
                dry_run=dry_run,
                quiet=quiet,
            )

            # If exact name failed and we have a profile parameter, try as title query
            if exit_code != 0 and profile_query and not exact_name and 'exact_name or title_query' in stderr:
                # Log the retry in debug mode
                if debug:
                    logging.debug('[DEBUG] Retrying with profile query as title_query')
                    if not dry_run:
                        try:
                            dry_exit_code, dry_stdout, dry_stderr = builder.run_api(
                                exact_name=None,
                                title_query=profile_query,
                                command_name=api_name,
                                dry_run=True,
                                quiet=True,
                            )
                            if dry_exit_code == 0 and dry_stdout:
                                logging.debug(f'[DEBUG] Command to execute:\n{dry_stdout}')
                        except Exception as e:
                            logging.debug(f'[DEBUG] Could not get command preview: {e}')

                exit_code, stdout, stderr = builder.run_api(
                    exact_name=None,
                    title_query=profile_query,
                    command_name=api_name,
                    dry_run=dry_run,
                    quiet=quiet,
                )

            # Check if command failed and add formatted error information
            result = {
                'success': exit_code == 0,
                'exit_code': exit_code,
                'stdout': stdout,
                'stderr': stderr,
                'params_used': params,
            }

            # If command failed, add formatted error message
            if exit_code != 0:
                error_info = _format_error_response(exit_code, stdout, stderr)
                result['error_message'] = error_info['error_message']

            return result

        except Exception as e:
            return {
                'success': False,
                'exit_code': 1,
                'stdout': '',
                'stderr': str(e),
                'error_message': f'❌ EXECUTION EXCEPTION\n\n🔍 ERROR DETAILS:\n{str(e)}',
                'params_used': params,
            }

    except Exception as e:
        return {
            'success': False,
            'exit_code': 1,
            'stdout': '',
            'stderr': f'Command execution failed: {str(e)}',
            'error_message': f'❌ COMMAND EXECUTION FAILED\n\n🔍 ERROR DETAILS:\n{str(e)}',
            'params_used': params,
        }

    finally:
        # Always cleanup Builder resources
        if builder:
            builder.cleanup()


def create_argument_parser():
    """Create argument parser with the same interface as the original CLI."""
    parser = argparse.ArgumentParser(
        description='Hagent build tool - Unified interface for all build profiles',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""Examples:
  # List all profiles
  %(prog)s --list

  # List APIs for a title substring
  %(prog)s --profile "Pipelined Dual Issue" --list-apis

  # Select by exact unique name (preferred)
  %(prog)s --name PipelinedDualIssueNoDbg --api compile

  # Select by title substring (legacy 'description' is now 'title')
  %(prog)s --profile "Single Cycle CPU" --api compile

  # Dry run
  %(prog)s --name GCD --api compile --dry-run
        """,
    )

    parser.add_argument('--config', help='Path to hagent.yaml')
    parser.add_argument('--schema', action='store_true', help='Print MCP tool schema as JSON')
    parser.add_argument('--list', action='store_true', help='List all profiles')

    # Selection:
    parser.add_argument('--name', '-N', help="Exact profile 'name' (unique, case-insensitive)")
    parser.add_argument('--profile', '-p', help="Substring match on profile 'description')")

    # Actions:
    parser.add_argument('--list-apis', action='store_true', help='List APIs for the selected/matched profiles')
    parser.add_argument('--api', '-a', help='API to execute (compile, lint, synthesize, etc.)')

    parser.add_argument('--dry-run', '-n', action='store_true', help='Show what would be executed without running')
    parser.add_argument('--debug', action='store_true', help='Enable debug mode: print commands and use verbose output')
    parser.add_argument('extra_args', nargs=argparse.REMAINDER, help='Extra arguments to pass to the command (after --)')

    return parser


def main():
    """Standard CLI entry point with both MCP schema and CLI argument handling."""
    import sys
    import json

    # Handle CLI arguments
    parser = create_argument_parser()
    args = parser.parse_args()

    # Handle --schema option
    if args.schema:
        schema = get_mcp_schema(config_path=args.config)
        print(json.dumps(schema, indent=2))
        return 0

    if args.extra_args and args.extra_args[0] == '--':
        args.extra_args = args.extra_args[1:]

    # Set config path in environment if provided
    if args.config:
        os.environ['HAGENT_CONFIG_PATH'] = args.config

    try:
        # Convert CLI args to MCP params format
        params = {
            'name': args.name,
            'profile': args.profile,
            'api': args.api,
            'dry_run': args.dry_run if hasattr(args, 'dry_run') else False,
            'debug': args.debug if hasattr(args, 'debug') else False,
        }

        # Handle list operations (no API specified)
        if args.list or args.list_apis:
            params['api'] = None

        # Execute through MCP interface
        result = mcp_execute(params)

        # Handle output
        print('STDOUT:')
        print(result['stdout'], end='')
        print('\n\nSTDERR:', file=sys.stderr)
        print(result['stderr'], end='', file=sys.stderr)

        if 'error_message' in result:
            print('error_message:', file=sys.stderr)
            print(result['error_message'], end='', file=sys.stderr)
        else:
            print('error_message: NONE', file=sys.stderr)

        # Return appropriate exit code
        if 'exit_code' in result:
            return result['exit_code']

        return 0 if result.get('success', False) else 1

    except FileNotFoundError as e:
        print(f'Error: {e}', file=sys.stderr)
        return 1
    except ValueError as e:
        # Descriptive selection/matching errors
        print(f'Error: {e}', file=sys.stderr)
        return 2
    except Exception as e:
        print(f'Error: {e}', file=sys.stderr)
        import traceback

        traceback.print_exc()
        return 1


if __name__ == '__main__':
    sys.exit(main())
