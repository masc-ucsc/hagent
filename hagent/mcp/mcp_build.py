#!/usr/bin/env python3
"""
MCP Command: Build

HAgent build command with both CLI and MCP interfaces.
Provides access to HAgent profile-based build operations.
"""

import sys
from pathlib import Path
from typing import Dict, Any

# Add the project root to the path so we can import hagent modules
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))

try:
    from hagent.core.tests.cli_hagent_build import main as cli_main
except ImportError:
    print('Error: Could not import the new hagent-build implementation.', file=sys.stderr)
    print('Please ensure the hagent package is properly installed.', file=sys.stderr)
    sys.exit(1)


def get_mcp_schema() -> Dict[str, Any]:
    """Return MCP tool schema for HAgent build command with dynamic profile/API information."""

    # Try to get actual available profiles and APIs from the current environment
    available_profiles = []
    available_apis = []
    profiles_description = ''

    try:
        # Use CLI directly to get profiles in current environment
        import subprocess
        import re
        import os

        # Set up environment for the subprocess call
        env = os.environ.copy()
        if 'HAGENT_EXECUTION_MODE' not in env:
            env['HAGENT_EXECUTION_MODE'] = 'docker'

        # Call the CLI with --list to get current profiles
        result = subprocess.run([sys.executable, __file__, '--list'], env=env, capture_output=True, text=True, timeout=30)

        if result.returncode == 0:
            profiles_output = result.stdout
            profiles_description = f'\n\nCurrent Available Profiles:\n{profiles_output}'

            # Extract profile names (lines starting with "name: ")
            profile_matches = re.findall(r'^name: (\w+)', profiles_output, re.MULTILINE)
            available_profiles = profile_matches

            # Extract API names (lines with "- api_name: description")
            api_matches = re.findall(r'^\s*-\s*(\w+):', profiles_output, re.MULTILINE)
            # Remove duplicates and keep unique APIs
            available_apis = list(set(api_matches))

        else:
            # Fallback to static list if dynamic discovery fails
            available_profiles = ['echo', 'gcd', 'singlecyclecpu_nd', 'singlecyclecpu_d', 'pipelined_d', 'pipelined_nd']
            available_apis = ['compile', 'lint', 'synthesize', 'build_dir', 'repo_dir']
            profiles_description = (
                f'\n\nNote: Could not get current profiles (stderr: {result.stderr[:200]}). Use --list to see available profiles.'
            )

    except Exception as e:
        # Fallback to static list if any error occurs
        available_profiles = ['echo', 'gcd', 'singlecyclecpu_nd', 'singlecyclecpu_d', 'pipelined_d', 'pipelined_nd']
        available_apis = ['compile', 'lint', 'synthesize', 'build_dir', 'repo_dir']
        profiles_description = f'\n\nNote: Could not get current profiles ({str(e)[:100]}). Use --list to see available profiles.'

    # Clean up the profiles description - extract just the profiles info without the CLI header
    clean_description = profiles_description
    if profiles_description and 'Available profiles:' in profiles_description:
        # Extract everything after "Available profiles:" line
        lines = profiles_description.split('\n')
        profile_start_idx = None
        for i, line in enumerate(lines):
            if 'Available profiles:' in line:
                profile_start_idx = i + 2  # Skip the "Available profiles:" and "----" lines
                break
        if profile_start_idx:
            clean_description = '\n'.join(lines[profile_start_idx:]).strip()

    # Use clean description or fallback
    final_description = (
        clean_description
        if clean_description and not clean_description.startswith('Note:')
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
                    'description': 'Profile or target name (exact match, case-insensitive)',
                    'enum': available_profiles,
                }
                if available_profiles
                else {'type': 'string', 'description': 'Profile or target name (exact match, case-insensitive)'},
                'profile': {
                    'type': 'string',
                    'description': 'Profile name or regex pattern to match in titles/descriptions',
                },
                'api': {
                    'type': 'string',
                    'description': 'API or command to execute',
                    'enum': available_apis,
                }
                if available_apis
                else {'type': 'string', 'description': 'API or command to execute'},
                'dry_run': {'type': 'boolean', 'description': 'Show what would be executed without running', 'default': False},
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
    try:
        # Build argument list from simplified MCP parameters
        args = []

        # Handle both exact name matching and profile regex matching
        if params.get('name'):
            args.extend(['--name', params['name']])
        elif params.get('profile'):
            # Profile parameter does regex matching on descriptions
            # First try exact name match, if fails try title_query
            args.extend(['--name', params['profile']])

        if params.get('api'):
            args.extend(['--api', params['api']])

        if params.get('dry_run', False):
            args.append('--dry-run')

        # Run as subprocess to properly capture ALL output including SBT errors
        import subprocess
        import os

        try:
            cli_args = [sys.executable, __file__] + args

            process = subprocess.run(cli_args, capture_output=True, text=True, cwd=os.getcwd(), env=os.environ.copy())

            exit_code = process.returncode
            stdout_output = process.stdout
            stderr_output = process.stderr

            # If exact name failed and we used profile parameter, try title_query for regex matching
            if exit_code != 0 and params.get('profile') and 'exact_name or title_query' in stderr_output:
                # Retry with title_query for profile regex matching
                retry_args = []
                if params.get('profile'):
                    retry_args.extend(['--title-query', params['profile']])
                if params.get('api'):
                    retry_args.extend(['--api', params['api']])
                if params.get('dry_run', False):
                    retry_args.append('--dry-run')

                retry_cli_args = [sys.executable, __file__] + retry_args
                retry_process = subprocess.run(
                    retry_cli_args, capture_output=True, text=True, cwd=os.getcwd(), env=os.environ.copy()
                )

                # Use retry results if successful, otherwise keep original error
                if retry_process.returncode == 0:
                    exit_code = retry_process.returncode
                    stdout_output = retry_process.stdout
                    stderr_output = retry_process.stderr
                else:
                    # Combine both error messages for clarity
                    stderr_output += f'\n\nAlso tried regex matching with --title-query:\n{retry_process.stderr}'

        except Exception as e:
            exit_code = 1
            stdout_output = ''
            stderr_output = f'Error running command: {str(e)}'

        return {
            'success': exit_code == 0,
            'exit_code': exit_code,
            'stdout': stdout_output,
            'stderr': stderr_output,
            'params_used': params,
        }

    except Exception as e:
        return {'success': False, 'error': f'Command execution failed: {str(e)}', 'params_used': params}


def main():
    """Standard CLI entry point maintaining backward compatibility."""
    import sys

    # Check for --schema flag first before delegating to shared implementation
    if len(sys.argv) > 1 and sys.argv[1] == '--schema':
        import json

        schema = get_mcp_schema()
        print(json.dumps(schema, indent=2))
        return 0

    # If called from MCP without arguments, don't print the extra message
    # The MCP server will handle parameter parsing via mcp_execute()
    if len(sys.argv) == 1:
        # No arguments provided - this is likely an MCP call that will be handled by mcp_execute
        # Just delegate to cli_main without extra print
        return cli_main()

    print('Calling hagent.core.tests.cli_hagent_build')
    return cli_main()


if __name__ == '__main__':
    sys.exit(main())
