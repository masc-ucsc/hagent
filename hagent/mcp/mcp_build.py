#!/usr/bin/env python3
"""
MCP Command: Build

HAgent build command with both CLI and MCP interfaces.
Provides access to HAgent profile-based build operations.
"""

import sys
import io
from pathlib import Path
from typing import Dict, Any

# Add the project root to the path so we can import hagent modules
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))

try:
    from hagent.core.tests.cli_hagent_build import main as cli_main, HagentBuilder
except ImportError:
    print('Error: Could not import the new hagent-build implementation.', file=sys.stderr)
    print('Please ensure the hagent package is properly installed.', file=sys.stderr)
    sys.exit(1)


def get_mcp_schema() -> Dict[str, Any]:
    """Return MCP tool schema for HAgent build command."""
    return {
        'name': 'hagent_build',
        'description': 'Execute HAgent build profiles and APIs (compile, lint, synthesize, etc.)',
        'inputSchema': {
            'type': 'object',
            'properties': {
                'config': {'type': 'string', 'description': 'Path to hagent.yaml configuration file'},
                'list': {'type': 'boolean', 'description': 'List all available profiles', 'default': False},
                'name': {'type': 'string', 'description': 'Exact profile name (unique, case-insensitive)'},
                'profile': {'type': 'string', 'description': 'Substring match on profile description/title'},
                'list_apis': {'type': 'boolean', 'description': 'List APIs for the selected profile', 'default': False},
                'api': {'type': 'string', 'description': 'API to execute (compile, lint, synthesize, etc.)'},
                'dry_run': {'type': 'boolean', 'description': 'Show what would be executed without running', 'default': False},
                'extra_args': {
                    'type': 'array',
                    'items': {'type': 'string'},
                    'description': 'Extra arguments to pass to the command',
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
    try:
        # Capture stdout and stderr to return structured results
        old_stdout = sys.stdout
        old_stderr = sys.stderr
        stdout_buffer = io.StringIO()
        stderr_buffer = io.StringIO()

        try:
            sys.stdout = stdout_buffer
            sys.stderr = stderr_buffer

            # Build argument list from MCP parameters
            args = []

            if params.get('config'):
                args.extend(['--config', params['config']])

            if params.get('list', False):
                args.append('--list')

            if params.get('name'):
                args.extend(['--name', params['name']])

            if params.get('profile'):
                args.extend(['--profile', params['profile']])

            if params.get('list_apis', False):
                args.append('--list-apis')

            if params.get('api'):
                args.extend(['--api', params['api']])

            if params.get('dry_run', False):
                args.append('--dry-run')

            if params.get('extra_args'):
                args.append('--')
                args.extend(params['extra_args'])

            # Temporarily replace sys.argv to simulate CLI call
            original_argv = sys.argv
            sys.argv = ['hagent-build'] + args

            try:
                exit_code = cli_main()
            finally:
                sys.argv = original_argv

        finally:
            sys.stdout = old_stdout
            sys.stderr = old_stderr

        stdout_output = stdout_buffer.getvalue()
        stderr_output = stderr_buffer.getvalue()

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
    print('hagent-builder using conf.yaml configuration (delegating to shared implementation)')
    return cli_main()


if __name__ == '__main__':
    sys.exit(main())
