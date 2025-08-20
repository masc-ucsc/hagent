#!/usr/bin/env python3
"""
MCP Command Template

This is a template for creating new HAgent MCP commands. Copy this file to
create new mcp_*.py commands that will be automatically discovered by the
MCP server.

Required functions:
- get_mcp_schema(): Return MCP tool schema
- mcp_execute(): Execute command with MCP parameters
- main(): CLI entry point (optional, for backward compatibility)
"""

import argparse
import sys
from typing import Dict, Any


def get_mcp_schema() -> Dict[str, Any]:
    """
    Return MCP tool schema for this command.

    This function defines the interface that Claude Code will see.
    Modify the schema below to match your command's parameters.
    """
    return {
        'name': 'hagent_template',
        'description': 'Template command for HAgent MCP integration',
        'inputSchema': {
            'type': 'object',
            'properties': {
                'input_param': {'type': 'string', 'description': 'Example input parameter'},
                'optional_param': {'type': 'string', 'description': 'Example optional parameter', 'default': 'default_value'},
                'flag_param': {'type': 'boolean', 'description': 'Example boolean flag', 'default': False},
            },
            'required': ['input_param'],
        },
    }


def mcp_execute(params: Dict[str, Any]) -> Dict[str, Any]:
    """
    MCP execution entry point.

    Args:
        params: Dictionary containing the input parameters from Claude Code

    Returns:
        Dictionary with execution results in a structured format
    """
    try:
        # Extract parameters with defaults
        input_param = params.get('input_param')
        optional_param = params.get('optional_param', 'default_value')
        flag_param = params.get('flag_param', False)

        # Validate required parameters
        if not input_param:
            return {'success': False, 'error': 'Missing required parameter: input_param'}

        # Your command implementation goes here
        result = execute_command_logic(input_param, optional_param, flag_param)

        return {
            'success': True,
            'result': result,
            'input_param': input_param,
            'optional_param': optional_param,
            'flag_param': flag_param,
        }

    except Exception as e:
        return {'success': False, 'error': f'Command execution failed: {str(e)}'}


def execute_command_logic(input_param: str, optional_param: str, flag_param: bool) -> str:
    """
    Core command logic - replace this with your actual implementation.

    Args:
        input_param: The main input parameter
        optional_param: Optional parameter with default
        flag_param: Boolean flag parameter

    Returns:
        Command execution result
    """
    result = f"Template command executed with input='{input_param}'"

    if optional_param != 'default_value':
        result += f", optional='{optional_param}'"

    if flag_param:
        result += ' (flag enabled)'

    return result


def main():
    """
    Standard CLI entry point with argparse.

    This allows the command to be used both via MCP and traditional CLI.
    Modify the argument parser to match your command's interface.
    """
    parser = argparse.ArgumentParser(description='Template HAgent MCP command')

    parser.add_argument('input_param', help='Example input parameter')
    parser.add_argument('--optional-param', default='default_value', help='Example optional parameter')
    parser.add_argument('--flag-param', action='store_true', help='Example boolean flag')

    args = parser.parse_args()

    # Convert CLI args to MCP params format and execute
    params = {'input_param': args.input_param, 'optional_param': args.optional_param, 'flag_param': args.flag_param}

    result = mcp_execute(params)

    if result['success']:
        print(result['result'])
        sys.exit(0)
    else:
        print(f'Error: {result["error"]}', file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
