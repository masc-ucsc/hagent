#!/usr/bin/env python3
"""
MCP Command: Build

HAgent build command with unified CLI and MCP interfaces.
Provides access to HAgent profile-based build operations through the Builder class.
"""

import os
import argparse
import sys
from typing import Dict, Any


from hagent.inou.builder import Builder


def get_mcp_schema() -> Dict[str, Any]:
    """Return MCP tool schema for HAgent build command with dynamic profile/API information."""

    # Try to get actual available profiles and APIs from the current environment
    available_profiles = []
    available_apis = []
    profiles_description = ''

    try:
        # Use Builder directly to get profiles in current environment
        # For schema generation, we don't need Docker - just YAML config reading
        builder = Builder()

        # Get all profiles and APIs
        profiles = builder.get_all_profiles()
        available_profiles = [p.get('name', '') for p in profiles if p.get('name')]

        # Collect unique API names across all profiles
        api_set = set()
        for profile in profiles:
            for api in profile.get('apis', []):
                if api.get('name'):
                    api_set.add(api.get('name'))
        available_apis = list(api_set)

        # Generate description from profiles
        if profiles:
            description_lines = []
            for p in profiles:
                name = p.get('name', '<unnamed>')
                title = builder.profile_title(p) or 'N/A'
                description_lines.append(f'\nname: {name}')
                description_lines.append(f'  title: {title}')
                description_lines.append('  APIs:')
                for api in p.get('apis', []):
                    api_name = api.get('name', '<noname>')
                    api_desc = api.get('description', 'N/A')
                    description_lines.append(f'    - {api_name}: {api_desc}')

            profiles_description = '\n'.join(description_lines)
        else:
            profiles_description = 'No profiles found'

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
    builder = None
    try:
        # Initialize Builder
        builder = Builder()

        # Handle parameters
        exact_name = params.get('name')
        profile_query = params.get('profile')
        api_name = params.get('api')
        dry_run = params.get('dry_run', False)

        # If no API specified, this might be a listing request (no setup needed)
        if not api_name:
            # Default to showing available profiles if no specific action
            if exact_name or profile_query:
                # Try to list APIs for the specified profile
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
                    builder.list_profiles()
                    return {
                        'success': True,
                        'exit_code': 0,
                        'stdout': 'Profiles listed successfully',
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

        # Only setup if not dry run and we need to execute something (setup requires full Docker/Runner infrastructure)
        if not dry_run and not builder.setup():
            return {
                'success': False,
                'error': f'Builder setup failed: {builder.get_error()}',
                'params_used': params,
            }

        # Execute the command
        try:
            # First try with exact name if provided
            exit_code, stdout, stderr = builder.execute(
                exact_name=exact_name,
                title_query=None,
                command_name=api_name,
                dry_run=dry_run,
                quiet=False,
            )

            # If exact name failed and we have a profile parameter, try as title query
            if exit_code != 0 and profile_query and not exact_name and 'exact_name or title_query' in stderr:
                exit_code, stdout, stderr = builder.execute(
                    exact_name=None,
                    title_query=profile_query,
                    command_name=api_name,
                    dry_run=dry_run,
                    quiet=False,
                )

            return {
                'success': exit_code == 0,
                'exit_code': exit_code,
                'stdout': stdout,
                'stderr': stderr,
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

    except Exception as e:
        return {
            'success': False,
            'error': f'Command execution failed: {str(e)}',
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
    parser.add_argument('--list', action='store_true', help='List all profiles')

    # Selection:
    parser.add_argument('--name', '-N', help="Exact profile 'name' (unique, case-insensitive)")
    parser.add_argument('--profile', '-p', help="Substring match on profile 'description')")

    # Actions:
    parser.add_argument('--list-apis', action='store_true', help='List APIs for the selected/matched profiles')
    parser.add_argument('--api', '-a', help='API to execute (compile, lint, synthesize, etc.)')

    parser.add_argument('--dry-run', '-n', action='store_true', help='Show what would be executed without running')
    parser.add_argument('extra_args', nargs=argparse.REMAINDER, help='Extra arguments to pass to the command (after --)')

    return parser


def main():
    """Standard CLI entry point with both MCP schema and CLI argument handling."""
    import sys
    import json

    # Check for --schema flag first for MCP integration
    if len(sys.argv) > 1 and sys.argv[1] == '--schema':
        schema = get_mcp_schema()
        print(json.dumps(schema, indent=2))
        return 0

    # Handle CLI arguments
    parser = create_argument_parser()
    args = parser.parse_args()

    if args.extra_args and args.extra_args[0] == '--':
        args.extra_args = args.extra_args[1:]

    builder = None
    try:
        # Handle operations that don't require Docker first
        if args.list or args.list_apis:
            builder = Builder(config_path=args.config)
            if args.list:
                builder.list_profiles()
                return 0
        
        # For execution commands, require Docker
        docker_image = os.environ.get('HAGENT_DOCKER')
        if not docker_image:
            print('ERROR: mcp_builder needs a HAGENT_DOCKER specified to run tools')
            return 3

        if not builder:  # Create builder with Docker if not already created
            builder = Builder(config_path=args.config, docker_image=docker_image)

        # Only setup for operations that require execution (not dry run, not list operations)
        if not args.dry_run and not args.list_apis and not builder.setup():
            print(f'Error: Builder setup failed: {builder.get_error()}', file=sys.stderr)
            return 1

        # List APIs for selected profiles.
        if args.list_apis:
            success = builder.list_apis_for_profile(args.name, args.profile)
            return 0 if success else 2

        # Execute selected API
        if args.api:
            exit_code, stdout, stderr = builder.execute(
                exact_name=args.name,
                title_query=args.profile,
                command_name=args.api,
                extra_args=args.extra_args,
                dry_run=args.dry_run,
                quiet=False,
            )

            # Print stdout and stderr if they contain anything
            if stdout:
                print(stdout, end='')
            if stderr:
                print(stderr, end='', file=sys.stderr)

            return exit_code

        parser.print_help()
        return 0

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

    finally:
        # Always cleanup Builder resources
        if builder:
            builder.cleanup()


if __name__ == '__main__':
    sys.exit(main())
