#!/usr/bin/env python3
"""
CLI wrapper for HagentBuildCore that maintains compatibility with the original hagent-build.py script.

This provides a shell-based execution strategy and preserves the original CLI interface.
"""

import argparse
import sys
from typing import List, Optional

from hagent.core.hagent_build import HagentBuildCore
from hagent.inou.executor import create_executor


class HagentBuilder:
    """
    CLI wrapper for HagentBuildCore that maintains backward compatibility.

    This class provides the same interface as the original HagentBuilder
    while delegating core functionality to HagentBuildCore.
    """

    def __init__(self, config_path: Optional[str] = None):
        """Initialize with appropriate execution strategy based on HAGENT_EXECUTION_MODE."""
        if config_path is None:
            config_path = HagentBuildCore.find_config()

        # Use factory to create appropriate executor based on HAGENT_EXECUTION_MODE
        execution_strategy = create_executor()

        # Setup the execution strategy
        if not execution_strategy.setup():
            raise RuntimeError(
                f'Failed to setup execution strategy: {getattr(execution_strategy, "error_message", "Unknown error")}'
            )

        self.core = HagentBuildCore(config_path, execution_strategy)

        # Expose properties for backward compatibility
        self.config_path = self.core.config_path
        self.config = self.core.config
        self.repo_dir = self.core.repo_dir
        self.build_base = self.core.build_base

    # ---------------------------- listing methods ----------------------------

    def list_profiles(self):
        """List all available profiles."""
        print('\nAvailable profiles:')
        print('-' * 60)
        for p in self.core.get_all_profiles():
            print(f'\nname: {p.get("name", "<unnamed>")}')
            print(f'  title: {HagentBuildCore.profile_title(p) or "N/A"}')
            print('  APIs:')
            for api in p.get('apis', []):
                print(f'    - {api.get("name", "<noname>")}: {api.get("description", "N/A")}')

    def list_apis_for(self, profs: List[dict]):
        """List APIs for given profiles."""
        for p in profs:
            print(f'\nAPIs for {p.get("name", "<unnamed>")} [{HagentBuildCore.profile_title(p) or "N/A"}]:')
            for api in p.get('apis', []):
                line = f'  {api.get("name", "<noname>")}: {api.get("description", "N/A")}'
                if 'command' in api:
                    line += f'\n    Command: {api["command"]}'
                print(line)

    # ---------------------------- execution ----------------------------

    def execute(
        self,
        exact_name: Optional[str],
        title_query: Optional[str],
        api_name: str,
        extra_args: List[str] = None,
        dry_run: bool = False,
    ) -> int:
        """
        Execute a command with the original interface.

        Args:
            exact_name: Exact profile name match
            title_query: Title query for profile matching
            api_name: Name of the API/command to execute
            extra_args: Extra arguments to pass to command
            dry_run: Whether to perform a dry run

        Returns:
            Exit code
        """
        try:
            # Use the core's execution method which respects the execution strategy
            exit_code, stdout, stderr = self.core.execute(
                exact_name=exact_name,
                title_query=title_query,
                command_name=api_name,
                extra_args=extra_args,
                build_dir=self.build_base,
                dry_run=dry_run,
                quiet=False,
            )

            # Print stdout and stderr if they contain anything
            if stdout:
                print(stdout, end='')
            if stderr:
                print(stderr, end='', file=sys.stderr)

            return exit_code

        except Exception as e:
            print(f'Error: {e}', file=sys.stderr)
            return 1


def main():
    """Main CLI entry point maintaining original interface."""
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

    args = parser.parse_args()

    if args.extra_args and args.extra_args[0] == '--':
        args.extra_args = args.extra_args[1:]

    try:
        builder = HagentBuilder(args.config)

        if args.list:
            builder.list_profiles()
            return 0

        # List APIs for selected profiles.
        if args.list_apis:
            if args.name:
                hits = builder.core.find_profile_by_name(args.name)
                if not hits:
                    # Exact error text required by user.
                    avail = ', '.join(p.get('name', '<unnamed>') for p in builder.core.get_all_profiles())
                    print(f"Error: No profile matched --name '{args.name}'. Available names: {avail}", file=sys.stderr)
                    return 2
                if len(hits) > 1:
                    print(
                        f"Error: --name '{args.name}' matched multiple profiles: " + ', '.join(p.get('name') for p in hits),
                        file=sys.stderr,
                    )
                    return 2
                builder.list_apis_for(hits)
                return 0
            elif args.profile:
                hits = builder.core.find_profile_by_title(args.profile)
                if not hits:
                    print(f"Error: --profile '{args.profile}' did not match any profile titles.", file=sys.stderr)
                    builder.list_profiles()
                    return 2
                if len(hits) > 1:
                    print('Error: Multiple profiles matched --profile. Disambiguate with --name.\nMatches:', file=sys.stderr)
                    for p in hits:
                        print(f'  {p.get("name")} : {HagentBuildCore.profile_title(p) or "N/A"}', file=sys.stderr)
                    return 2
                builder.list_apis_for(hits)
                return 0
            else:
                print('Error: --list-apis requires either --name or --profile.', file=sys.stderr)
                return 2

        # Execute selected API
        if args.api:
            return builder.execute(args.name, args.profile, api_name=args.api, extra_args=args.extra_args, dry_run=args.dry_run)

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


if __name__ == '__main__':
    sys.exit(main())
