#!/usr/bin/env python3
"""
CLI example for Executor functionality

Demonstrates usage of the executor module for command execution in both
local and Docker modes.
"""

import argparse
import sys
import os
from pathlib import Path

# Add parent directory to path to allow direct execution
sys.path.insert(0, str(Path(__file__).parent.parent.parent))

from hagent.inou.executor import run_cmd


def main():
    """Main CLI function."""
    parser = argparse.ArgumentParser(description='Executor CLI Demo')
    parser.add_argument('command', help='Command to execute')
    parser.add_argument('--mode', choices=['local', 'docker'], default='local', help='Execution mode (default: local)')
    parser.add_argument('--docker-image', help='Docker image to use when mode is docker')
    parser.add_argument('--cwd', default='.', help='Working directory (default: current)')
    parser.add_argument('--env', action='append', help='Environment variables in KEY=VALUE format')
    parser.add_argument('--quiet', action='store_true', help='Run in quiet mode')

    args = parser.parse_args()

    # Prepare environment variables
    env_vars = {}
    if args.env:
        for env_pair in args.env:
            if '=' in env_pair:
                key, value = env_pair.split('=', 1)
                env_vars[key] = value
            else:
                print(f'Warning: Invalid environment variable format: {env_pair}', file=sys.stderr)

    # Set execution mode (docker if HAGENT_DOCKER is set, otherwise local)
    if args.mode == 'docker':
        if not args.docker_image:
            print('Error: --docker-image is required when --mode is docker', file=sys.stderr)
            return 1
        os.environ['HAGENT_DOCKER'] = args.docker_image
    else:
        # Ensure HAGENT_DOCKER is not set for local mode
        os.environ.pop('HAGENT_DOCKER', None)

    try:
        print(f"Executing '{args.command}' in {args.mode} mode...")

        # Use convenience function
        exit_code, stdout, stderr = run_cmd(args.command, cwd=args.cwd, env=env_vars, quiet=args.quiet)

        print(f'\nExit code: {exit_code}')
        if stdout:
            print(f'STDOUT:\n{stdout}')
        if stderr:
            print(f'STDERR:\n{stderr}')

        return exit_code

    except Exception as e:
        print(f'Error: {e}', file=sys.stderr)
        return 1


if __name__ == '__main__':
    sys.exit(main())
