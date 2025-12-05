#!/usr/bin/env python3
# See LICENSE for details
"""
Command-line tool for equivalence checking between multiple Verilog files.

This tool allows you to specify multiple gold (reference) files and multiple gate (implementation) files,
then performs equivalence checking between all matching top modules.

Usage:
  uv run python ./hagent/tool/tests/cli_equiv_check.py -r gold1.v -r gold2.v -i test1.v
  uv run python ./hagent/tool/tests/cli_equiv_check.py --reference gold.v --implementation impl.v
  uv run python ./hagent/tool/tests/cli_equiv_check.py -r ref/*.v -i impl/*.v

The tool will:
1. Read all gold/reference files and combine them into a single design
2. Read all gate/implementation files and combine them into a single design
3. Find matching top modules between gold and gate based on IO compatibility
4. Run equivalence checking on each matched pair
5. Stop and report counterexample on first mismatch found
"""

import argparse
import sys
import os
import glob
from hagent.tool.equiv_check import Equiv_check
from pathlib import Path


def ensure_hagent_env():
    """
    Ensure HAGENT_CACHE_DIR is set up and default Docker image is selected when not provided.
    Users don't need to set HAGENT_DOCKER manually for this CLI.
    """
    # Default Docker image for Yosys if not provided by user
    os.environ.setdefault('HAGENT_DOCKER', 'mascucsc/hagent-builder:2025.11')

    if not os.environ.get('HAGENT_CACHE_DIR'):
        cache_dir = Path('output/cli_equiv_check/cache').resolve()
        cache_dir.mkdir(parents=True, exist_ok=True)
        os.environ['HAGENT_CACHE_DIR'] = str(cache_dir)


def expand_file_patterns(file_patterns):
    """
    Expand file patterns (including wildcards) into actual file paths.

    Args:
        file_patterns: List of file patterns (may include wildcards)

    Returns:
        List of actual file paths
    """
    expanded_files = []
    for pattern in file_patterns:
        # Expand wildcards
        matches = glob.glob(pattern)
        if matches:
            expanded_files.extend(matches)
        else:
            # If no wildcard matches, treat as literal filename
            expanded_files.append(pattern)
    return expanded_files


def read_verilog_files(file_list):
    """
    Read and combine multiple Verilog files into a single string.

    Args:
        file_list: List of Verilog file paths

    Returns:
        Combined Verilog code as string

    Raises:
        FileNotFoundError: If any file doesn't exist
        IOError: If any file can't be read
    """
    combined_code = []

    for file_path in file_list:
        if not os.path.exists(file_path):
            raise FileNotFoundError(f'File not found: {file_path}')

        try:
            with open(file_path, 'r') as f:
                content = f.read()
                combined_code.append(f'// File: {file_path}')
                combined_code.append(content)
                combined_code.append('')  # Add blank line between files
        except IOError as e:
            raise IOError(f'Error reading file {file_path}: {e}')

    return '\n'.join(combined_code)


def main():
    # Ensure HAGENT_* env vars are available so PathManager can initialize
    ensure_hagent_env()

    parser = argparse.ArgumentParser(
        description='Equivalence checking tool for multiple Verilog files',
        epilog="""
Examples:
  %(prog)s -r gold1.v -r gold2.v -i test1.v
  %(prog)s --reference ref.v --implementation impl.v
  %(prog)s -r ref/*.v -i impl/*.v
  %(prog)s -r gold.v -i impl1.v -i impl2.v -i impl3.v
        """,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    parser.add_argument(
        '-r',
        '--reference',
        action='append',
        dest='gold_files',
        required=True,
        help='Gold/reference Verilog file(s). Can be specified multiple times. Supports wildcards.',
    )

    parser.add_argument(
        '-i',
        '--implementation',
        action='append',
        dest='gate_files',
        required=True,
        help='Gate/implementation Verilog file(s). Can be specified multiple times. Supports wildcards.',
    )

    parser.add_argument('--top', help='Specify a particular top module name to check (optional)')

    parser.add_argument('--verbose', '-v', action='store_true', help='Enable verbose output')

    args = parser.parse_args()

    try:
        # Expand file patterns
        if args.verbose:
            print('Expanding file patterns...')

        gold_files = expand_file_patterns(args.gold_files)
        gate_files = expand_file_patterns(args.gate_files)

        if args.verbose:
            print(f'Gold/Reference files: {gold_files}')
            print(f'Gate/Implementation files: {gate_files}')

        # Validate that all files exist
        all_files = gold_files + gate_files
        missing_files = [f for f in all_files if not os.path.exists(f)]
        if missing_files:
            print('ERROR: The following files do not exist:', file=sys.stderr)
            for f in missing_files:
                print(f'  - {f}', file=sys.stderr)
            sys.exit(1)

        # Read and combine Verilog files
        print('Reading gold/reference files...')
        gold_code = read_verilog_files(gold_files)

        print('Reading gate/implementation files...')
        gate_code = read_verilog_files(gate_files)

        if args.verbose:
            print(f'Combined gold code: {len(gold_code)} characters')
            print(f'Combined gate code: {len(gate_code)} characters')

        # Setup equivalence checker
        print('Setting up equivalence checker...')
        checker = Equiv_check()

        setup_ok = checker.setup()
        if not setup_ok:
            print(f'ERROR: Equivalence checker setup failed: {checker.get_error()}', file=sys.stderr)
            sys.exit(1)

        if args.verbose:
            docker_status = 'via Docker' if checker.use_docker else 'locally'
            print(f'✓ Yosys setup successful ({docker_status})')

        # Run equivalence check
        print('Running equivalence check...')
        try:
            result = checker.check_equivalence(gold_code, gate_code, args.top or '')

            if result is True:
                print('✓ SUCCESS: All modules are equivalent!')
                sys.exit(0)

            elif result is False:
                print('✗ FAILURE: Designs are NOT equivalent!')

                # Get and display counterexample
                counterexample = checker.get_counterexample()
                if counterexample:
                    print('\nCounterexample:')
                    print('=' * 80)
                    print(counterexample)
                    print('=' * 80)
                else:
                    print('No detailed counterexample available.')

                sys.exit(1)

            else:  # result is None
                print('? INCONCLUSIVE: Equivalence check could not be determined.')
                error_msg = checker.get_error()
                if error_msg:
                    print(f'Error: {error_msg}')
                sys.exit(2)

        except ValueError as e:
            print(f'ERROR: {e}', file=sys.stderr)
            sys.exit(1)
        except Exception as e:
            print(f'UNEXPECTED ERROR: {e}', file=sys.stderr)
            sys.exit(1)

    except FileNotFoundError as e:
        print(f'ERROR: {e}', file=sys.stderr)
        sys.exit(1)
    except IOError as e:
        print(f'ERROR: {e}', file=sys.stderr)
        sys.exit(1)
    except KeyboardInterrupt:
        print('\nInterrupted by user.', file=sys.stderr)
        sys.exit(1)


if __name__ == '__main__':
    main()
