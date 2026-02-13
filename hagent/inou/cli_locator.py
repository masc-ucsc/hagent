#!/usr/bin/env python3
"""CLI tool for Locator - Map variables and code between HDL representations.

This tool provides command-line access to the Locator functionality for mapping
variables and code changes between different HDL representations (VCD, Verilog, Chisel, Netlist).

Environment Variables:
    HAGENT_REPO_DIR: Repository directory (default: current directory)
    HAGENT_BUILD_DIR: Build output directory
    HAGENT_CACHE_DIR: Cache directory
    HAGENT_DOCKER: Docker image to use (if set, docker mode is enabled)

Examples:
    # Map VCD signal to Verilog source
    python -m hagent.inou.cli_locator --api locate_vcd --to verilog --name gcd "top.gcd.x"

    # Map Verilog variable to Chisel source
    python -m hagent.inou.cli_locator --api map_variable --from verilog --to chisel --name gcd "x"

    # Map Verilog diff to Chisel source (reads from stdin)
    cat changes.diff | python -m hagent.inou.cli_locator --api locate_code --from verilog --to chisel --name gcd
"""

import argparse
import sys
from typing import Optional

from hagent.inou.locator import Locator, RepresentationType, SourceLocation


def parse_representation(rep_str: str) -> RepresentationType:
    """Parse representation type from string (case-insensitive).

    Args:
        rep_str: String representation ('vcd', 'verilog', 'chisel', 'netlist')
                 Case insensitive - VCD, Verilog, CHISEL, etc. all work

    Returns:
        RepresentationType enum value

    Raises:
        ValueError: If representation type is invalid
    """
    rep_map = {
        'vcd': RepresentationType.VCD,
        'verilog': RepresentationType.VERILOG,
        'chisel': RepresentationType.CHISEL,
        'netlist': RepresentationType.NETLIST,
    }

    rep_lower = rep_str.lower()
    if rep_lower not in rep_map:
        raise ValueError(f"Invalid representation '{rep_str}'. Valid values (case-insensitive): {', '.join(rep_map.keys())}")

    return rep_map[rep_lower]


def format_location(loc: SourceLocation, verbose: bool = False) -> str:
    """Format a SourceLocation for display.

    Args:
        loc: SourceLocation to format
        verbose: If True, show detailed information

    Returns:
        Formatted string representation
    """
    if verbose:
        return (
            f'{loc.file_path}:{loc.line_start}-{loc.line_end}\n'
            f'  Module: {loc.module_name}\n'
            f'  Confidence: {loc.confidence:.2f}\n'
            f'  Representation: {loc.representation.value}'
        )
    else:
        return f'{loc.file_path}:{loc.line_start}-{loc.line_end}'


def run_locate_vcd(
    locator: Locator,
    vcd_variable: str,
    to_type: RepresentationType,
    verbose: bool = False,
) -> int:
    """Map VCD hierarchical signal to target representation.

    Args:
        locator: Initialized Locator instance
        vcd_variable: VCD hierarchical path (e.g., "top.cpu.alu.result")
        to_type: Target representation type
        verbose: Show detailed output

    Returns:
        Exit code (0 for success, 1 for failure)
    """
    if verbose:
        print(
            f"Mapping VCD signal '{vcd_variable}' to {to_type.value}...",
            file=sys.stderr,
        )

    locations = locator.locate_vcd(to=to_type, vcd_variable=vcd_variable)

    if not locations:
        error = locator.get_error()
        if error:
            print(f'Error: {error}', file=sys.stderr)
        else:
            print(f"No locations found for VCD signal '{vcd_variable}'", file=sys.stderr)
        return 1

    # Print results
    if verbose:
        print(f'\nFound {len(locations)} location(s):\n', file=sys.stderr)

    for i, loc in enumerate(locations, 1):
        if verbose:
            print(f'[{i}] {format_location(loc, verbose=True)}\n')
        else:
            print(format_location(loc, verbose=False))

    return 0


def run_map_variable(
    locator: Locator,
    variable: str,
    from_type: RepresentationType,
    to_type: RepresentationType,
    module: str,
    verbose: bool = False,
) -> int:
    """Map variable across representations (cross-representation mapping).

    Args:
        locator: Initialized Locator instance
        variable: Variable name or regex pattern
        from_type: Source representation type
        to_type: Target representation type
        module: Module/class name to constrain search
        verbose: Show detailed output

    Returns:
        Exit code (0 for success, 1 for failure)
    """
    if verbose:
        print(
            f"Mapping variable '{variable}' from {from_type.value} to {to_type.value} in module '{module}'...",
            file=sys.stderr,
        )

    locations = locator.map_variable(to=to_type, from_type=from_type, variable=variable, module=module)

    if not locations:
        error = locator.get_error()
        if error:
            print(f'Error: {error}', file=sys.stderr)
        else:
            print(f"No locations found for variable '{variable}' in module '{module}'", file=sys.stderr)
        return 1

    # Print results
    if verbose:
        print(f'\nFound {len(locations)} location(s):\n', file=sys.stderr)

    for i, loc in enumerate(locations, 1):
        if verbose:
            print(f'[{i}] {format_location(loc, verbose=True)}\n')
        else:
            print(format_location(loc, verbose=False))

    return 0


def run_locate_variable(
    locator: Locator,
    variable: str,
    to_type: RepresentationType,
    module: Optional[str],
    verbose: bool = False,
) -> int:
    """Find variable within a single representation.

    Args:
        locator: Initialized Locator instance
        variable: Variable name or regex pattern
        to_type: Representation type to search in
        module: Optional module/class name to constrain search
        verbose: Show detailed output

    Returns:
        Exit code (0 for success, 1 for failure)
    """
    if verbose:
        module_str = f" in module '{module}'" if module else ' across all modules'
        print(
            f"Locating variable '{variable}' in {to_type.value}{module_str}...",
            file=sys.stderr,
        )

    locations = locator.locate_variable(to=to_type, variable=variable, module=module)

    if not locations:
        error = locator.get_error()
        if error:
            print(f'Error: {error}', file=sys.stderr)
        else:
            module_str = f" in module '{module}'" if module else ''
            print(f"No locations found for variable '{variable}'{module_str}", file=sys.stderr)
        return 1

    # Print results
    if verbose:
        print(f'\nFound {len(locations)} location(s):\n', file=sys.stderr)

    for i, loc in enumerate(locations, 1):
        if verbose:
            print(f'[{i}] {format_location(loc, verbose=True)}\n')
        else:
            print(format_location(loc, verbose=False))

    return 0


def locate_code(
    locator: Locator,
    diff_patch: str,
    from_type: RepresentationType,
    to_type: RepresentationType,
    verbose: bool = False,
) -> int:
    """Locate code changes across representations.

    Args:
        locator: Initialized Locator instance
        diff_patch: Unified diff string
        from_type: Source representation type
        to_type: Target representation type
        verbose: Show detailed output

    Returns:
        Exit code (0 for success, 1 for failure)
    """
    if verbose:
        print(
            f'Mapping code changes from {from_type.value} to {to_type.value}...',
            file=sys.stderr,
        )

    locations = locator.locate_code(to=to_type, from_type=from_type, diff_patch=diff_patch)

    if not locations:
        error = locator.get_error()
        if error:
            print(f'Error: {error}', file=sys.stderr)
        else:
            print('No locations found for code changes', file=sys.stderr)
        return 1

    # Print results
    if verbose:
        print(f'\nFound {len(locations)} location(s):\n', file=sys.stderr)

    for i, loc in enumerate(locations, 1):
        if verbose:
            print(f'[{i}] {format_location(loc, verbose=True)}\n')
        else:
            print(format_location(loc, verbose=False))

    return 0


def main():
    """Main entry point for CLI locator."""
    parser = argparse.ArgumentParser(
        description='Locate variables and code across HDL representations',
        epilog="""
Environment Variables:
  HAGENT_REPO_DIR       Repository directory
  HAGENT_BUILD_DIR      Build output directory
  HAGENT_CACHE_DIR      Cache directory
  HAGENT_DOCKER         Docker image to use (if set, docker mode is enabled)

Examples:
  # Map VCD signal to Verilog
  %(prog)s --api locate_vcd --to verilog --name gcd "top.gcd.x"

  # Map Verilog variable to Chisel (cross-representation)
  %(prog)s --api map_variable --from verilog --to chisel --name gcd --module GCD "x"

  # Find variable in Chisel (single-representation)
  %(prog)s --api locate_variable --to chisel --name gcd --module GCD "x"

  # Map Verilog diff to Chisel (from stdin)
  cat changes.diff | %(prog)s --api locate_code --from verilog --to chisel --name gcd
        """,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    # Required arguments
    parser.add_argument(
        '--api',
        choices=['locate_vcd', 'map_variable', 'locate_variable', 'locate_code'],
        required=True,
        help='API mode: locate_vcd, map_variable, locate_variable, or locate_code',
    )

    # Profile name (required)
    parser.add_argument('--name', dest='profile_name', required=True, help='Profile name from hagent.yaml')

    # --to is always required
    parser.add_argument(
        '--to',
        dest='to_type',
        required=True,
        help='Target representation type (case-insensitive): verilog, chisel, netlist',
    )

    # --from is required for map_variable and locate_code
    parser.add_argument(
        '--from',
        dest='from_type',
        help='Source representation type (case-insensitive): vcd, verilog, chisel, netlist (required for map_variable and locate_code)',
    )

    # --module is required for map_variable, optional for locate_variable
    parser.add_argument(
        '--module',
        dest='module_name',
        help='Module/class name to constrain search (case-insensitive, required for map_variable, optional for locate_variable)',
    )

    # Optional arguments
    parser.add_argument('--config', dest='config_path', help='Path to hagent.yaml (auto-discovered if not specified)')

    parser.add_argument('-v', '--verbose', action='store_true', help='Show detailed output including confidence scores')

    parser.add_argument(
        '--debug',
        action='store_true',
        help='Show debug output from underlying commands (slang-hier, synth.py, etc.)',
    )

    parser.add_argument(
        '--invalidate-cache',
        action='store_true',
        help='Invalidate cache before running (forces rebuild)',
    )

    # Positional argument for variable name
    parser.add_argument(
        'variable',
        nargs='?',
        help='Variable name, regex pattern, or hierarchical VCD path (required for all APIs except locate_code)',
    )

    args = parser.parse_args()

    # Validate arguments based on API mode
    if args.api in ['locate_vcd', 'map_variable', 'locate_variable'] and not args.variable:
        parser.error(f'variable argument is required when --api {args.api} is used')

    if args.api == 'locate_code' and args.variable:
        parser.error('variable argument should not be provided when --api locate_code is used')

    if args.api in ['map_variable', 'locate_code'] and not args.from_type:
        parser.error(f'--from is required when --api {args.api} is used')

    if args.api == 'map_variable' and not args.module_name:
        parser.error('--module is required when --api map_variable is used')

    # Parse representation types
    try:
        to_rep = parse_representation(args.to_type)
        from_rep = parse_representation(args.from_type) if args.from_type else None
    except ValueError as e:
        print(f'Error: {e}', file=sys.stderr)
        return 1

    # Initialize Locator
    if args.verbose:
        print(f"Initializing Locator with profile '{args.profile_name}'...", file=sys.stderr)

    locator = Locator(config_path=args.config_path, profile_name=args.profile_name, debug=args.debug)

    if not locator.setup():
        print(f'Error: Locator setup failed: {locator.get_error()}', file=sys.stderr)
        return 1

    # Invalidate cache if requested
    if args.invalidate_cache:
        if args.verbose:
            print('Invalidating cache...', file=sys.stderr)
        locator.invalidate_cache(force=True)

    # Execute the requested operation
    exit_code = 1
    try:
        if args.api == 'locate_vcd':
            exit_code = run_locate_vcd(locator, args.variable, to_rep, args.verbose)
        elif args.api == 'map_variable':
            exit_code = run_map_variable(locator, args.variable, from_rep, to_rep, args.module_name, args.verbose)
        elif args.api == 'locate_variable':
            exit_code = run_locate_variable(locator, args.variable, to_rep, args.module_name, args.verbose)
        elif args.api == 'locate_code':
            # Read diff from stdin
            if args.verbose:
                print('Reading diff from stdin...', file=sys.stderr)

            diff_input = sys.stdin.read()
            if not diff_input.strip():
                print('Error: No diff input provided on stdin', file=sys.stderr)
                return 1

            exit_code = locate_code(locator, diff_input, from_rep, to_rep, args.verbose)
    finally:
        locator.cleanup()

    return exit_code


if __name__ == '__main__':
    sys.exit(main())
