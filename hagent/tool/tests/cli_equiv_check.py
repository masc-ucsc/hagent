#!/bin/sh
# fmt: off
# ruff: noqa: E402
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

    exec uv run python "$0" "$@"
else
    # Local: use uv run to manage environment (handles sync automatically)
    exec uv run --project "$PROJECT_ROOT" python "$0" "$@"
fi
'''
# fmt: on
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

import yaml


def ensure_hagent_env():
    """
    Ensure HAGENT_CACHE_DIR is set up and default Docker image is selected when not provided.
    Users don't need to set HAGENT_DOCKER manually for this CLI.
    """
    # Default Docker image for Yosys if not provided by user
    os.environ.setdefault('HAGENT_DOCKER', 'mascucsc/hagent-simplechisel:2026.02')

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


def load_manifest(manifest_path):
    """Load manifest YAML, return None if doesn't exist."""
    if not manifest_path.exists():
        return None
    try:
        with open(manifest_path) as f:
            return yaml.safe_load(f)
    except Exception as e:
        print(f'Warning: Failed to load manifest {manifest_path}: {e}', file=sys.stderr)
        return None


def resolve_tag(tag_name, base_dir=None, use_synth=False, debug=False):
    """Resolve tag to actual file path and manifest.

    Args:
        tag_name: Tag name to resolve
        base_dir: Optional base directory to search first
        use_synth: Prefer synth.v over elab.v
        debug: Print debug information

    Returns:
        tuple: (file_path, manifest_dict or None)

    Raises:
        FileNotFoundError: If tag not found in search paths
    """
    search_paths = []

    # Build search path list
    if base_dir:
        search_paths.append(Path(base_dir) / tag_name)

    # HAGENT_CACHE_DIR has priority for tags
    cache_dir = os.environ.get('HAGENT_CACHE_DIR')
    if cache_dir:
        search_paths.append(Path(cache_dir) / tag_name)

    build_dir = os.environ.get('HAGENT_BUILD_DIR')
    if build_dir:
        search_paths.append(Path(build_dir) / tag_name)

    search_paths.extend(
        [
            Path('./build') / tag_name,
            Path('../build') / tag_name,
        ]
    )

    if debug:
        print(f'Resolving tag "{tag_name}" in search paths:', file=sys.stderr)
        for p in search_paths:
            print(f'  {p}', file=sys.stderr)

    # Find first existing tag directory
    for path in search_paths:
        if not path.exists():
            continue

        # Choose elab.v vs synth.v
        elab_file = path / 'elab.v'
        synth_file = path / 'synth.v'

        chosen_file = None
        if use_synth and synth_file.exists():
            chosen_file = synth_file
        elif elab_file.exists():
            chosen_file = elab_file
        elif synth_file.exists():
            chosen_file = synth_file

        if chosen_file:
            manifest = load_manifest(path / 'manifest.yaml')
            if debug:
                print(f'✓ Resolved tag "{tag_name}" to {chosen_file}', file=sys.stderr)
                if manifest:
                    print(f'  Top module: {manifest.get("top_module", "unknown")}', file=sys.stderr)
            return chosen_file, manifest

    raise FileNotFoundError(f'Tag "{tag_name}" not found in: {", ".join(str(p) for p in search_paths)}')


def resolve_file_or_dir(path_str, use_synth=False, debug=False):
    """Resolve a file path or directory to actual Verilog file.

    Args:
        path_str: File path or directory path
        use_synth: Prefer synth.v over elab.v for directories
        debug: Print debug information

    Returns:
        tuple: (file_path, manifest_dict or None)
    """
    path = Path(path_str)

    if not path.exists():
        raise FileNotFoundError(f'Path not found: {path}')

    # If it's a file, return it directly
    if path.is_file():
        # Try to find manifest in same directory
        manifest = load_manifest(path.parent / 'manifest.yaml')
        return path, manifest

    # If it's a directory, auto-detect elab.v or synth.v
    if path.is_dir():
        elab_file = path / 'elab.v'
        synth_file = path / 'synth.v'

        chosen_file = None
        if use_synth and synth_file.exists():
            chosen_file = synth_file
        elif elab_file.exists():
            chosen_file = elab_file
        elif synth_file.exists():
            chosen_file = synth_file

        if chosen_file:
            manifest = load_manifest(path / 'manifest.yaml')
            if debug:
                print(f'Auto-detected {chosen_file.name} in directory {path}', file=sys.stderr)
            return chosen_file, manifest

        raise FileNotFoundError(f'No elab.v or synth.v found in directory: {path}')

    raise ValueError(f'Path is neither file nor directory: {path}')


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
  # Direct files
  %(prog)s -r gold1.v -r gold2.v -i test1.v
  %(prog)s --reference ref.v --implementation impl.v
  %(prog)s -r ref/*.v -i impl/*.v

  # Tagged versions
  %(prog)s --ref-tag baseline --impl-tag current --dir build/
  %(prog)s --ref-tag baseline --implementation new_alu.v --dir build/
        """,
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )

    # Tag-based arguments
    parser.add_argument(
        '--ref-tag',
        help='Reference tag name (searches in --dir, HAGENT_CACHE_DIR, HAGENT_BUILD_DIR, ./build/)',
    )

    parser.add_argument(
        '--impl-tag',
        help='Implementation tag name (searches in --dir, HAGENT_CACHE_DIR, HAGENT_BUILD_DIR, ./build/)',
    )

    parser.add_argument(
        '--dir',
        help='Base directory for tag resolution (optional, auto-detects if not specified)',
    )

    parser.add_argument(
        '--use-synth',
        action='store_true',
        help='Prefer synth.v over elab.v when resolving tags or directories',
    )

    # Direct file arguments (backward compatible)
    parser.add_argument(
        '-r',
        '--reference',
        action='append',
        dest='gold_files',
        help='Gold/reference Verilog file(s) or directories. Can be specified multiple times. Supports wildcards.',
    )

    parser.add_argument(
        '-i',
        '--implementation',
        action='append',
        dest='gate_files',
        help='Gate/implementation Verilog file(s) or directories. Can be specified multiple times. Supports wildcards.',
    )

    parser.add_argument('--top', help='Specify a particular top module name to check (optional)')

    parser.add_argument('--debug', action='store_true', help='Enable debug output')

    args = parser.parse_args()

    try:
        # Resolve reference (gold) files/tags
        gold_files = []
        gold_manifests = []

        if args.ref_tag:
            # Resolve tag to file
            ref_file, ref_manifest = resolve_tag(args.ref_tag, args.dir, args.use_synth, args.debug)
            gold_files.append(str(ref_file))
            gold_manifests.append(ref_manifest)
        elif args.gold_files:
            # Expand and resolve file patterns or directories
            expanded = expand_file_patterns(args.gold_files)
            for file_path in expanded:
                resolved_file, manifest = resolve_file_or_dir(file_path, args.use_synth, args.debug)
                gold_files.append(str(resolved_file))
                gold_manifests.append(manifest)
        else:
            print('ERROR: Either --ref-tag or --reference is required', file=sys.stderr)
            sys.exit(1)

        # Resolve implementation (gate) files/tags
        gate_files = []
        gate_manifests = []

        if args.impl_tag:
            # Resolve tag to file
            impl_file, impl_manifest = resolve_tag(args.impl_tag, args.dir, args.use_synth, args.debug)
            gate_files.append(str(impl_file))
            gate_manifests.append(impl_manifest)
        elif args.gate_files:
            # Expand and resolve file patterns or directories
            expanded = expand_file_patterns(args.gate_files)
            for file_path in expanded:
                resolved_file, manifest = resolve_file_or_dir(file_path, args.use_synth, args.debug)
                gate_files.append(str(resolved_file))
                gate_manifests.append(manifest)
        else:
            print('ERROR: Either --impl-tag or --implementation is required', file=sys.stderr)
            sys.exit(1)

        if args.debug:
            print(f'Gold/Reference files: {gold_files}', file=sys.stderr)
            print(f'Gate/Implementation files: {gate_files}', file=sys.stderr)

        # Read and combine Verilog files
        print('Reading gold/reference files...')
        gold_code = read_verilog_files(gold_files)

        print('Reading gate/implementation files...')
        gate_code = read_verilog_files(gate_files)

        if args.debug:
            print(f'Combined gold code: {len(gold_code)} characters', file=sys.stderr)
            print(f'Combined gate code: {len(gate_code)} characters', file=sys.stderr)

        # Validate top modules if manifests are available
        ref_top = None
        impl_top = None

        if gold_manifests and gold_manifests[0]:
            ref_top = gold_manifests[0].get('top_module')

        if gate_manifests and gate_manifests[0]:
            impl_top = gate_manifests[0].get('top_module')

        if ref_top and impl_top and ref_top != impl_top:
            print('Warning: Comparing different top modules:', file=sys.stderr)
            print(f'  Reference:     {ref_top}', file=sys.stderr)
            print(f'  Implementation: {impl_top}', file=sys.stderr)
            print('This comparison may not be meaningful.', file=sys.stderr)
            print('', file=sys.stderr)

        # Setup equivalence checker
        print('Setting up equivalence checker...')
        checker = Equiv_check()

        setup_ok = checker.setup()
        if not setup_ok:
            print(f'ERROR: Equivalence checker setup failed: {checker.get_error()}', file=sys.stderr)
            sys.exit(1)

        if args.debug:
            docker_status = 'via Docker' if checker.use_docker else 'locally'
            print(f'✓ Yosys setup successful ({docker_status})', file=sys.stderr)

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
