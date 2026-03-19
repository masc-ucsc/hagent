#!/usr/bin/env python3
# See LICENSE for details
"""
Script to run label-path locator via LiveHD's lgshell.

Runs pass.label.path on a synthesized netlist and on original RTL source
(with hierarchical mode), then uses the locator script to cross-reference
instance signals back to source-level paths.

Usage:
    python scripts/label_path_locator.py \
        --lgshell <path> --livehd-locator <path> --liberty <path> \
        --netlist-top <name> --netlist-path <path> \
        --instance-names inst1 inst2 ... \
        --source-top <name> \
        [--standalone-files f1 f2 ...] [--manifest-file <path>] \
        [--output-dir <path>]
"""

import argparse
import subprocess
import sys
import threading
from pathlib import Path


def run_lgshell(lgshell_path: str, command: str, output_file: str, log_file: str, timeout: int = 36000) -> bool:
    """Run an lgshell command, log stdout/stderr to log_file, and write stdout to output_file."""
    print(f'Running: {lgshell_path} {command!r}', file=sys.stderr)

    try:
        process = subprocess.Popen(
            [lgshell_path, command],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
        )
    except FileNotFoundError:
        print(f'Error: lgshell not found at {lgshell_path}', file=sys.stderr)
        return False

    stdout_lines = []
    log_handle = open(log_file, 'a')

    def read_stderr():
        for line in process.stderr:
            log_handle.write(line)

    stderr_thread = threading.Thread(target=read_stderr)
    stderr_thread.start()

    for line in process.stdout:
        log_handle.write(line)
        stdout_lines.append(line)

    stderr_thread.join()
    log_handle.close()

    try:
        process.wait(timeout=timeout)
    except subprocess.TimeoutExpired:
        process.kill()
        print(f'Error: lgshell timed out after {timeout}s', file=sys.stderr)
        return False

    if process.returncode != 0:
        print(f'Warning: lgshell exited with code {process.returncode}', file=sys.stderr)

    with open(output_file, 'w') as f:
        f.writelines(stdout_lines)

    print(f'  Output written to {output_file}', file=sys.stderr)
    return True


def build_netlist_command(liberty_file: str, netlist_top: str, netlist_path: str, instance_names: list[str]) -> str:
    """Build lgshell command for pass.label.path on the synthesized netlist."""
    instances = ','.join(instance_names)
    liberty_cmd = f'inou.liberty files:{liberty_file}'
    parts = [
        f'inou.yosys.tolg top:{netlist_top} files:{netlist_path}',
        f'pass.label.path instance:{instances} verbose:true',
    ]
    return liberty_cmd + '\n' + ' |> '.join(parts)


def build_source_command(
    liberty_file: str,
    source_top: str,
    standalone_files: list[str] | None = None,
    manifest_file: str | None = None,
) -> str:
    """Build lgshell command for pass.label.path on original source with hier:true."""
    liberty_cmd = f'inou.liberty files:{liberty_file}'
    tolg_cmd = f'inou.yosys.tolg top:{source_top}'
    if standalone_files:
        tolg_cmd += f' files:{",".join(standalone_files)}'
    if manifest_file:
        tolg_cmd += f' filelist_file:{manifest_file}'

    parts = [
        tolg_cmd,
        'filter',
        f'lgraph.open name:{source_top}',
        'pass.label.path hier:true verbose:true',
    ]
    return liberty_cmd + '\n' + ' |> '.join(parts)


def run_locator(locator_path: str, netlist_label: str, source_label: str) -> str:
    """Run the locator script and return its stdout."""
    print(f'Running: {locator_path} {netlist_label} {source_label}', file=sys.stderr)

    try:
        result = subprocess.run(
            [locator_path, netlist_label, source_label],
            stdout=subprocess.PIPE,
            stderr=subprocess.PIPE,
            text=True,
            timeout=300,
        )
    except FileNotFoundError:
        print(f'Error: locator not found at {locator_path}', file=sys.stderr)
        return ''
    except subprocess.TimeoutExpired:
        print('Error: locator timed out', file=sys.stderr)
        return ''

    if result.returncode != 0:
        print(f'Warning: locator exited with code {result.returncode}', file=sys.stderr)
        if result.stderr:
            print(f'  stderr: {result.stderr[:500]}', file=sys.stderr)

    return result.stdout


def main():
    parser = argparse.ArgumentParser(description='Run label-path locator via LiveHD lgshell')
    parser.add_argument('--lgshell', required=True, help='Path to lgshell binary')
    parser.add_argument('--livehd-locator', required=True, help='Path to locator script')
    parser.add_argument('--liberty', required=True, help='Path to liberty file')
    parser.add_argument('--netlist-top', required=True, help='Top module name in the synthesized netlist')
    parser.add_argument('--netlist-path', required=True, help='Path to synthesized netlist file')
    parser.add_argument('--instance-names', nargs='+', required=True, help='Instance names in the netlist')
    parser.add_argument('--source-top', required=True, help='Top module name for original RTL source')
    parser.add_argument('--standalone-files', nargs='*', help='Original RTL source files')
    parser.add_argument('--manifest-file', help='RTL manifest/filelist file')
    parser.add_argument('--output-dir', default='.', help='Working directory for intermediate files')

    args = parser.parse_args()

    if not args.standalone_files and not args.manifest_file:
        parser.error('at least one of --standalone-files or --manifest-file is required')

    work_dir = Path(args.output_dir)
    work_dir.mkdir(parents=True, exist_ok=True)

    netlist_out = str(work_dir / 'netlist.label.path')
    source_out = str(work_dir / 'source.label.path')
    log_file = str(work_dir / 'log.txt')

    # Clear log file
    open(log_file, 'w').close()

    # Step 1: pass.label.path on synthesized netlist
    netlist_cmd = build_netlist_command(args.liberty, args.netlist_top, args.netlist_path, args.instance_names)
    if not run_lgshell(args.lgshell, netlist_cmd, netlist_out, log_file):
        sys.exit(1)

    # Step 2: pass.label.path on original source (hier:true)
    source_cmd = build_source_command(args.liberty, args.source_top, args.standalone_files, args.manifest_file)
    if not run_lgshell(args.lgshell, source_cmd, source_out, log_file):
        sys.exit(1)

    # Step 3: Run locator to cross-reference
    output = run_locator(args.locator, netlist_out, source_out)
    matched_files = str(work_dir / 'matched_files')
    with open(matched_files, 'w') as f:
        f.write(output)
    print(f'  Output written to {matched_files}', file=sys.stderr)
    print(output, end='')


if __name__ == '__main__':
    main()
