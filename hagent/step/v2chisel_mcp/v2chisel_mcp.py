#!/usr/bin/env python3
"""
V2chisel_mcp - MCP-based Verilog to Chisel conversion using shell commands
"""

import argparse
import os
import subprocess
import sys
from datetime import datetime
from pathlib import Path

import yaml

# Add parent path for imports
sys.path.insert(0, str(Path(__file__).resolve().parent.parent.parent))

from hagent.tool.chisel_diff_applier import ChiselDiffApplier

# Get HAGENT_ROOT from this script's location
HAGENT_ROOT = Path(__file__).resolve().parent.parent.parent.parent


def main():
    # Parse arguments
    parser = argparse.ArgumentParser(description='V2chisel MCP - Verilog to Chisel conversion')
    parser.add_argument('-i', '--input', required=True, help='Input YAML file containing verilog_diff')
    parser.add_argument('--cpu', default='singlecyclecpu_nd', help='CPU profile name')
    parser.add_argument(
        '--llm', default='openai/gpt-4o', help='LLM model to use (e.g., "openai/gpt-4o", "anthropic/claude-sonnet-4-5-20250929")'
    )
    args = parser.parse_args()

    # Step 1: Read the input YAML file
    input_file = Path(args.input).resolve()
    print(f'Reading input file: {input_file}')

    with open(input_file, 'r') as f:
        input_data = yaml.safe_load(f)

    # Extract verilog_diff from the input
    bugs = input_data.get('bugs', [])
    if not bugs:
        print('ERROR: No bugs found in input file')
        return 1

    verilog_diff = bugs[0].get('unified_diff', '')
    bug_file = bugs[0].get('file', 'unknown')

    print(f'Bug file: {bug_file}')
    print(f'Verilog diff:\n{verilog_diff}')

    # Step 2: Create a directory in tmp named based on date/time
    timestamp = datetime.now().strftime('%Y%m%d_%H%M%S')
    work_dir = Path.home() / 'hagent' / 'tmp' / f'v2chisel_{timestamp}'
    work_dir.mkdir(parents=True, exist_ok=True)
    print(f'\nCreated work directory: {work_dir}')

    # Step 3: Run setup_mcp.sh simplechisel <work_dir>
    cmd = f'{HAGENT_ROOT}/scripts/setup_mcp.sh simplechisel {work_dir}'
    print(f'Running: {cmd}')

    result = subprocess.run(cmd, shell=True, capture_output=True, text=True)

    print('STDOUT:', result.stdout)
    print('STDERR:', result.stderr)
    print('Return code:', result.returncode)

    if result.returncode != 0:
        print('ERROR: setup_mcp.sh failed')
        return 1

    # Step 4: Read and set environment variables from hagent_server.sh
    server_script = work_dir / 'hagent_server.sh'
    print(f'\nReading environment variables from: {server_script}')

    with open(server_script, 'r') as f:
        for line in f:
            line = line.strip()
            if line.startswith('export '):
                var_part = line[7:]  # Remove 'export '
                if '=' in var_part:
                    key, value = var_part.split('=', 1)
                    value = value.strip('"\'')
                    os.environ[key] = value
                    print(f'  {key}={value}')

    print('\nEnvironment variables set successfully')

    # Step 5: Compile baseline Chisel to get fresh Verilog
    print(f'\n{"=" * 60}')
    print('Step 5: Compile baseline Chisel to Verilog')
    print(f'{"=" * 60}')

    cmd = f'uv run --python 3.13 python {HAGENT_ROOT}/hagent/mcp/mcp_build.py --name {args.cpu} --api compile'
    print(f'Running: {cmd}')

    result = subprocess.run(cmd, shell=True, cwd=str(work_dir), capture_output=True, text=True, env=os.environ)

    print('STDOUT:', result.stdout[:500] if len(result.stdout) > 500 else result.stdout)
    print('Return code:', result.returncode)

    if result.returncode != 0:
        print('ERROR: Compile failed')
        print('STDERR:', result.stderr)
        return 1

    print('Compile completed successfully')

    # Step 6: Apply verilog_diff to the compiled Verilog
    print(f'\n{"=" * 60}')
    print('Step 6: Apply verilog_diff to compiled Verilog')
    print(f'{"=" * 60}')

    # Find the target Verilog file
    build_dir = work_dir / 'build' / f'build_{args.cpu}'
    target_file = build_dir / bug_file

    if not target_file.exists():
        print(f'ERROR: Target file not found: {target_file}')
        return 1

    print(f'Target file: {target_file}')

    # Read the original Verilog file
    original_code = target_file.read_text()
    print(f'Original file size: {len(original_code)} chars')

    # Apply the diff using ChiselDiffApplier (works for Verilog too)
    applier = ChiselDiffApplier()
    modified_code = applier.apply_diff(verilog_diff, original_code)

    if applier.error_message:
        print(f'WARNING: {applier.error_message}')

    # Check if the code was actually modified
    if modified_code == original_code:
        print('ERROR: verilog_diff was not applied - no changes detected')
        return 1

    # Write the modified code back
    target_file.write_text(modified_code)
    print(f'Modified file size: {len(modified_code)} chars')
    print('Applying verilog_diff is done without errors')

    # Step 7: Run elab with tag=gold to create gold design
    print(f'\n{"=" * 60}')
    print('Step 7: Create gold design (elab with tag=gold)')
    print(f'{"=" * 60}')

    cmd = f'uv run --python 3.13 python {HAGENT_ROOT}/hagent/mcp/mcp_build.py --name {args.cpu} --api elab -o tag=gold'
    print(f'Running: {cmd}')

    result = subprocess.run(cmd, shell=True, cwd=str(work_dir), capture_output=True, text=True, env=os.environ)

    print('STDOUT:', result.stdout)
    print('Return code:', result.returncode)

    if result.returncode != 0:
        print('ERROR: Elab failed')
        print('STDERR:', result.stderr)
        return 1

    print('Gold design created successfully')

    # Step 8: Run v2chisel_batch to generate chisel_diff using the LLM
    print(f'\n{"=" * 60}')
    print('Step 8: Generate chisel_diff using v2chisel_batch')
    print(f'{"=" * 60}')

    batch_output_dir = work_dir / 'v2chisel_output'
    batch_output_dir.mkdir(parents=True, exist_ok=True)

    cmd = (
        f'uv run --python 3.13 python {HAGENT_ROOT}/hagent/step/v2chisel_batch/v2chisel_batch.py'
        f' {input_file}'
        f' -o {batch_output_dir}'
        f' --cpu {args.cpu}'
        f' --llm {args.llm}'
        f' --chisel-diff-only'
    )
    print(f'Running: {cmd}')

    result = subprocess.run(cmd, shell=True, cwd=str(work_dir), capture_output=True, text=True, env=os.environ)

    print('STDOUT:', result.stdout[-2000:] if len(result.stdout) > 2000 else result.stdout)
    print('Return code:', result.returncode)

    if result.returncode != 0:
        print('ERROR: v2chisel_batch failed')
        print('STDERR:', result.stderr[-2000:] if len(result.stderr) > 2000 else result.stderr)
        return 1

    print('chisel_diff generation completed successfully')

    # Read the output to get the chisel_diff
    output_yaml = batch_output_dir / 'output.yaml'
    if not output_yaml.exists():
        print(f'ERROR: Output file not found: {output_yaml}')
        return 1

    with open(output_yaml, 'r') as f:
        batch_result = yaml.safe_load(f)

    bug_results = batch_result.get('bug_results', [])
    if not bug_results:
        print('ERROR: No bug results in output')
        return 1

    chisel_diff = bug_results[0].get('chisel_diff', '')
    if not chisel_diff:
        print('ERROR: No chisel_diff generated')
        return 1

    print(f'Generated chisel_diff ({len(chisel_diff)} chars):')
    print(chisel_diff[:500] if len(chisel_diff) > 500 else chisel_diff)

    # Steps 9-10: Apply chisel_diff to Chisel source, compile, retry loop
    MAX_COMPILE_RETRIES = 3
    compile_success = False
    chisel_backup = ''

    for retry in range(MAX_COMPILE_RETRIES):
        # Step 9: Apply chisel_diff to Chisel source files
        print(f'\n{"=" * 60}')
        print(f'Step 9: Apply chisel_diff to Chisel source (attempt {retry + 1}/{MAX_COMPILE_RETRIES})')
        print(f'{"=" * 60}')

        # Parse file path from diff header (--- a/path/to/file.scala)
        chisel_target_file = _parse_diff_target_file(chisel_diff)
        if not chisel_target_file:
            print('ERROR: Could not parse target file from chisel_diff header')
            return 1

        chisel_file_path = work_dir / 'repo' / chisel_target_file
        if not chisel_file_path.exists():
            print(f'ERROR: Chisel source file not found: {chisel_file_path}')
            return 1

        print(f'Target Chisel file: {chisel_file_path}')

        # On first attempt, save a backup of the original Chisel source
        if retry == 0:
            chisel_backup = chisel_file_path.read_text()

        # Restore original Chisel source before applying new diff
        chisel_file_path.write_text(chisel_backup)
        chisel_original = chisel_backup

        # Apply the chisel_diff
        applier = ChiselDiffApplier()
        modified_chisel = applier.apply_diff(chisel_diff, chisel_original)

        if applier.error_message:
            print(f'WARNING: {applier.error_message}')

        if modified_chisel == chisel_original:
            print('ERROR: chisel_diff was not applied - no changes detected')
            return 1

        chisel_file_path.write_text(modified_chisel)
        print(f'Applied chisel_diff successfully ({len(modified_chisel)} chars)')

        # Step 10: Compile the modified Chisel
        print(f'\n{"=" * 60}')
        print(f'Step 10: Compile modified Chisel (attempt {retry + 1}/{MAX_COMPILE_RETRIES})')
        print(f'{"=" * 60}')

        cmd = f'uv run --python 3.13 python {HAGENT_ROOT}/hagent/mcp/mcp_build.py --name {args.cpu} --api compile'
        print(f'Running: {cmd}')

        result = subprocess.run(cmd, shell=True, cwd=str(work_dir), capture_output=True, text=True, env=os.environ)

        print('STDOUT:', result.stdout[-1000:] if len(result.stdout) > 1000 else result.stdout)
        print('Return code:', result.returncode)

        if result.returncode == 0:
            print('Compile passed!')
            compile_success = True
            break

        # Compile failed - prepare for retry
        compile_error_msg = result.stderr[-2000:] if len(result.stderr) > 2000 else result.stderr
        if not compile_error_msg:
            compile_error_msg = result.stdout[-2000:] if len(result.stdout) > 2000 else result.stdout
        print(f'Compile FAILED (attempt {retry + 1}/{MAX_COMPILE_RETRIES})')
        print(f'Error: {compile_error_msg[:500]}')

        if retry + 1 >= MAX_COMPILE_RETRIES:
            print('ERROR: All compile retries exhausted')
            return 1

        # Save the failed diff to a temp file for retry
        prev_diff_file = work_dir / f'prev_chisel_diff_{retry}.txt'
        prev_diff_file.write_text(chisel_diff)

        # Re-run v2chisel_batch with compile error context
        print(f'\n{"=" * 60}')
        print('Step 8 (retry): Re-generate chisel_diff with compile error context')
        print(f'{"=" * 60}')

        cmd = (
            f'uv run --python 3.13 python {HAGENT_ROOT}/hagent/step/v2chisel_batch/v2chisel_batch.py'
            f' {input_file}'
            f' -o {batch_output_dir}'
            f' --cpu {args.cpu}'
            f' --llm {args.llm}'
            f' --chisel-diff-only'
            f' --compile-error {_shell_quote(compile_error_msg)}'
            f' --previous-diff-file {prev_diff_file}'
        )
        print(f'Running: {cmd}')

        result = subprocess.run(cmd, shell=True, cwd=str(work_dir), capture_output=True, text=True, env=os.environ)

        print('STDOUT:', result.stdout[-2000:] if len(result.stdout) > 2000 else result.stdout)
        print('Return code:', result.returncode)

        if result.returncode != 0:
            print('ERROR: v2chisel_batch retry failed')
            print('STDERR:', result.stderr[-1000:] if len(result.stderr) > 1000 else result.stderr)
            return 1

        # Read the new chisel_diff from output
        with open(output_yaml, 'r') as f:
            batch_result = yaml.safe_load(f)

        bug_results = batch_result.get('bug_results', [])
        if not bug_results:
            print('ERROR: No bug results in retry output')
            return 1

        chisel_diff = bug_results[0].get('chisel_diff', '')
        if not chisel_diff:
            print('ERROR: No chisel_diff generated in retry')
            return 1

        print(f'New chisel_diff generated ({len(chisel_diff)} chars)')

    if not compile_success:
        print('ERROR: Failed to compile after all retries')
        return 1

    # Step 11: Run elab with tag=gate to generate gate-level Verilog
    print(f'\n{"=" * 60}')
    print('Step 11: Generate gate design (elab with tag=gate)')
    print(f'{"=" * 60}')

    cmd = f'uv run --python 3.13 python {HAGENT_ROOT}/hagent/mcp/mcp_build.py --name {args.cpu} --api elab -o tag=gate'
    print(f'Running: {cmd}')

    result = subprocess.run(cmd, shell=True, cwd=str(work_dir), capture_output=True, text=True, env=os.environ)

    print('STDOUT:', result.stdout)
    print('Return code:', result.returncode)

    if result.returncode != 0:
        print('ERROR: Elab gate failed')
        print('STDERR:', result.stderr)
        return 1

    print('Gate design created successfully')

    # Step 12: Run LEC to verify gold vs gate
    print(f'\n{"=" * 60}')
    print('Step 12: Run LEC (gold vs gate)')
    print(f'{"=" * 60}')

    lec_dir = work_dir / 'build' / f'build_{args.cpu}'
    cmd = (
        f'uv run --python 3.13 python {HAGENT_ROOT}/hagent/tool/tests/cli_equiv_check.py'
        f' --dir {lec_dir}'
        f' --ref-tag gold'
        f' --impl-tag gate'
    )
    print(f'Running: {cmd}')

    result = subprocess.run(cmd, shell=True, cwd=str(work_dir), capture_output=True, text=True, env=os.environ)

    print('STDOUT:', result.stdout)
    print('Return code:', result.returncode)

    if result.returncode != 0:
        print('ERROR: LEC failed')
        print('STDERR:', result.stderr)
        return 1

    print('LEC passed!')
    print(f'\nPipeline complete! Work directory: {work_dir}')
    return 0


def _parse_diff_target_file(diff_text):
    """Parse the target file path from a unified diff header.

    Looks for '--- a/path/to/file' or '+++ b/path/to/file' patterns.
    Returns the file path relative to repo root, or None if not found.
    """
    import re

    for line in diff_text.split('\n'):
        # Match --- a/path or +++ b/path (the 'b/' side is the modified file)
        m = re.match(r'^---\s+a/(.+)', line)
        if m:
            return m.group(1).strip()
        m = re.match(r'^---\s+(.+)', line)
        if m:
            path = m.group(1).strip()
            if path != '/dev/null':
                return path
    return None


def _shell_quote(text):
    """Quote a string for safe shell usage."""
    import shlex

    return shlex.quote(text)


if __name__ == '__main__':
    sys.exit(main() or 0)
