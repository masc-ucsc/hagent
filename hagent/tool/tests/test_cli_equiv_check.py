#!/usr/bin/env python3
"""
Test script for cli_equiv_check.py to verify it works correctly.
"""

import subprocess
import os
import pytest


def run_cli_command(args):
    """Run the CLI command and return (exit_code, stdout, stderr)"""
    cmd = ['uv', 'run', 'python', './hagent/tool/tests/cli_equiv_check.py'] + args
    # Set up environment for Docker mode
    env = os.environ.copy()
    env['HAGENT_EXECUTION_MODE'] = 'docker'
    # Set up output directories
    output_dir = os.path.abspath('./output/test_equiv_check')
    os.makedirs(output_dir, exist_ok=True)
    env['HAGENT_REPO_DIR'] = output_dir + '/repo'
    env['HAGENT_BUILD_DIR'] = output_dir + '/build'
    env['HAGENT_CACHE_DIR'] = output_dir + '/cache'
    # Create directories
    for dir_path in [env['HAGENT_REPO_DIR'], env['HAGENT_BUILD_DIR'], env['HAGENT_CACHE_DIR']]:
        os.makedirs(dir_path, exist_ok=True)

    # Debug information for CI
    print(f'DEBUG: Running command: {" ".join(cmd)}')
    print(f'DEBUG: Working directory: {os.getcwd()}')
    print('DEBUG: Environment variables:')
    for key in ['HAGENT_EXECUTION_MODE', 'HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR']:
        print(f'  {key}={env.get(key, "NOT_SET")}')
    print('DEBUG: Output directory setup:')
    for dir_path in [env['HAGENT_REPO_DIR'], env['HAGENT_BUILD_DIR'], env['HAGENT_CACHE_DIR']]:
        exists = os.path.exists(dir_path)
        perms = oct(os.stat(dir_path).st_mode)[-3:] if exists else 'N/A'
        print(f'  {dir_path}: exists={exists}, perms={perms}')

    # Check if CLI script exists
    cli_script = './hagent/tool/tests/cli_equiv_check.py'
    cli_exists = os.path.exists(cli_script)
    cli_perms = oct(os.stat(cli_script).st_mode)[-3:] if cli_exists else 'N/A'
    print(f'DEBUG: CLI script: {cli_script} exists={cli_exists}, perms={cli_perms}')

    # Check test files exist
    test_files = [
        './hagent/tool/tests/test_files/gold1.v',
        './hagent/tool/tests/test_files/gold2.v',
        './hagent/tool/tests/test_files/test1.v',
    ]
    for test_file in test_files:
        file_exists = os.path.exists(test_file)
        file_perms = oct(os.stat(test_file).st_mode)[-3:] if file_exists else 'N/A'
        print(f'DEBUG: Test file: {test_file} exists={file_exists}, perms={file_perms}')

    # Check if Docker is available
    try:
        docker_check = subprocess.run(['docker', '--version'], capture_output=True, text=True, timeout=10)
        print(f'DEBUG: Docker version check: exit_code={docker_check.returncode}')
        if docker_check.returncode == 0:
            print(f'DEBUG: Docker version: {docker_check.stdout.strip()}')
        else:
            print(f'DEBUG: Docker version error: {docker_check.stderr.strip()}')
    except Exception as e:
        print(f'DEBUG: Docker check failed: {e}')

    # Check uv command
    try:
        uv_check = subprocess.run(['uv', '--version'], capture_output=True, text=True, timeout=10)
        print(f'DEBUG: UV version check: exit_code={uv_check.returncode}')
        if uv_check.returncode == 0:
            print(f'DEBUG: UV version: {uv_check.stdout.strip()}')
        else:
            print(f'DEBUG: UV version error: {uv_check.stderr.strip()}')
    except Exception as e:
        print(f'DEBUG: UV check failed: {e}')

    result = subprocess.run(cmd, capture_output=True, text=True, cwd=os.getcwd(), env=env, timeout=120)

    # Debug output
    print(f'DEBUG: Command exit code: {result.returncode}')
    print(f'DEBUG: Command stdout length: {len(result.stdout)}')
    print(f'DEBUG: Command stderr length: {len(result.stderr)}')
    if result.stdout:
        print(f'DEBUG: Command stdout (first 500 chars): {result.stdout[:500]}')
    if result.stderr:
        print(f'DEBUG: Command stderr (first 500 chars): {result.stderr[:500]}')

    return result.returncode, result.stdout, result.stderr


def test_cli_equivalent_designs():
    """Test CLI with equivalent designs"""
    exit_code, stdout, stderr = run_cli_command(
        [
            '-r',
            './hagent/tool/tests/test_files/gold1.v',
            '-r',
            './hagent/tool/tests/test_files/gold2.v',
            '-i',
            './hagent/tool/tests/test_files/test1.v',
        ]
    )

    # Enhanced debugging for assertion failures
    if exit_code != 0:
        print(f'ERROR: Expected exit_code=0, got exit_code={exit_code}')
        print(f'ERROR: stdout={stdout}')
        print(f'ERROR: stderr={stderr}')

    if 'SUCCESS: All modules are equivalent!' not in stdout:
        print('ERROR: Expected success message not found in stdout')
        print(f'ERROR: Actual stdout={stdout}')

    if 'Checking equivalence: adder ↔ add_impl' not in stdout:
        print('ERROR: Expected adder check message not found in stdout')
        print(f'ERROR: Actual stdout={stdout}')

    if 'Checking equivalence: multiplier ↔ mult_impl' not in stdout:
        print('ERROR: Expected multiplier check message not found in stdout')
        print(f'ERROR: Actual stdout={stdout}')

    assert exit_code == 0, f'Command failed with exit_code={exit_code}, stderr={stderr}'
    assert 'SUCCESS: All modules are equivalent!' in stdout, f'Success message not found. stdout={stdout}'
    assert 'Checking equivalence: adder ↔ add_impl' in stdout, f'Adder check not found. stdout={stdout}'
    assert 'Checking equivalence: multiplier ↔ mult_impl' in stdout, f'Multiplier check not found. stdout={stdout}'


def test_cli_non_equivalent_designs():
    """Test CLI with non-equivalent designs"""
    exit_code, stdout, stderr = run_cli_command(
        [
            '-r',
            './hagent/tool/tests/test_files/gold1.v',
            '-r',
            './hagent/tool/tests/test_files/gold2.v',
            '-i',
            './hagent/tool/tests/test_files/bad_impl.v',
        ]
    )

    # Enhanced debugging for assertion failures
    if exit_code != 1:
        print(f'ERROR: Expected exit_code=1, got exit_code={exit_code}')
        print(f'ERROR: stdout={stdout}')
        print(f'ERROR: stderr={stderr}')

    assert exit_code == 1, f'Expected failure exit_code=1, got {exit_code}. stderr={stderr}'
    assert 'FAILURE: Designs are NOT equivalent!' in stdout, f'Failure message not found. stdout={stdout}'
    assert 'Counterexample:' in stdout, f'Counterexample not found. stdout={stdout}'
    assert 'Module pair adder↔add_impl:' in stdout, f'Module pair info not found. stdout={stdout}'


def test_cli_specific_top_module():
    """Test CLI with specific top module"""
    exit_code, stdout, stderr = run_cli_command(
        [
            '-r',
            './hagent/tool/tests/test_files/gold1.v',
            '-r',
            './hagent/tool/tests/test_files/gold2.v',
            '-i',
            './hagent/tool/tests/test_files/test1.v',
            '--top',
            'adder',
        ]
    )

    # Enhanced debugging for assertion failures
    if exit_code != 0:
        print(f'ERROR: Expected exit_code=0, got exit_code={exit_code}')
        print(f'ERROR: stdout={stdout}')
        print(f'ERROR: stderr={stderr}')

    assert exit_code == 0, f'Command failed with exit_code={exit_code}, stderr={stderr}'
    assert 'SUCCESS: All modules are equivalent!' in stdout, f'Success message not found. stdout={stdout}'
    assert 'Checking equivalence: adder ↔ add_impl' in stdout, f'Adder check not found. stdout={stdout}'
    # Should NOT check multiplier when --top adder is specified
    assert (
        'Checking equivalence: multiplier ↔ mult_impl' not in stdout
    ), f'Multiplier should not be checked with --top adder. stdout={stdout}'


def test_cli_missing_file():
    """Test CLI error handling for missing files"""
    exit_code, stdout, stderr = run_cli_command(['-r', 'nonexistent.v', '-i', './hagent/tool/tests/test_files/test1.v'])

    assert exit_code == 1  # Error
    assert 'The following files do not exist:' in stderr
    assert 'nonexistent.v' in stderr


def test_cli_help():
    """Test CLI help output"""
    exit_code, stdout, stderr = run_cli_command(['--help'])

    assert exit_code == 0  # Success
    assert 'Equivalence checking tool for multiple Verilog files' in stdout
    assert '--reference' in stdout
    assert '--implementation' in stdout


if __name__ == '__main__':
    pytest.main(['-v', __file__])
