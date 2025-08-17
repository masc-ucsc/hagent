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

    result = subprocess.run(cmd, capture_output=True, text=True, cwd=os.getcwd(), env=env)
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

    assert exit_code == 0  # Success
    assert 'SUCCESS: All modules are equivalent!' in stdout
    assert 'Checking equivalence: adder ↔ add_impl' in stdout
    assert 'Checking equivalence: multiplier ↔ mult_impl' in stdout


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

    assert exit_code == 1  # Failure
    assert 'FAILURE: Designs are NOT equivalent!' in stdout
    assert 'Counterexample:' in stdout
    assert 'Module pair adder↔add_impl:' in stdout


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

    assert exit_code == 0  # Success
    assert 'SUCCESS: All modules are equivalent!' in stdout
    assert 'Checking equivalence: adder ↔ add_impl' in stdout
    # Should NOT check multiplier when --top adder is specified
    assert 'Checking equivalence: multiplier ↔ mult_impl' not in stdout


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
