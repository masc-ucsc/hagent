#!/usr/bin/env python3
"""
CLI Tests for Trivial Step

Tests various execution modes and environment variable combinations
for the trivial step to ensure proper Docker and local execution.
"""

import os
import subprocess
import pytest
from pathlib import Path

DEFAULT_HAGENT_DOCKER = 'mascucsc/hagent-builder:2025.09'


class TestTrivialCLI:
    """Test trivial step CLI with different execution modes."""

    @pytest.fixture
    def input_file(self):
        """Use the existing input1.yaml file for testing."""
        input_path = Path(__file__).parent / 'input1.yaml'
        return str(input_path)

    @pytest.fixture
    def output_file(self, request):
        """Create output file in organized test directory."""
        # Get the project root (4 levels up from test file)
        project_root = Path(__file__).parent.parent.parent.parent.parent
        output_dir = project_root / 'output' / 'test_cli_trivial'

        # Create output directory if it doesn't exist
        output_dir.mkdir(parents=True, exist_ok=True)

        # Create output file with test name for easy identification
        test_name = request.node.name
        output_file = output_dir / f'{test_name}.yaml'

        yield str(output_file)

        # Keep the file for debugging - don't delete it

    def test_local_execution_with_all_env_vars(self, input_file, output_file):
        """Test local execution with all required environment variables."""
        env = os.environ.copy()
        # Get paths relative to the project root (4 levels up from this test file)
        project_root = Path(__file__).parent.parent.parent.parent.parent
        env.update(
            {
                'HAGENT_REPO_DIR': str((project_root / 'output/local/repo').resolve()),
                'HAGENT_BUILD_DIR': str((project_root / 'output/local/build').resolve()),
                'HAGENT_CACHE_DIR': str((project_root / 'output/local/cache').resolve()),
            }
        )

        # Ensure directories exist
        for dir_path in [env['HAGENT_REPO_DIR'], env['HAGENT_BUILD_DIR'], env['HAGENT_CACHE_DIR']]:
            os.makedirs(dir_path, exist_ok=True)

        # Get the trivial.py path relative to the current working directory
        trivial_script = Path(__file__).parent.parent / 'trivial.py'

        result = subprocess.run(
            ['uv', 'run', 'python', str(trivial_script), input_file, '-o', output_file], env=env, capture_output=True, text=True
        )

        assert result.returncode == 0, f'Local execution failed: {result.stderr}'
        assert os.path.exists(output_file), 'Output file was not created'

        # Check that output contains expected fields
        with open(output_file, 'r') as f:
            content = f.read()
            assert 'added_field_trivial: sample' in content
            assert "uname_ret: '0'" in content
            assert "pwd_ret: '0'" in content
            # yosys_path_ret can be '0' or '1' depending on whether yosys is locally installed
            assert 'yosys_path_ret:' in content  # Just check that the field exists
            # Check that original input data is preserved
            assert 'POTATO: foo' in content
            assert 'FOOO_VAR: another_value' in content

    @pytest.mark.slow
    def test_docker_execution_no_env_vars(self, input_file, output_file):
        """Test Docker execution with only execution mode (no directory mounts)."""
        env = os.environ.copy()
        env['HAGENT_DOCKER'] = 'test-image:latest'
        env['HAGENT_DOCKER'] = DEFAULT_HAGENT_DOCKER

        # Remove any existing HAGENT directory env vars to test defaults
        for key in ['HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR']:
            env.pop(key, None)

        # Get the trivial.py path relative to the current working directory
        trivial_script = Path(__file__).parent.parent / 'trivial.py'

        result = subprocess.run(
            ['uv', 'run', 'python', str(trivial_script), input_file, '-o', output_file],
            env=env,
            capture_output=True,
            text=True,
            timeout=300,
        )

        assert result.returncode == 0, f'Docker execution failed: {result.stderr}'
        assert os.path.exists(output_file), 'Output file was not created'

        # Check that output contains expected fields and shows container environment
        with open(output_file, 'r') as f:
            content = f.read()
            assert 'added_field_trivial: sample' in content
            assert "uname_ret: '0'" in content
            assert "pwd_ret: '0'" in content
            # yosys_path_ret can be '0' or '1' depending on whether yosys is locally installed
            assert 'yosys_path_ret:' in content  # Just check that the field exists
            # Container should show Linux and /code/workspace/repo path
            assert 'Linux' in content
            assert '/code/workspace/repo' in content
            # Check that original input data is preserved
            assert 'POTATO: foo' in content
            assert 'FOOO_VAR: another_value' in content

    @pytest.mark.slow
    def test_docker_execution_with_repo_mount(self, input_file, output_file):
        """Test Docker execution with repo directory mounted."""
        env = os.environ.copy()
        # Get paths relative to the project root
        project_root = Path(__file__).parent.parent.parent.parent.parent
        repo_path = project_root / 'output/local/repo'

        env.update(
            {
                'HAGENT_DOCKER': DEFAULT_HAGENT_DOCKER,
                'HAGENT_REPO_DIR': str(repo_path),
            }
        )

        # Remove other directory env vars to test partial mounting
        for key in ['HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR']:
            env.pop(key, None)

        # Ensure repo directory exists
        os.makedirs(repo_path, exist_ok=True)

        # Get the trivial.py path relative to the current working directory
        trivial_script = Path(__file__).parent.parent / 'trivial.py'

        result = subprocess.run(
            ['uv', 'run', 'python', str(trivial_script), input_file, '-o', output_file],
            env=env,
            capture_output=True,
            text=True,
            timeout=300,
        )

        assert result.returncode == 0, f'Docker execution with repo mount failed: {result.stderr}'
        assert os.path.exists(output_file), 'Output file was not created'

        # Check that output contains expected fields
        with open(output_file, 'r') as f:
            content = f.read()
            assert 'added_field_trivial: sample' in content
            assert "uname_ret: '0'" in content
            assert "pwd_ret: '0'" in content
            # yosys_path_ret can be '0' or '1' depending on whether yosys is locally installed
            assert 'yosys_path_ret:' in content  # Just check that the field exists
            # Check that original input data is preserved
            assert 'POTATO: foo' in content
            assert 'FOOO_VAR: another_value' in content

    @pytest.mark.slow
    def test_docker_execution_with_absolute_paths(self, input_file, output_file):
        """Test Docker execution with absolute paths for mounting."""
        env = os.environ.copy()
        # Get paths relative to the project root
        project_root = Path(__file__).parent.parent.parent.parent.parent
        repo_dir = (project_root / 'output/local/repo').resolve()
        cache_dir = (project_root / 'output/local/cache').resolve()

        env.update(
            {
                'HAGENT_DOCKER': DEFAULT_HAGENT_DOCKER,
                'HAGENT_REPO_DIR': str(repo_dir),
                'HAGENT_CACHE_DIR': str(cache_dir),
            }
        )

        # Ensure directories exist
        os.makedirs(repo_dir, exist_ok=True)
        os.makedirs(cache_dir, exist_ok=True)

        # Get the trivial.py path relative to the current working directory
        trivial_script = Path(__file__).parent.parent / 'trivial.py'

        result = subprocess.run(
            ['uv', 'run', 'python', str(trivial_script), input_file, '-o', output_file],
            env=env,
            capture_output=True,
            text=True,
            timeout=300,
        )

        assert result.returncode == 0, f'Docker execution with absolute paths failed: {result.stderr}'
        assert os.path.exists(output_file), 'Output file was not created'

        # Check that output contains expected fields
        with open(output_file, 'r') as f:
            content = f.read()
            assert 'added_field_trivial: sample' in content
            assert "uname_ret: '0'" in content

    def test_local_execution_missing_env_vars(self, input_file, output_file):
        """Test that local execution fails when required environment variables are missing."""
        env = os.environ.copy()
        env.pop('HAGENT_DOCKER', None)

        # Remove required env vars
        for key in ['HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR']:
            env.pop(key, None)

        # Get the trivial.py path relative to the current working directory
        trivial_script = Path(__file__).parent.parent / 'trivial.py'

        result = subprocess.run(
            ['uv', 'run', 'python', str(trivial_script), input_file, '-o', output_file], env=env, capture_output=True, text=True
        )

        assert result.returncode != 0, 'Local execution should fail without required env vars'
        assert 'Local execution mode requires these environment variables' in result.stderr

    def test_invalid_execution_mode(self, input_file, output_file):
        """Test that invalid execution mode fails gracefully."""
        env = os.environ.copy()
        # Invalid mode test - set invalid HAGENT_DOCKER

        # Get the trivial.py path relative to the current working directory
        trivial_script = Path(__file__).parent.parent / 'trivial.py'

        result = subprocess.run(
            ['uv', 'run', 'python', str(trivial_script), input_file, '-o', output_file], env=env, capture_output=True, text=True
        )

        assert result.returncode != 0, 'Should fail with invalid execution mode'
        # Check for error message

    def test_missing_execution_mode(self, input_file, output_file):
        """Test that missing HAGENT_DOCKER (execution mode) fails gracefully."""
        env = os.environ.copy()
        # Remove HAGENT_DOCKER to test missing execution mode
        env.pop('HAGENT_DOCKER', None)
        # Also ensure repo/build/cache dirs are not set to trigger the error
        for var in ['HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR']:
            env.pop(var, None)

        # Get the trivial.py path relative to the current working directory
        trivial_script = Path(__file__).parent.parent / 'trivial.py'

        result = subprocess.run(
            ['uv', 'run', 'python', str(trivial_script), input_file, '-o', output_file], env=env, capture_output=True, text=True
        )

        assert result.returncode != 0, 'Should fail without execution mode'
        # The error should be about missing environment configuration


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
