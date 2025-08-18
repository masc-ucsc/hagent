#!/usr/bin/env python3
"""
Converted test suite for container operations using new Executor API.

This test covers:
1. File copying and basic container operations
2. Shell command execution with redirection
3. File content retrieval and modification
4. Error handling and edge cases

Converted from original test_file_manager.py to use new Executor API.
"""

import os
import uuid
import pytest
from hagent.inou.container_manager import ContainerManager
from hagent.inou.executor import ExecutorFactory
from hagent.inou.path_manager import PathManager


@pytest.fixture(scope='session', autouse=True)
def setup_hagent_environment():
    """Setup HAGENT environment variables for Docker mode tests."""
    original_env = {}

    # Save original environment
    hagent_vars = ['HAGENT_EXECUTION_MODE', 'HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR']
    for var in hagent_vars:
        original_env[var] = os.environ.get(var)

    # Set Docker mode environment with host-accessible paths for testing
    os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

    # Use local directories that Docker can easily mount
    # IMPORTANT: Don't mount the repository root directory - use output subdirectory instead
    repo_dir = os.path.abspath('./output/test_executor_repo')  # Use subdirectory instead of '.'
    build_dir = os.path.abspath('./output/test_executor_build')
    cache_dir = os.path.abspath('./output/test_executor_cache')

    # Create directories if they don't exist
    os.makedirs(repo_dir, exist_ok=True)
    os.makedirs(build_dir, exist_ok=True)
    os.makedirs(cache_dir, exist_ok=True)

    os.environ['HAGENT_REPO_DIR'] = repo_dir
    os.environ['HAGENT_BUILD_DIR'] = build_dir
    os.environ['HAGENT_CACHE_DIR'] = cache_dir

    yield

    # Restore original environment
    for var, value in original_env.items():
        if value is None:
            os.environ.pop(var, None)
        else:
            os.environ[var] = value


@pytest.mark.slow
class TestExecutorContainerOperations:
    """Test suite for container operations using new Executor API."""

    @pytest.fixture
    def temp_files(self):
        """Create temporary test files and clean them up after test."""
        temp_file_name = f'tmp_{uuid.uuid4().hex}.txt'
        test_output_dir = os.path.abspath('./output/test_executor_container_operations')
        os.makedirs(test_output_dir, exist_ok=True)

        temp_file_host_path = os.path.join(test_output_dir, temp_file_name)
        greeting_host_path = os.path.join(test_output_dir, 'greeting.txt')

        # Create initial test files
        with open(temp_file_host_path, 'w') as f:
            f.write('potato')

        with open(greeting_host_path, 'w') as f:
            f.write('Hello\n')

        yield {
            'temp_file_name': temp_file_name,
            'temp_file_host_path': temp_file_host_path,
            'greeting_host_path': greeting_host_path,
        }

        # Cleanup
        for path in [temp_file_host_path, greeting_host_path]:
            if os.path.exists(path):
                os.remove(path)

    @pytest.fixture
    def executor_setup(self):
        """Create and setup an Executor instance with ContainerManager."""
        # Ensure directories exist before creating path_manager
        cache_dir = os.environ.get('HAGENT_CACHE_DIR')
        if cache_dir:
            os.makedirs(cache_dir, exist_ok=True)

        path_manager = PathManager()
        container_manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08', path_manager)
        executor = ExecutorFactory.create_executor(container_manager)

        assert executor.setup(), f'Executor setup failed: {executor.get_error()}'

        yield executor, container_manager

        # Cleanup
        try:
            container_manager.cleanup()
        except Exception:
            pass

    def test_basic_command_execution(self, executor_setup):
        """Test working directory and basic command execution."""
        executor, _ = executor_setup

        # Test basic echo command
        rc, out, err = executor.run('echo "test"')
        assert rc == 0, f'Basic echo failed - RC: {rc}, ERR: {err}'
        assert 'test' in out

        # Test shell availability
        rc, out, err = executor.run('which sh')
        assert rc == 0, f'Shell check failed - RC: {rc}, ERR: {err}'
        assert '/bin/sh' in out or '/sh' in out

    def test_file_operations_via_container(self, executor_setup, temp_files):
        """Test file operations through container commands."""
        executor, container_manager = executor_setup

        # Copy file to container using container_manager's copy functionality
        # Note: In the new API, we use container_manager for file operations
        temp_file_content = 'potato'

        rc, out, err = executor.run('id')
        print(f'id result rc:{rc} out:{out} err:{err}')
        assert rc == 0

        rc, out, err = executor.run('ls -ald')
        print(f'ls result rc:{rc} out:{out} err:{err}')
        assert rc == 0

        # Create the test output directory in container and write content to a file there
        container_output_dir = 'output/test_executor_container_operations'
        container_temp_file = f'{container_output_dir}/{temp_files["temp_file_name"]}'

        rc, out, err = executor.run(f'mkdir -p {container_output_dir}')
        assert rc == 0, f'Directory creation failed - RC: {rc}, ERR: {err}'

        rc, out, err = executor.run(f'echo "{temp_file_content}" > {container_temp_file}')
        assert rc == 0, f'File write failed - RC: {rc}, ERR: {err}'

        # Verify file exists and has correct content
        rc, out, err = executor.run(f'cat {container_temp_file}')
        assert rc == 0, f'File read failed - RC: {rc}, ERR: {err}'
        assert temp_file_content in out

        # Test file modification
        rc, out, err = executor.run(f'echo "destroyer" > {container_temp_file}')
        assert rc == 0, f'File modification failed - RC: {rc}, ERR: {err}'

        # Verify modification
        rc, out, err = executor.run(f'cat {container_temp_file}')
        assert rc == 0, f'Modified file read failed - RC: {rc}, ERR: {err}'
        assert 'destroyer' in out

    def test_directory_operations(self, executor_setup):
        """Test directory listing and navigation."""
        executor, _ = executor_setup

        # Test directory listing
        rc, out, err = executor.run('ls -la')
        assert rc == 0, f'Directory listing failed - RC: {rc}, ERR: {err}'

        # Test working directory
        rc, out, err = executor.run('pwd')
        assert rc == 0, f'pwd command failed - RC: {rc}, ERR: {err}'
        # Should be in the repo workspace directory
        assert '/code/workspace/repo' in out

    def test_multiple_command_execution(self, executor_setup, temp_files):
        """Test executing multiple commands in sequence."""
        executor, _ = executor_setup

        # Create test output directory and greeting file there
        container_output_dir = 'output/test_executor_container_operations'
        container_greeting_file = f'{container_output_dir}/greeting.txt'

        rc, out, err = executor.run(f'mkdir -p {container_output_dir}')
        assert rc == 0, f'Directory creation failed - RC: {rc}, ERR: {err}'

        rc, out, err = executor.run(f'echo "Hello" > {container_greeting_file}')
        assert rc == 0, f'Create greeting failed - RC: {rc}, ERR: {err}'

        # Execute multiple commands
        commands = [
            f'echo "World" >> {container_greeting_file}',
            f'cat {container_greeting_file}',
            f'wc -l {container_greeting_file}',
        ]

        for cmd in commands:
            rc, _, _ = executor.run(cmd)
            assert rc == 0, f'Command failed: {cmd}'

        # Verify final content
        rc, out, err = executor.run(f'cat {container_greeting_file}')
        assert rc == 0, f'Final read failed - RC: {rc}, ERR: {err}'
        assert 'Hello' in out and 'World' in out

    def test_error_handling(self, executor_setup):
        """Test error handling for invalid operations."""
        executor, _ = executor_setup

        # Test nonexistent command
        rc, out, err = executor.run('nonexistent-command-12345')
        assert rc != 0, 'Should fail for nonexistent command'

        # Test reading nonexistent file
        rc, out, err = executor.run('cat nonexistent.txt')
        assert rc != 0, 'Should fail for nonexistent file'

    def test_executable_installation(self, executor_setup, temp_files):
        """Test installing and running executable scripts."""
        executor, _ = executor_setup

        # Create a simple executable script on host
        script_content = '#!/bin/sh\necho "Hello from custom script"\n'
        test_output_dir = os.path.abspath('./output/test_executor_container_operations')
        os.makedirs(test_output_dir, exist_ok=True)
        script_path = os.path.join(test_output_dir, 'test_script.sh')

        try:
            with open(script_path, 'w') as f:
                f.write(script_content)

            # Make it executable on host
            os.chmod(script_path, 0o755)

            # Note: In new API, we would need to implement file copying via container_manager
            # For now, we'll create the script in build directory to avoid repo mount execution restrictions
            custom_name = '/code/workspace/build/my_custom_tool'

            # Create script in container
            rc, out, err = executor.run(f"echo '{script_content}' > {custom_name}")
            assert rc == 0, f'Script creation failed - RC: {rc}, ERR: {err}'

            # Make executable
            rc, out, err = executor.run(f'chmod +x {custom_name}')
            assert rc == 0, f'chmod failed - RC: {rc}, ERR: {err}'

            # Test execution
            rc, out, err = executor.run(f'{custom_name}')
            assert rc == 0, f'Script execution failed - RC: {rc}, ERR: {err}'
            assert 'Hello from custom script' in out

        finally:
            # Cleanup host file
            if os.path.exists(script_path):
                os.remove(script_path)

    def test_patch_utilities_available(self, executor_setup):
        """Test that patch utilities are available for future patch operations."""
        executor, _ = executor_setup

        # Check if patch is available
        rc, out, err = executor.run('which patch')
        if rc != 0:
            # Try to install patch
            rc, out, err = executor.run('apk update && apk add patch')
            if rc != 0:
                pytest.skip('Cannot install patch utility - skipping patch availability test')

        # Verify patch is now available
        rc, out, err = executor.run('which patch')
        assert rc == 0, 'Patch utility should be available'
