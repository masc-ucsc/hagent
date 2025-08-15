#!/usr/bin/env python3
"""
Pytest test suite for File_manager basic functionality.

This test covers:
1. File copying and basic container operations
2. Shell command execution with redirection
3. File content retrieval and modification
4. Diff generation and patch export
5. Error handling and edge cases
"""

import tempfile
import os
import uuid
import pytest
from hagent.tool.file_manager import File_manager


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

    # Use local directories that tests can actually create and access
    repo_dir = os.path.abspath('.')  # Current working directory
    build_dir = os.path.join(tempfile.gettempdir(), 'hagent_test_build')
    cache_dir = os.path.join(tempfile.gettempdir(), 'hagent_test_cache')

    # Create directories if they don't exist
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


def teardown_module():
    """Clean up any remaining anonymous checkpoints after running all tests in this module."""
    # The container cache should be auto-cleaned by the last instance destructor,
    # but we still clean up any orphaned anonymous checkpoints as a safety measure
    # File_manager.cleanup_all_anonymous_checkpoints()


class TestFileManagerBasics:
    """Test suite for File_manager basic functionality."""

    def _ensure_patch_available(self, fm):
        """Helper method to ensure patch utility is available in container."""
        # Check if patch is already available
        rc, _, _ = fm.run('which patch')
        if rc == 0:
            return True

        # Try to install patch
        rc, _, _ = fm.run('apk update && apk add patch')
        if rc != 0:
            pytest.skip('Cannot install patch utility - skipping patch tests')
        return True

    @pytest.fixture
    def temp_files(self):
        """Create temporary test files and clean them up after test."""
        temp_file_name = f'tmp_{uuid.uuid4().hex}.txt'
        temp_file_host_path = os.path.join(tempfile.gettempdir(), temp_file_name)
        greeting_host_path = os.path.join(tempfile.gettempdir(), 'greeting.txt')
        yaml_path = os.path.join(tempfile.gettempdir(), f'test_patches_{uuid.uuid4().hex}.yaml')

        # Create initial test files
        with open(temp_file_host_path, 'w') as f:
            f.write('potato')

        with open(greeting_host_path, 'w') as f:
            f.write('Hello\n')

        yield {
            'temp_file_name': temp_file_name,
            'temp_file_host_path': temp_file_host_path,
            'greeting_host_path': greeting_host_path,
            'yaml_path': yaml_path,
        }

        # Cleanup
        for path in [temp_file_host_path, greeting_host_path, yaml_path]:
            if os.path.exists(path):
                os.remove(path)

    @pytest.fixture
    def file_manager(self):
        """Create and setup a File_manager instance."""
        fm = File_manager(image='mascucsc/hagent-simplechisel:2025.08')
        assert fm.setup(), f'Setup failed: {fm.get_error()}'
        yield fm
        # Cleanup: ensure the instance is properly destroyed
        try:
            del fm
        except Exception:
            pass

    def test_file_copying_and_listing(self, file_manager, temp_files):
        """Test basic file copying and container operations."""
        fm = file_manager

        # Copy files to container
        assert fm.copy_file(host_path=temp_files['temp_file_host_path'], container_path=temp_files['temp_file_name']), (
            f'Copy temp file failed: {fm.get_error()}'
        )

        assert fm.copy_file(host_path=temp_files['greeting_host_path'], container_path='greeting.txt'), (
            f'Copy greeting file failed: {fm.get_error()}'
        )

        # Verify files exist in container
        rc, out, err = fm.run('ls -la')
        assert rc == 0, f'Container listing failed - RC: {rc}, ERR: {err}'
        assert 'greeting.txt' in out
        assert temp_files['temp_file_name'] in out

    def test_working_directory_and_basic_commands(self, file_manager):
        """Test working directory and basic command execution."""
        fm = file_manager

        # Test basic echo command
        rc, out, err = fm.run('echo "test"')
        assert rc == 0, f'Basic echo failed - RC: {rc}, ERR: {err}'
        assert 'test' in out

        # Test shell availability
        rc, out, err = fm.run('which sh')
        assert rc == 0, f'Shell check failed - RC: {rc}, ERR: {err}'
        assert '/bin/sh' in out or '/sh' in out

    def test_file_reading_and_modification(self, file_manager, temp_files):
        """Test file reading and shell redirection operations."""
        fm = file_manager

        # Copy initial files
        assert fm.copy_file(temp_files['greeting_host_path'], 'greeting.txt')
        assert fm.copy_file(temp_files['temp_file_host_path'], temp_files['temp_file_name'])

        # Verify initial file content
        rc, out, err = fm.run('cat greeting.txt')
        assert rc == 0, f'Failed to read greeting.txt - RC: {rc}, ERR: {err}'
        assert out.strip() == 'Hello'

        # Test file append operation
        rc, out, err = fm.run('echo "World" >> greeting.txt')
        assert rc == 0, f'Echo append failed - RC: {rc}, ERR: {err}'

        # Verify append worked
        rc, out, err = fm.run('cat greeting.txt')
        assert rc == 0, f'Failed to read modified greeting.txt - RC: {rc}, ERR: {err}'
        expected_content = 'Hello\nWorld'
        assert out.strip() == expected_content

        # Test file overwrite operation
        rc, out, err = fm.run(f'echo "destroyer" > {temp_files["temp_file_name"]}')
        assert rc == 0, f'Echo overwrite failed - RC: {rc}, ERR: {err}'

        # Verify overwrite worked
        rc, out, err = fm.run(f'cat {temp_files["temp_file_name"]}')
        assert rc == 0, f'Failed to read modified temp file - RC: {rc}, ERR: {err}'
        assert out.strip() == 'destroyer'

    def test_get_file_content_api(self, file_manager, temp_files):
        """Test the get_file_content API method."""
        fm = file_manager

        # Copy and modify files
        assert fm.copy_file(temp_files['greeting_host_path'], 'greeting.txt')
        assert fm.copy_file(temp_files['temp_file_host_path'], temp_files['temp_file_name'])

        # Modify files
        rc, _, _ = fm.run('echo "World" >> greeting.txt')
        assert rc == 0

        rc, _, _ = fm.run(f'echo "destroyer" > {temp_files["temp_file_name"]}')
        assert rc == 0

        # Test get_file_content method
        greeting_content = fm.get_file_content('greeting.txt')
        assert greeting_content == 'Hello\nWorld\n'

        temp_content = fm.get_file_content(temp_files['temp_file_name'])
        assert temp_content == 'destroyer\n'


    def test_patch_export(self, file_manager, temp_files):
        """Test YAML patch export functionality."""
        fm = file_manager

        # Copy and modify files
        assert fm.copy_file(temp_files['greeting_host_path'], 'greeting.txt')
        assert fm.copy_file(temp_files['temp_file_host_path'], temp_files['temp_file_name'])

        # Make modifications
        rc, _, _ = fm.run('echo "World" >> greeting.txt')
        assert rc == 0

        rc, _, _ = fm.run(f'echo "destroyer" > {temp_files["temp_file_name"]}')
        assert rc == 0

        # Export patches
        assert fm.save_patches(host_path=temp_files['yaml_path'], name='test_session'), f'Patch export failed: {fm.get_error()}'

        assert os.path.exists(temp_files['yaml_path']), 'YAML file should be created'

        # Verify YAML content structure
        import yaml

        with open(temp_files['yaml_path'], 'r') as f:
            data = yaml.safe_load(f)

        assert 'test_session' in data
        session = data['test_session']
        assert 'metadata' in session
        assert 'patches' in session
        assert 'timestamp' in session['metadata']
        assert 'image' in session['metadata']
        assert session['metadata']['image'] == 'mascucsc/hagent-simplechisel:2025.08'

    def test_original_files_unchanged(self, file_manager, temp_files):
        """Test that original host files remain unchanged after container operations."""
        fm = file_manager

        # Copy and modify files in container
        assert fm.copy_file(temp_files['greeting_host_path'], 'greeting.txt')
        assert fm.copy_file(temp_files['temp_file_host_path'], temp_files['temp_file_name'])

        rc, _, _ = fm.run('echo "World" >> greeting.txt')
        assert rc == 0

        rc, _, _ = fm.run(f'echo "destroyer" > {temp_files["temp_file_name"]}')
        assert rc == 0

        # Verify original host files are unchanged
        with open(temp_files['greeting_host_path'], 'r') as f:
            content = f.read()
            assert content == 'Hello\n', 'Original greeting file should be unchanged'

        with open(temp_files['temp_file_host_path'], 'r') as f:
            content = f.read()
            assert content == 'potato', 'Original temp file should be unchanged'

    def test_error_handling(self, file_manager):
        """Test error handling for various edge cases."""
        fm = file_manager

        # Test reading non-existent file
        content = fm.get_file_content('nonexistent.txt')
        assert content == '', 'Should return empty string for non-existent file'
        assert 'not found' in fm.get_error().lower()

        # Test diff for non-tracked file
        diff = fm.get_diff('nonexistent.txt')
        assert diff == '', 'Should return empty diff for non-tracked file'
        assert 'not found' in fm.get_error().lower()

        # Test failed command
        rc, out, err = fm.run('nonexistent-command-12345')
        assert rc != 0, 'Non-existent command should fail'

    def test_multiple_command_execution(self, file_manager, temp_files):
        """Test that multiple commands can be executed in sequence."""
        fm = file_manager

        # Copy initial file
        assert fm.copy_file(temp_files['greeting_host_path'], 'greeting.txt')

        # Execute multiple commands
        commands = ['echo "Line 1" >> greeting.txt', 'echo "Line 2" >> greeting.txt', 'echo "Line 3" >> greeting.txt']

        for cmd in commands:
            rc, _, _ = fm.run(cmd)
            assert rc == 0, f'Command failed: {cmd}'

        # Verify final content
        content = fm.get_file_content('greeting.txt')
        expected_lines = ['Hello', 'Line 1', 'Line 2', 'Line 3']
        for line in expected_lines:
            assert line in content



    def test_install_executable_with_filename(self, file_manager, temp_files):
        """Test installing executable with custom filename."""
        fm = file_manager

        # Create a simple executable script on host
        script_content = '#!/bin/sh\necho "Renamed executable test"\n'
        script_path = os.path.join(tempfile.gettempdir(), f'original_name_{uuid.uuid4().hex}.sh')

        with open(script_path, 'w') as f:
            f.write(script_content)

        try:
            # Install executable with custom name
            custom_name = '/usr/local/bin/my_custom_tool'
            assert fm.install_executable(script_path, custom_name), f'Failed to install with custom name: {fm.get_error()}'

            # Verify executable exists with custom name
            rc, out, err = fm.run(f'ls -la {custom_name}')
            assert rc == 0, f'Executable not found with custom name: {err}'
            assert 'rwxr-xr-x' in out or '-rwxr-xr-x' in out, f'Executable should have 755 permissions: {out}'

            # Verify executable can be run with custom name
            rc, out, err = fm.run('my_custom_tool')  # Should be in PATH
            assert rc == 0, f'Failed to execute script with custom name: {err}'
            assert 'Renamed executable test' in out, f'Script output incorrect: {out}'

        finally:
            # Cleanup host file
            if os.path.exists(script_path):
                os.remove(script_path)



    def test_patch_file_nonexistent_file(self, file_manager):
        """Test patch_file behavior with non-existent target file."""
        fm = file_manager
        self._ensure_patch_available(fm)

        # Try to patch a file that doesn't exist
        patch_content = """--- a/nonexistent.txt
+++ b/nonexistent.txt
@@ -1 +1 @@
-old line
+new line"""

        success = fm.patch_file('nonexistent.txt', patch_content)
        # This might succeed if patch creates the file, or fail - behavior depends on patch implementation
        # We'll just verify it doesn't crash and gives appropriate feedback
        assert isinstance(success, bool), 'Should return boolean result'
        if not success:
            assert fm.get_error(), 'Should have error message when failing'

    def test_patch_file_before_setup(self, temp_files):
        """Test patch_file fails when called before setup."""
        fm = File_manager(image='mascucsc/hagent-simplechisel:2025.08')
        # Don't call setup()

        patch_content = """--- a/test.txt
+++ b/test.txt
@@ -1 +1 @@
-old
+new"""

        success = fm.patch_file('test.txt', patch_content)
        assert not success, 'patch_file should fail before setup'
        assert 'must be called after setup' in fm.get_error()




