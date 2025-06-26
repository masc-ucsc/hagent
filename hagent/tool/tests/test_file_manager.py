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


class TestFileManagerBasics:
    """Test suite for File_manager basic functionality."""

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
        fm = File_manager(image='alpine:latest')
        assert fm.setup(), f'Setup failed: {fm.get_error()}'
        return fm

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

    def test_diff_generation(self, file_manager, temp_files):
        """Test unified diff generation functionality."""
        fm = file_manager

        # Copy and modify file
        assert fm.copy_file(temp_files['greeting_host_path'], 'greeting.txt')

        rc, _, _ = fm.run('echo "World" >> greeting.txt')
        assert rc == 0

        # Test diff generation
        diff = fm.get_diff('greeting.txt')
        assert diff, 'Diff should not be empty'
        assert '+World' in diff, 'Diff should show added line'
        assert 'greeting.txt' in diff, 'Diff should reference filename'
        assert '@@' in diff, 'Diff should have hunk headers'

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
        assert session['metadata']['image'] == 'alpine:latest'

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
        assert 'not tracked' in fm.get_error().lower()

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

    def test_complete_workflow(self, file_manager, temp_files):
        """Integration test covering the complete workflow."""
        fm = file_manager

        # 1. Copy files
        assert fm.copy_file(temp_files['greeting_host_path'], 'greeting.txt')
        assert fm.copy_file(temp_files['temp_file_host_path'], temp_files['temp_file_name'])

        # 2. Modify files
        rc, _, _ = fm.run('echo "World" >> greeting.txt')
        assert rc == 0

        rc, _, _ = fm.run(f'echo "destroyer" > {temp_files["temp_file_name"]}')
        assert rc == 0

        # 3. Verify content
        greeting_content = fm.get_file_content('greeting.txt')
        assert greeting_content == 'Hello\nWorld\n'

        temp_content = fm.get_file_content(temp_files['temp_file_name'])
        assert temp_content == 'destroyer\n'

        # 4. Check diffs
        diff = fm.get_diff('greeting.txt')
        assert '+World' in diff

        # 5. Export patches
        assert fm.save_patches(temp_files['yaml_path'], 'integration_test')
        assert os.path.exists(temp_files['yaml_path'])

        # 6. Verify host files unchanged
        with open(temp_files['temp_file_host_path'], 'r') as f:
            assert f.read() == 'potato'


# Standalone test runner for compatibility
def test_file_manager_integration():
    """Standalone integration test that can be run directly."""
    print('Running File_manager integration test...')

    # Create temporary files
    temp_file_name = f'tmp_{uuid.uuid4().hex}.txt'
    temp_file_host_path = os.path.join(tempfile.gettempdir(), temp_file_name)
    greeting_host_path = os.path.join(tempfile.gettempdir(), 'greeting.txt')
    yaml_path = os.path.join(tempfile.gettempdir(), f'test_patches_{uuid.uuid4().hex}.yaml')

    with open(temp_file_host_path, 'w') as f:
        f.write('potato')

    with open(greeting_host_path, 'w') as f:
        f.write('Hello\n')

    try:
        # Initialize and test
        fm = File_manager(image='alpine:latest')
        assert fm.setup(), f'Setup failed: {fm.get_error()}'

        # Run the complete workflow
        assert fm.copy_file(temp_file_host_path, temp_file_name)
        assert fm.copy_file(greeting_host_path, 'greeting.txt')

        rc, _, _ = fm.run('echo "World" >> greeting.txt')
        assert rc == 0

        rc, _, _ = fm.run(f'echo "destroyer" > {temp_file_name}')
        assert rc == 0

        # Verify results
        greeting_content = fm.get_file_content('greeting.txt')
        assert greeting_content == 'Hello\nWorld\n'

        temp_content = fm.get_file_content(temp_file_name)
        assert temp_content == 'destroyer\n'

        diff = fm.get_diff('greeting.txt')
        assert '+World' in diff

        assert fm.save_patches(yaml_path, 'standalone_test')
        assert os.path.exists(yaml_path)

        print('✓ All integration tests passed!')

    finally:
        # Cleanup
        for path in [temp_file_host_path, greeting_host_path, yaml_path]:
            if os.path.exists(path):
                os.remove(path)


if __name__ == '__main__':
    test_file_manager_integration()
