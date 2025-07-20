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


def teardown_module():
    """Clean up any remaining anonymous checkpoints after running all tests in this module."""
    # The container cache should be auto-cleaned by the last instance destructor,
    # but we still clean up any orphaned anonymous checkpoints as a safety measure
    # File_manager.cleanup_all_anonymous_checkpoints()


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
        yield fm
        # Cleanup: ensure the instance is properly destroyed
        try:
            del fm
        except:
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

    def test_diff_generation(self, file_manager, temp_files):
        """Test unified diff generation functionality."""
        fm = file_manager

        # Copy and modify file
        assert fm.copy_file(temp_files['greeting_host_path'], 'greeting.txt')

        checkpoint = fm.image_checkpoint()
        assert checkpoint

        fm2 = File_manager(image=checkpoint)
        assert fm2.setup(), f'Setup failed: {fm2.get_error()}'

        rc, _, _ = fm2.run('echo "World" >> greeting.txt')
        assert rc == 0

        # Test diff generation
        diff = fm2.get_diff('greeting.txt') # Get diff does not need track_file
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

    def test_complete_workflow(self, file_manager, temp_files):
        """Integration test covering the complete workflow with proper tracking."""
        fm = file_manager
        fm.setup() # Cleanup previous container variable reuse

        # 1. Copy a file first (before any run commands)
        assert fm.copy_file(temp_files['temp_file_host_path'], 'copied_file.txt'), f'Failed to copy file: {fm.get_error()}'

        # 2. Create a file that exists in the original container (like /etc/alpine-release)
        # Check what files exist in alpine
        rc, out, _ = fm.run('ls /etc/')
        assert rc == 0

        # Use /etc/hostname as it should exist and be simple
        original_hostname = fm.get_file_content('/etc/hostname')

        # 3. Track the existing file (this is the key difference - track vs copy)
        assert fm.track_file('/etc/hostname'), f'Failed to track /etc/hostname: {fm.get_error()}'

        # 4. Modify the tracked file
        rc, _, _ = fm.run('echo "modified_hostname" > /etc/hostname')
        assert rc == 0

        # 5. Create a new file (not tracked originally)
        rc, _, _ = fm.run('echo "I am new" > greetings2.txt')
        assert rc == 0

        # 6. Modify the copied file multiple times to test that final state matters
        rc, _, _ = fm.run('echo "first change" >> copied_file.txt')
        assert rc == 0
        rc, _, _ = fm.run('echo "second change" >> copied_file.txt')
        assert rc == 0

        # 7. Verify content
        hostname_content = fm.get_file_content('/etc/hostname')
        assert hostname_content == 'modified_hostname\n'

        new_content = fm.get_file_content('greetings2.txt')
        assert new_content == 'I am new\n'

        # 8. Check diff against original container (not copied file)
        diff = fm.get_diff('/etc/hostname')
        assert 'modified_hostname' in diff, f'Diff should show hostname was modified. Got: {diff}'
        assert '/etc/hostname' in diff

        # 9. Get patch dict to test tracked files
        full_path_set = fm.get_current_tracked_files()
        assert len(full_path_set) == 1

        fm.track_dir('.', ext=".txt")
        full_path_set = fm.get_current_tracked_files()
        basenames = {os.path.basename(path) for path in full_path_set}
        assert "copied_file.txt" in basenames
        assert "greetings2.txt" in basenames
        assert "hostname" in basenames
        assert len(basenames) == 3

        patches = fm.get_patch_dict()

        # Should have the modified tracked file and copied file in patches
        tracked_found = False
        copied_found = False

        for patch in patches.get('patch', []) + patches.get('full', []):
            filename = patch['filename']
            if '/etc/hostname' in filename:
                tracked_found = True
                if 'diff' in patch:
                    assert 'modified_hostname' in patch['diff']
            elif 'copied_file.txt' in filename:
                copied_found = True

        assert tracked_found, 'Should find the tracked and modified /etc/hostname'
        assert copied_found, 'Should find the copied and modified file'

        # 10. Export patches
        assert fm.save_patches(temp_files['yaml_path'], 'integration_test')
        assert os.path.exists(temp_files['yaml_path'])

        # 11. Verify host files unchanged
        with open(temp_files['temp_file_host_path'], 'r') as f:
            assert f.read() == 'potato'

    def test_track_directory_with_extension_filter(self, file_manager):
        """Test that track_dir with extension filter only includes matching files in get_patch_dict."""
        fm = file_manager

        # 1. Use existing directory /etc which has files
        # Check what's in /etc first
        rc, out, _ = fm.run('ls /etc')
        assert rc == 0

        # 2. Track /etc directory with *.conf extension (Alpine has several .conf files)
        assert fm.track_dir('/etc', ext='.conf'), f'Failed to track directory: {fm.get_error()}'

        # 3. Modify a .conf file and create a non-.conf file
        # Modify an existing .conf file
        rc, _, _ = fm.run('echo "# Modified by test" >> /etc/sysctl.conf')
        assert rc == 0

        # Create a new .conf file
        rc, _, _ = fm.run('echo "# New config file" > /etc/test.conf')
        assert rc == 0

        # Create a non-.conf file (should be ignored)
        rc, _, _ = fm.run('echo "This should be ignored" > /etc/ignore.txt')
        assert rc == 0

        # 4. Get patch dict and verify only .conf files are included
        patches = fm.get_patch_dict()

        # Collect all filenames from patches
        all_filenames = []
        for patch in patches.get('patch', []) + patches.get('full', []):
            all_filenames.append(patch['filename'])

        # Check that only .conf files are included
        conf_files_found = [f for f in all_filenames if f.endswith('.conf')]
        txt_files_found = [f for f in all_filenames if f.endswith('.txt')]

        assert len(conf_files_found) >= 1, f'Expected at least 1 .conf file, found: {conf_files_found}'
        assert len(txt_files_found) == 0, f'Expected 0 .txt files, but found: {txt_files_found}'

        # Verify that our modified sysctl.conf and new test.conf are present
        sysctl_found = any('sysctl.conf' in f for f in conf_files_found)
        test_conf_found = any('test.conf' in f for f in conf_files_found)

        assert sysctl_found or test_conf_found, f'Expected to find sysctl.conf or test.conf in: {conf_files_found}'

        # Verify content contains our modifications for any .conf files found
        for patch in patches.get('patch', []) + patches.get('full', []):
            if 'sysctl.conf' in patch['filename']:
                content = patch.get('contents', '') or patch.get('diff', '')
                assert 'Modified by test' in content, 'sysctl.conf should contain our modification'
            elif 'test.conf' in patch['filename']:
                content = patch.get('contents', '') or patch.get('diff', '')
                assert 'New config file' in content, 'test.conf should contain our content'


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

        # Run the complete workflow with proper tracking
        # 1. Copy a file first (before any run commands)
        assert fm.copy_file(temp_file_host_path, temp_file_name)

        # 2. Track an existing file from the container (/etc/hostname)
        assert fm.track_file('/etc/hostname')

        # 3. Modify tracked file
        rc, _, _ = fm.run('echo "modified_hostname" > /etc/hostname')
        assert rc == 0

        # 4. Create new file
        rc, _, _ = fm.run('echo "I am new" > greetings2.txt')
        assert rc == 0

        # 5. Modify the copied file
        rc, _, _ = fm.run(f'echo "destroyer" > {temp_file_name}')
        assert rc == 0

        # Verify results
        hostname_content = fm.get_file_content('/etc/hostname')
        assert hostname_content == 'modified_hostname\n'

        new_content = fm.get_file_content('greetings2.txt')
        assert new_content == 'I am new\n'

        temp_content = fm.get_file_content(temp_file_name)
        assert temp_content == 'destroyer\n'

        # Test diff against original container
        diff = fm.get_diff('/etc/hostname')
        assert 'modified_hostname' in diff

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
