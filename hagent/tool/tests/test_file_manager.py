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
        fm = File_manager(image='alpine:latest')
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
        diff = fm2.get_diff('greeting.txt')  # Get diff does not need track_file
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
        fm.setup()  # Cleanup previous container variable reuse

        # 1. Copy a file first (before any run commands)
        assert fm.copy_file(temp_files['temp_file_host_path'], 'copied_file.txt'), f'Failed to copy file: {fm.get_error()}'

        # 2. Create a file that exists in the original container (like /etc/alpine-release)
        # Check what files exist in alpine
        rc, out, _ = fm.run('ls /etc/')
        assert rc == 0

        # Use /etc/hostname as it should exist and be simple
        fm.get_file_content('/etc/hostname')

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

        fm.track_dir('.', ext='.txt')
        full_path_set = fm.get_current_tracked_files()
        basenames = {os.path.basename(path) for path in full_path_set}
        assert 'copied_file.txt' in basenames
        assert 'greetings2.txt' in basenames
        assert 'hostname' in basenames
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

    def test_patch_file_basic_functionality(self, file_manager, temp_files):
        """Test basic patch_file functionality with unified diff."""
        fm = file_manager
        self._ensure_patch_available(fm)

        # Create initial file
        initial_content = 'line1\nline2\nline3\n'
        rc, _, _ = fm.run(f'cat > test_patch.txt << EOF\n{initial_content}EOF')
        assert rc == 0

        # Create a simple unified diff patch
        patch_content = """--- a/test_patch.txt
+++ b/test_patch.txt
@@ -1,3 +1,3 @@
 line1
-line2
+modified_line2
 line3"""

        # Apply the patch
        success = fm.patch_file('test_patch.txt', patch_content)
        assert success, f'patch_file should succeed: {fm.get_error()}'

        # Verify the file was patched correctly
        content = fm.get_file_content('test_patch.txt')
        expected = 'line1\nmodified_line2\nline3\n'
        assert content == expected, f'Content mismatch. Expected: {repr(expected)}, Got: {repr(content)}'

    def test_patch_file_with_context_lines(self, file_manager):
        """Test patch_file with more context lines."""
        fm = file_manager
        self._ensure_patch_available(fm)

        # Create a larger file with more context
        initial_content = """header line
context1
context2
old target line
context3
context4
footer line"""

        rc, _, _ = fm.run(f'cat > context_test.txt << EOF\n{initial_content}\nEOF')
        assert rc == 0

        # Create patch with context
        patch_content = """--- a/context_test.txt
+++ b/context_test.txt
@@ -1,7 +1,7 @@
 header line
 context1
 context2
-old target line
+new target line
 context3
 context4
 footer line"""

        # Apply patch
        success = fm.patch_file('context_test.txt', patch_content)
        assert success, f'patch_file with context should succeed: {fm.get_error()}'

        # Verify result
        content = fm.get_file_content('context_test.txt')
        assert 'new target line' in content
        assert 'old target line' not in content

    def test_patch_file_multiple_hunks(self, file_manager):
        """Test patch_file with multiple hunks in the same file."""
        fm = file_manager
        self._ensure_patch_available(fm)

        # Create initial file
        initial_content = """section1_line1
section1_line2
section1_line3

section2_line1
section2_line2
section2_line3

section3_line1
section3_line2
section3_line3"""

        rc, _, _ = fm.run(f'cat > multi_hunk.txt << EOF\n{initial_content}\nEOF')
        assert rc == 0

        # Create patch with multiple hunks
        patch_content = """--- a/multi_hunk.txt
+++ b/multi_hunk.txt
@@ -1,3 +1,3 @@
 section1_line1
-section1_line2
+section1_modified
 section1_line3
@@ -9,3 +9,3 @@
 
 section3_line1
-section3_line2
+section3_modified
 section3_line3"""

        # Apply patch
        success = fm.patch_file('multi_hunk.txt', patch_content)
        assert success, f'multi-hunk patch should succeed: {fm.get_error()}'

        # Verify both modifications
        content = fm.get_file_content('multi_hunk.txt')
        assert 'section1_modified' in content
        assert 'section3_modified' in content
        assert 'section1_line2' not in content
        assert 'section3_line2' not in content

    def test_patch_file_invalid_patch_format(self, file_manager):
        """Test patch_file with malformed patch content."""
        fm = file_manager
        self._ensure_patch_available(fm)

        # Create test file
        rc, _, _ = fm.run('echo "test content" > invalid_patch_test.txt')
        assert rc == 0

        # Try to apply invalid patch
        invalid_patch = 'This is not a valid patch format\nAt all!'

        success = fm.patch_file('invalid_patch_test.txt', invalid_patch)
        assert not success, 'patch_file should fail with invalid patch format'
        assert fm.get_error(), 'Should have error message for invalid patch'

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
        fm = File_manager(image='alpine:latest')
        # Don't call setup()

        patch_content = """--- a/test.txt
+++ b/test.txt
@@ -1 +1 @@
-old
+new"""

        success = fm.patch_file('test.txt', patch_content)
        assert not success, 'patch_file should fail before setup'
        assert 'must be called after setup' in fm.get_error()

    def test_patch_file_with_special_characters(self, file_manager):
        """Test patch_file with files containing special characters."""
        fm = file_manager
        self._ensure_patch_available(fm)

        # Create file with special characters
        special_content = """line with "quotes"
line with 'apostrophes'
line with $variables and &symbols
line with unicode: café résumé"""

        rc, _, _ = fm.run(f"cat > special_chars.txt << 'EOF'\n{special_content}\nEOF")
        assert rc == 0

        # Create patch to modify unicode line
        patch_content = """--- a/special_chars.txt
+++ b/special_chars.txt
@@ -2,3 +2,3 @@
 line with 'apostrophes'
 line with $variables and &symbols
-line with unicode: café résumé
+line with unicode: café résumé (modified)"""

        success = fm.patch_file('special_chars.txt', patch_content)
        assert success, f'patch with special chars should succeed: {fm.get_error()}'

        # Verify the modification
        content = fm.get_file_content('special_chars.txt')
        assert '(modified)' in content

    def test_patch_file_empty_patch(self, file_manager):
        """Test patch_file with empty patch content."""
        fm = file_manager
        self._ensure_patch_available(fm)

        # Create test file
        rc, _, _ = fm.run('echo "unchanged content" > empty_patch_test.txt')
        assert rc == 0

        # Try empty patch
        success = fm.patch_file('empty_patch_test.txt', '')
        # Empty patch might be handled differently by different patch implementations
        assert isinstance(success, bool), 'Should return boolean for empty patch'

    def test_patch_file_state_validation(self, file_manager):
        """Test that patch_file validates file manager state correctly."""
        fm = file_manager
        self._ensure_patch_available(fm)

        # Test after setup (should work)
        rc, _, _ = fm.run('echo "test" > state_test.txt')
        assert rc == 0

        patch_content = """--- a/state_test.txt
+++ b/state_test.txt
@@ -1 +1 @@
-test
+patched"""

        success = fm.patch_file('state_test.txt', patch_content)
        assert success, f'patch_file should work after setup: {fm.get_error()}'

        # Verify the file was patched
        content = fm.get_file_content('state_test.txt')
        assert content.strip() == 'patched'

    def test_patch_file_integration_with_get_diff(self, file_manager, temp_files):
        """Integration test: create diff, then apply as patch."""
        fm = file_manager
        self._ensure_patch_available(fm)

        # Copy initial file and track it
        assert fm.copy_file(temp_files['greeting_host_path'], 'integration_test.txt')

        # Create checkpoint for reference
        checkpoint = fm.image_checkpoint()
        assert checkpoint

        # Create new instance from checkpoint and modify file
        fm2 = File_manager(image=checkpoint)
        assert fm2.setup()
        self._ensure_patch_available(fm2)

        rc, _, _ = fm2.run('echo "World" >> integration_test.txt')
        assert rc == 0

        # Get the diff
        diff = fm2.get_diff('integration_test.txt')
        assert diff, 'Should have diff content'

        # Create third instance to apply the patch
        fm3 = File_manager(image=checkpoint)
        assert fm3.setup()
        self._ensure_patch_available(fm3)

        # Apply the diff as a patch
        success = fm3.patch_file('integration_test.txt', diff)
        assert success, f'Should be able to apply generated diff as patch: {fm3.get_error()}'

        # Verify both instances have same content
        content2 = fm2.get_file_content('integration_test.txt')
        content3 = fm3.get_file_content('integration_test.txt')
        assert content2 == content3, 'Content should match after applying diff as patch'


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

        # fm.image_checkpoint("test")

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
