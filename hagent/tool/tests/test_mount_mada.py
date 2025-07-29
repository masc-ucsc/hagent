#!/usr/bin/env python3
"""
Test for mounting /mada/software directory in File_manager.

This test verifies that the add_mount functionality works correctly
for mounting /mada/software from the host to the container.
"""

import os
import pytest
from hagent.tool.file_manager import File_manager


class TestMountMada:
    """Test suite for mounting /mada/software directory."""

    def test_add_mount_mada_software(self):
        """Test mounting /mada/software if it exists on the local machine."""
        host_path = '/mada/software'
        container_path = '/mada/software'

        # Check if the directory exists on the local machine
        if not os.path.exists(host_path):
            print(f'Warning: {host_path} does not exist on the local machine. Test is disabled.')
            pytest.skip(f'Directory {host_path} does not exist on local machine')
            return

        # Use a lightweight Alpine image for testing
        with File_manager('alpine:latest') as fm:
            # Test add_mount before setup
            assert fm.add_mount(host_path, container_path), 'add_mount should succeed'

            # Setup the container
            assert fm.setup(), f'Setup failed: {fm.get_error()}'

            # Verify the mount is accessible in the container
            exit_code, stdout, stderr = fm.run(f'ls -la {container_path}', quiet=True)
            assert exit_code == 0, f'Failed to access mounted directory: {stderr}'

            # Verify it's actually the mounted directory by checking if it's not empty
            # (assuming /mada/software has some content)
            exit_code, stdout, stderr = fm.run(f'test -d {container_path}', quiet=True)
            assert exit_code == 0, f'Mounted directory should exist: {stderr}'

            print(f'Successfully mounted {host_path} to {container_path}')

    def test_add_mount_after_setup_fails(self):
        """Test that add_mount fails when called after setup()."""
        host_path = '/mada/software'
        container_path = '/mada/software'

        # Check if the directory exists on the local machine
        if not os.path.exists(host_path):
            print(f'Warning: {host_path} does not exist on the local machine. Test is disabled.')
            pytest.skip(f'Directory {host_path} does not exist on local machine')
            return

        with File_manager('alpine:latest') as fm:
            # Setup first
            assert fm.setup(), f'Setup failed: {fm.get_error()}'

            # Try to add mount after setup - should fail
            assert not fm.add_mount(host_path, container_path), 'add_mount should fail after setup'

            # Check error message
            error = fm.get_error()
            assert 'add_mount must be called before setup()' in error, f'Expected specific error message, got: {error}'


def run_tests_directly():
    """Run tests directly when script is executed."""
    host_path = '/mada/software'

    # Check if the directory exists on the local machine
    if not os.path.exists(host_path):
        print(f'Warning: {host_path} does not exist on the local machine. Tests are disabled.')
        return

    print(f'Running tests for mounting {host_path}...')

    # Create test instance and run tests
    test_instance = TestMountMada()

    try:
        print('\n1. Testing add_mount functionality...')
        test_instance.test_add_mount_mada_software()
        print('✓ add_mount test passed')

        print('\n2. Testing add_mount after setup fails...')
        test_instance.test_add_mount_after_setup_fails()
        print('✓ add_mount after setup test passed')

        print('\n✓ All tests passed!')

    except Exception as e:
        print(f'\n✗ Test failed: {e}')
        raise


if __name__ == '__main__':
    run_tests_directly()
