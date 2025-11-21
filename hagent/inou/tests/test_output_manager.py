#!/usr/bin/env python3

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..'))
from hagent.inou.output_manager import get_output_dir, get_output_path
from hagent.inou.path_manager import PathManager


class TestOutputManager:
    @pytest.fixture(autouse=True)
    def reset_path_manager_state(self):
        """
        Reset PathManager state before and after each test.

        This test class tests output_manager behavior with different environment
        configurations, so we need to reset PathManager directly to allow
        tests to set up their own environment.
        """
        # Save original state
        old_instance = PathManager._instance
        old_initialized = PathManager._initialized

        # Reset before test
        PathManager._instance = None
        PathManager._initialized = False

        yield

        # Reset after test
        PathManager._instance = old_instance
        PathManager._initialized = old_initialized

    def test_get_output_dir_with_hagent_output_dir(self, monkeypatch):
        """Test that HAGENT_OUTPUT_DIR takes priority."""
        # Clear other environment variables
        monkeypatch.delenv('HAGENT_OUTPUT_DIR', raising=False)
        monkeypatch.delenv('HAGENT_CACHE_DIR', raising=False)
        monkeypatch.delenv('HAGENT_REPO_DIR', raising=False)
        monkeypatch.delenv('HAGENT_BUILD_DIR', raising=False)

        with tempfile.TemporaryDirectory() as temp_base:
            test_dir = os.path.join(temp_base, 'custom_output_dir_test')
            monkeypatch.setenv('HAGENT_OUTPUT_DIR', test_dir)

            result = get_output_dir()
            assert result == str(Path(test_dir).resolve())
            assert Path(test_dir).exists()

    def test_get_output_dir_default(self, monkeypatch):
        """Test default fallback to 'output' directory."""
        # Clear all relevant environment variables to trigger fallback behavior
        monkeypatch.delenv('HAGENT_OUTPUT_DIR', raising=False)
        monkeypatch.delenv('HAGENT_CACHE_DIR', raising=False)
        monkeypatch.delenv('HAGENT_REPO_DIR', raising=False)
        monkeypatch.delenv('HAGENT_BUILD_DIR', raising=False)

        result = get_output_dir()
        expected = str(Path.cwd() / 'output')
        assert result == expected

    def test_get_output_dir_creates_directory(self, monkeypatch):
        """Test that output directory is created automatically."""
        # Clear all environment variables
        monkeypatch.delenv('HAGENT_OUTPUT_DIR', raising=False)
        monkeypatch.delenv('HAGENT_CACHE_DIR', raising=False)
        monkeypatch.delenv('HAGENT_REPO_DIR', raising=False)
        monkeypatch.delenv('HAGENT_BUILD_DIR', raising=False)

        with tempfile.TemporaryDirectory() as temp_dir:
            test_output = os.path.join(temp_dir, 'new_output_dir')
            monkeypatch.setenv('HAGENT_OUTPUT_DIR', test_output)

            assert not Path(test_output).exists()

            result = get_output_dir()
            assert result == str(Path(test_output).resolve())
            assert Path(test_output).exists()

    def test_get_output_path_valid_filename(self, monkeypatch):
        """Test get_output_path with simple filename."""
        # Clear all relevant environment variables to test default behavior
        monkeypatch.delenv('HAGENT_OUTPUT_DIR', raising=False)
        monkeypatch.delenv('HAGENT_CACHE_DIR', raising=False)
        monkeypatch.delenv('HAGENT_REPO_DIR', raising=False)
        monkeypatch.delenv('HAGENT_BUILD_DIR', raising=False)

        result = get_output_path('test.txt')
        expected = str(Path.cwd() / 'output' / 'test.txt')
        assert result == expected

    def test_get_output_path_valid_relative_path(self, monkeypatch):
        """Test get_output_path with relative path."""
        # Clear all relevant environment variables to test default behavior
        monkeypatch.delenv('HAGENT_OUTPUT_DIR', raising=False)
        monkeypatch.delenv('HAGENT_CACHE_DIR', raising=False)
        monkeypatch.delenv('HAGENT_REPO_DIR', raising=False)
        monkeypatch.delenv('HAGENT_BUILD_DIR', raising=False)

        result = get_output_path('subdir/test.txt')
        expected = str(Path.cwd() / 'output' / 'subdir' / 'test.txt')
        assert result == expected

    def test_get_output_path_with_hagent_output_dir(self, monkeypatch):
        """Test get_output_path with HAGENT_OUTPUT_DIR."""
        # Clear other environment variables
        monkeypatch.delenv('HAGENT_OUTPUT_DIR', raising=False)
        monkeypatch.delenv('HAGENT_CACHE_DIR', raising=False)
        monkeypatch.delenv('HAGENT_REPO_DIR', raising=False)
        monkeypatch.delenv('HAGENT_BUILD_DIR', raising=False)
        monkeypatch.delenv('HAGENT_DOCKER', raising=False)

        with tempfile.TemporaryDirectory() as temp_base:
            test_dir = os.path.join(temp_base, 'custom_output_dir')
            monkeypatch.setenv('HAGENT_OUTPUT_DIR', test_dir)

            result = get_output_path('test.txt')
            expected = str(Path(test_dir, 'test.txt').resolve())
            assert result == expected

    def test_get_output_path_absolute_unix_path_fails(self):
        with pytest.raises(SystemExit) as excinfo:
            get_output_path('/tmp/test.txt')
        assert excinfo.value.code == 1

    def test_get_output_path_absolute_windows_path_fails(self):
        with pytest.raises(SystemExit) as excinfo:
            get_output_path('C:\\temp\\test.txt')
        assert excinfo.value.code == 1

    def test_get_output_path_home_directory_path_fails(self):
        with pytest.raises(SystemExit) as excinfo:
            get_output_path('~/test.txt')
        assert excinfo.value.code == 1

    def test_get_output_path_parent_directory_escape_fails(self):
        with pytest.raises(SystemExit) as excinfo:
            get_output_path('../test.txt')
        assert excinfo.value.code == 1

    def test_get_output_path_just_parent_directory_fails(self):
        with pytest.raises(SystemExit) as excinfo:
            get_output_path('..')
        assert excinfo.value.code == 1

    def test_get_output_path_current_directory_reference(self, monkeypatch):
        # Clear environment variables
        monkeypatch.delenv('HAGENT_OUTPUT_DIR', raising=False)
        monkeypatch.delenv('HAGENT_CACHE_DIR', raising=False)
        monkeypatch.delenv('HAGENT_REPO_DIR', raising=False)
        monkeypatch.delenv('HAGENT_BUILD_DIR', raising=False)

        result = get_output_path('./test.txt')
        expected = str((Path.cwd() / 'output' / '.' / 'test.txt').resolve())
        assert result == expected

    @patch('sys.stderr')
    def test_invalid_path_error_message_content(self, mock_stderr):
        with pytest.raises(SystemExit):
            get_output_path('/tmp/test.txt')

        calls = mock_stderr.write.call_args_list
        error_output = ''.join([call[0][0] for call in calls])

        assert "ERROR: get_output_path() called with invalid path: '/tmp/test.txt'" in error_output
        assert 'API CONSTRAINT VIOLATION:' in error_output
        assert 'get_output_path() only accepts relative paths within the output directory' in error_output
        assert "get_output_path('my_file.log')" in error_output
        assert "get_output_path('subdir/my_file.txt')" in error_output
        assert "get_output_path('../escape/file.txt')    # ✗ escapes output directory" in error_output

    @patch('sys.stderr')
    def test_parent_directory_error_message_content(self, mock_stderr):
        with pytest.raises(SystemExit):
            get_output_path('../escape.txt')

        calls = mock_stderr.write.call_args_list
        error_output = ''.join([call[0][0] for call in calls])

        assert "ERROR: get_output_path() called with invalid path: '../escape.txt'" in error_output
        assert "get_output_path('..')                    # ✗ parent directory reference" in error_output
