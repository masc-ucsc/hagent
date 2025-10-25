#!/usr/bin/env python3

import os
import sys
import tempfile
from pathlib import Path
from unittest.mock import patch
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..'))
from hagent.inou.output_manager import get_output_dir, get_output_path


class TestOutputManager:
    def setup_method(self):
        self.original_output_dir = os.environ.get('HAGENT_OUTPUT_DIR')
        self.original_docker = os.environ.get('HAGENT_DOCKER')

    def teardown_method(self):
        # Restore HAGENT_OUTPUT_DIR
        if self.original_output_dir is not None:
            os.environ['HAGENT_OUTPUT_DIR'] = self.original_output_dir
        elif 'HAGENT_OUTPUT_DIR' in os.environ:
            del os.environ['HAGENT_OUTPUT_DIR']

        # Restore HAGENT_DOCKER
        if self.original_docker is not None:
            os.environ['HAGENT_DOCKER'] = self.original_docker
        elif 'HAGENT_DOCKER' in os.environ:
            del os.environ['HAGENT_DOCKER']

    def test_get_output_dir_with_hagent_output_dir(self):
        """Test that HAGENT_OUTPUT_DIR takes priority."""
        # Clear other environment variables
        for var in ['HAGENT_OUTPUT_DIR']:
            if var in os.environ:
                del os.environ[var]

        with tempfile.TemporaryDirectory() as temp_base:
            test_dir = os.path.join(temp_base, 'custom_output_dir_test')
            os.environ['HAGENT_OUTPUT_DIR'] = test_dir

            result = get_output_dir()
            assert result == str(Path(test_dir).resolve())
            assert Path(test_dir).exists()

    def test_get_output_dir_default(self):
        """Test default fallback to 'output' directory."""
        # Clear all relevant environment variables
        for var in ['HAGENT_OUTPUT_DIR']:
            if var in os.environ:
                del os.environ[var]

        result = get_output_dir()
        expected = str(Path.cwd() / 'output')
        assert result == expected

    def test_get_output_dir_creates_directory(self):
        """Test that output directory is created automatically."""
        # Clear all environment variables
        for var in ['HAGENT_OUTPUT_DIR']:
            if var in os.environ:
                del os.environ[var]

        with tempfile.TemporaryDirectory() as temp_dir:
            test_output = os.path.join(temp_dir, 'new_output_dir')
            os.environ['HAGENT_OUTPUT_DIR'] = test_output

            assert not Path(test_output).exists()

            result = get_output_dir()
            assert result == str(Path(test_output).resolve())
            assert Path(test_output).exists()

    def test_get_output_path_valid_filename(self):
        """Test get_output_path with simple filename."""
        # Clear all relevant environment variables to test default behavior
        for var in ['HAGENT_OUTPUT_DIR']:
            if var in os.environ:
                del os.environ[var]

        result = get_output_path('test.txt')
        expected = str(Path.cwd() / 'output' / 'test.txt')
        assert result == expected

    def test_get_output_path_valid_relative_path(self):
        """Test get_output_path with relative path."""
        # Clear all relevant environment variables to test default behavior
        for var in ['HAGENT_OUTPUT_DIR']:
            if var in os.environ:
                del os.environ[var]

        result = get_output_path('subdir/test.txt')
        expected = str(Path.cwd() / 'output' / 'subdir' / 'test.txt')
        assert result == expected

    def test_get_output_path_with_hagent_output_dir(self):
        """Test get_output_path with HAGENT_OUTPUT_DIR."""
        # Clear other environment variables
        for var in ['HAGENT_DOCKER']:
            if var in os.environ:
                del os.environ[var]

        with tempfile.TemporaryDirectory() as temp_base:
            test_dir = os.path.join(temp_base, 'custom_output_dir')
            os.environ['HAGENT_OUTPUT_DIR'] = test_dir

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

    def test_get_output_path_current_directory_reference(self):
        # Clear environment variables
        for var in ['HAGENT_OUTPUT_DIR']:
            if var in os.environ:
                del os.environ[var]

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
