#!/usr/bin/env python3

import os
import sys
import tempfile
import shutil
from pathlib import Path
from unittest.mock import patch
import pytest

sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..', '..', '..'))
from hagent.core.output_manager import get_output_dir, get_output_path


class TestOutputManager:
    def setup_method(self):
        self.original_env = os.environ.get('HAGENT_OUTPUT')

    def teardown_method(self):
        if self.original_env is not None:
            os.environ['HAGENT_OUTPUT'] = self.original_env
        elif 'HAGENT_OUTPUT' in os.environ:
            del os.environ['HAGENT_OUTPUT']

    def test_get_output_dir_default(self):
        if 'HAGENT_OUTPUT' in os.environ:
            del os.environ['HAGENT_OUTPUT']

        result = get_output_dir()
        assert result == 'output'

    def test_get_output_dir_env_variable(self):
        test_dir = 'custom_output_test'
        os.environ['HAGENT_OUTPUT'] = test_dir

        try:
            result = get_output_dir()
            assert result == test_dir
            assert Path(test_dir).exists()
        finally:
            if Path(test_dir).exists():
                shutil.rmtree(test_dir)

    def test_get_output_dir_creates_directory(self):
        with tempfile.TemporaryDirectory() as temp_dir:
            test_output = os.path.join(temp_dir, 'new_output_dir')
            os.environ['HAGENT_OUTPUT'] = test_output

            assert not Path(test_output).exists()

            result = get_output_dir()
            assert result == test_output
            assert Path(test_output).exists()

    def test_get_output_path_valid_filename(self):
        if 'HAGENT_OUTPUT' in os.environ:
            del os.environ['HAGENT_OUTPUT']

        result = get_output_path('test.txt')
        expected = os.path.join('output', 'test.txt')
        assert result == expected

    def test_get_output_path_valid_relative_path(self):
        if 'HAGENT_OUTPUT' in os.environ:
            del os.environ['HAGENT_OUTPUT']

        result = get_output_path('subdir/test.txt')
        expected = os.path.join('output', 'subdir', 'test.txt')
        assert result == expected

    def test_get_output_path_with_custom_output_dir(self):
        os.environ['HAGENT_OUTPUT'] = 'custom_dir'

        try:
            result = get_output_path('test.txt')
            expected = os.path.join('custom_dir', 'test.txt')
            assert result == expected
        finally:
            if Path('custom_dir').exists():
                shutil.rmtree('custom_dir')

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
        if 'HAGENT_OUTPUT' in os.environ:
            del os.environ['HAGENT_OUTPUT']

        result = get_output_path('./test.txt')
        expected = os.path.join('output', '.', 'test.txt')
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
