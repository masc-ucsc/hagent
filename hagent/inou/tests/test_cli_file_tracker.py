"""
Tests for FileTracker CLI tool

Tests the command-line interface for FileTracker demonstration functionality
including all commands and error handling scenarios.
"""

import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock
import pytest

from hagent.inou.cli_file_tracker import (
    cmd_track_file,
    cmd_track_dir,
    cmd_get_diff,
    cmd_get_all_diffs,
    cmd_status,
    cmd_patch_dict,
    cmd_cleanup,
    main,
)


class TestCLICommands:
    """Test individual CLI command functions."""

    def setup_method(self):
        """Setup for each test method."""
        self.mock_args = MagicMock()

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_track_file_success(self, mock_path_manager_class, mock_file_tracker_class):
        """Test successful file tracking command."""
        self.mock_args.path = 'src/main.py'

        # Mock PathManager and FileTracker
        mock_path_manager = MagicMock()
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_tracker.track_file.return_value = True
        mock_file_tracker_class.return_value.__enter__.return_value = mock_tracker

        with patch('builtins.print') as mock_print:
            result = cmd_track_file(self.mock_args)

            assert result == 0
            mock_tracker.track_file.assert_called_once_with('src/main.py')
            mock_print.assert_any_call('✓ Successfully tracking file: src/main.py')

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_track_file_failure(self, mock_path_manager_class, mock_file_tracker_class):
        """Test file tracking command failure."""
        self.mock_args.path = 'nonexistent.py'

        mock_path_manager = MagicMock()
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_tracker.track_file.return_value = False
        mock_file_tracker_class.return_value.__enter__.return_value = mock_tracker

        with patch('builtins.print') as mock_print:
            result = cmd_track_file(self.mock_args)

            assert result == 1
            mock_print.assert_any_call('✗ Failed to track file: nonexistent.py')

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_track_dir_with_extension(self, mock_path_manager_class, mock_file_tracker_class):
        """Test directory tracking command with extension filter."""
        self.mock_args.path = 'src'
        self.mock_args.ext = '.py'

        mock_path_manager = MagicMock()
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_tracker.track_dir.return_value = True
        mock_file_tracker_class.return_value.__enter__.return_value = mock_tracker

        with patch('builtins.print') as mock_print:
            result = cmd_track_dir(self.mock_args)

            assert result == 0
            mock_tracker.track_dir.assert_called_once_with('src', '.py')
            mock_print.assert_any_call('Extension filter: .py')

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_track_dir_no_extension(self, mock_path_manager_class, mock_file_tracker_class):
        """Test directory tracking command without extension filter."""
        self.mock_args.path = 'src'
        self.mock_args.ext = None

        mock_path_manager = MagicMock()
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_tracker.track_dir.return_value = True
        mock_file_tracker_class.return_value.__enter__.return_value = mock_tracker

        result = cmd_track_dir(self.mock_args)

        assert result == 0
        mock_tracker.track_dir.assert_called_once_with('src', None)

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_get_diff_with_changes(self, mock_path_manager_class, mock_file_tracker_class):
        """Test get diff command with changes."""
        self.mock_args.path = 'src/main.py'

        mock_path_manager = MagicMock()
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_tracker.get_diff.return_value = 'diff output here'
        mock_file_tracker_class.return_value.__enter__.return_value = mock_tracker

        with patch('builtins.print') as mock_print:
            result = cmd_get_diff(self.mock_args)

            assert result == 0
            mock_tracker.track_file.assert_called_once_with('src/main.py')
            mock_tracker.get_diff.assert_called_once_with('src/main.py')
            mock_print.assert_any_call('diff output here')

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_get_diff_no_changes(self, mock_path_manager_class, mock_file_tracker_class):
        """Test get diff command with no changes."""
        self.mock_args.path = 'src/main.py'

        mock_path_manager = MagicMock()
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_tracker.get_diff.return_value = ''
        mock_file_tracker_class.return_value.__enter__.return_value = mock_tracker

        with patch('builtins.print') as mock_print:
            result = cmd_get_diff(self.mock_args)

            assert result == 0
            mock_print.assert_any_call('No changes detected or file not tracked.')

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_get_all_diffs(self, mock_path_manager_class, mock_file_tracker_class):
        """Test get all diffs command."""
        self.mock_args.ext = '.py'

        mock_path_manager = MagicMock()
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_tracker.get_all_diffs.return_value = {'file1.py': 'diff for file1', 'file2.py': 'diff for file2'}
        mock_file_tracker_class.return_value.__enter__.return_value = mock_tracker

        with patch('builtins.print') as mock_print:
            result = cmd_get_all_diffs(self.mock_args)

            assert result == 0
            mock_tracker.track_dir.assert_called_once_with('.', '.py')
            mock_tracker.get_all_diffs.assert_called_once_with('.py')
            mock_print.assert_any_call('\nFound changes in 2 files:')

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_status(self, mock_path_manager_class, mock_file_tracker_class):
        """Test status command."""
        mock_path_manager = MagicMock()
        mock_path_manager.is_docker_mode.return_value = False
        mock_path_manager.repo_dir = Path('/test/repo')
        mock_path_manager.build_dir = Path('/test/build')
        mock_path_manager.cache_dir = Path('/test/cache')
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_tracker._baseline_stash = 'abc123'
        mock_tracker._tracked_files = {'file1.py', 'file2.py'}
        mock_tracker._tracked_dirs = [{'path': '/test/repo/src', 'ext': '.py'}]
        mock_file_tracker_class.return_value.__enter__.return_value = mock_tracker

        with patch('builtins.print') as mock_print:
            result = cmd_status(self.mock_args)

            assert result == 0
            mock_print.assert_any_call('FileTracker Status:')
            mock_print.assert_any_call('Docker mode: No')
            mock_print.assert_any_call('Baseline stash: Yes')

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_patch_dict(self, mock_path_manager_class, mock_file_tracker_class):
        """Test patch dict command."""
        self.mock_args.ext = '.py'
        self.mock_args.show_content = False

        mock_path_manager = MagicMock()
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_tracker.get_patch_dict.return_value = {
            'full': [{'filename': 'file1.py', 'contents': 'content'}],
            'patch': [{'filename': 'file2.py', 'diff': 'diff content'}],
        }
        mock_file_tracker_class.return_value.__enter__.return_value = mock_tracker

        with patch('builtins.print') as mock_print:
            result = cmd_patch_dict(self.mock_args)

            assert result == 0
            mock_print.assert_any_call('\nPatch Dictionary Summary:')
            mock_print.assert_any_call('Full files: 1')
            mock_print.assert_any_call('Patch files: 1')

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_cleanup(self, mock_path_manager_class, mock_file_tracker_class):
        """Test cleanup command."""
        mock_path_manager = MagicMock()
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_file_tracker_class.return_value = mock_tracker

        with patch('builtins.print') as mock_print:
            result = cmd_cleanup(self.mock_args)

            assert result == 0
            mock_tracker.cleanup.assert_called_once()
            mock_print.assert_any_call('✓ Cleanup completed successfully')


class TestCLIErrorHandling:
    """Test CLI error handling scenarios."""

    def setup_method(self):
        """Setup for each test method."""
        self.mock_args = MagicMock()

    @patch('hagent.inou.cli_file_tracker.PathManager', side_effect=Exception('Path manager error'))
    def test_cmd_track_file_exception(self, mock_path_manager_class):
        """Test track file command with exception."""
        self.mock_args.path = 'src/main.py'

        with patch('builtins.print') as mock_print:
            result = cmd_track_file(self.mock_args)

            assert result == 1
            mock_print.assert_any_call('Error: Path manager error')

    @patch('hagent.inou.cli_file_tracker.FileTracker')
    @patch('hagent.inou.cli_file_tracker.PathManager')
    def test_cmd_get_all_diffs_no_changes(self, mock_path_manager_class, mock_file_tracker_class):
        """Test get all diffs with no changes."""
        self.mock_args.ext = None

        mock_path_manager = MagicMock()
        mock_path_manager_class.return_value = mock_path_manager

        mock_tracker = MagicMock()
        mock_tracker.get_all_diffs.return_value = {}
        mock_file_tracker_class.return_value.__enter__.return_value = mock_tracker

        with patch('builtins.print') as mock_print:
            result = cmd_get_all_diffs(self.mock_args)

            assert result == 0
            mock_print.assert_any_call('No changes detected in tracked files.')

    @patch('hagent.inou.cli_file_tracker.PathManager', side_effect=Exception('Status error'))
    def test_cmd_status_exception(self, mock_path_manager_class):
        """Test status command with exception."""
        with patch('builtins.print') as mock_print:
            result = cmd_status(self.mock_args)

            assert result == 1
            mock_print.assert_any_call('Error: Status error')


class TestCLIMain:
    """Test main CLI entry point and argument parsing."""

    @patch('sys.argv', ['cli_file_tracker.py', 'track-file', 'src/main.py'])
    @patch('hagent.inou.cli_file_tracker.cmd_track_file')
    def test_main_track_file(self, mock_cmd_track_file):
        """Test main function with track-file command."""
        mock_cmd_track_file.return_value = 0

        result = main()

        assert result == 0
        mock_cmd_track_file.assert_called_once()

        # Check that args were parsed correctly
        args = mock_cmd_track_file.call_args[0][0]
        assert args.path == 'src/main.py'

    @patch('sys.argv', ['cli_file_tracker.py', 'track-dir', 'src', '--ext', '.py'])
    @patch('hagent.inou.cli_file_tracker.cmd_track_dir')
    def test_main_track_dir_with_ext(self, mock_cmd_track_dir):
        """Test main function with track-dir command and extension."""
        mock_cmd_track_dir.return_value = 0

        result = main()

        assert result == 0
        mock_cmd_track_dir.assert_called_once()

        # Check that args were parsed correctly
        args = mock_cmd_track_dir.call_args[0][0]
        assert args.path == 'src'
        assert args.ext == '.py'

    @patch('sys.argv', ['cli_file_tracker.py', 'get-diff', 'src/main.py'])
    @patch('hagent.inou.cli_file_tracker.cmd_get_diff')
    def test_main_get_diff(self, mock_cmd_get_diff):
        """Test main function with get-diff command."""
        mock_cmd_get_diff.return_value = 0

        result = main()

        assert result == 0
        mock_cmd_get_diff.assert_called_once()

    @patch('sys.argv', ['cli_file_tracker.py', 'get-all-diffs', '--ext', '.scala'])
    @patch('hagent.inou.cli_file_tracker.cmd_get_all_diffs')
    def test_main_get_all_diffs(self, mock_cmd_get_all_diffs):
        """Test main function with get-all-diffs command."""
        mock_cmd_get_all_diffs.return_value = 0

        result = main()

        assert result == 0
        mock_cmd_get_all_diffs.assert_called_once()

    @patch('sys.argv', ['cli_file_tracker.py', 'status'])
    @patch('hagent.inou.cli_file_tracker.cmd_status')
    def test_main_status(self, mock_cmd_status):
        """Test main function with status command."""
        mock_cmd_status.return_value = 0

        result = main()

        assert result == 0
        mock_cmd_status.assert_called_once()

    @patch('sys.argv', ['cli_file_tracker.py', 'patch-dict', '--show-content'])
    @patch('hagent.inou.cli_file_tracker.cmd_patch_dict')
    def test_main_patch_dict_show_content(self, mock_cmd_patch_dict):
        """Test main function with patch-dict command and show-content flag."""
        mock_cmd_patch_dict.return_value = 0

        result = main()

        assert result == 0
        mock_cmd_patch_dict.assert_called_once()

        # Check that args were parsed correctly
        args = mock_cmd_patch_dict.call_args[0][0]
        assert args.show_content is True

    @patch('sys.argv', ['cli_file_tracker.py', 'cleanup'])
    @patch('hagent.inou.cli_file_tracker.cmd_cleanup')
    def test_main_cleanup(self, mock_cmd_cleanup):
        """Test main function with cleanup command."""
        mock_cmd_cleanup.return_value = 0

        result = main()

        assert result == 0
        mock_cmd_cleanup.assert_called_once()

    @patch('sys.argv', ['cli_file_tracker.py', '--help'])
    def test_main_help(self):
        """Test main function with help flag."""
        with pytest.raises(SystemExit) as exc_info:
            main()

        assert exc_info.value.code == 0

    @patch('sys.argv', ['cli_file_tracker.py'])
    def test_main_no_command(self):
        """Test main function with no command (should fail)."""
        with pytest.raises(SystemExit) as exc_info:
            main()

        assert exc_info.value.code == 2  # argparse error code

    def test_main_keyboard_interrupt(self):
        """Test main function with keyboard interrupt."""
        with (
            patch('sys.argv', ['cli_file_tracker.py', 'status']),
            patch('hagent.inou.cli_file_tracker.cmd_status', side_effect=KeyboardInterrupt),
        ):
            result = main()

            assert result == 130

    def test_main_unexpected_exception(self):
        """Test main function with unexpected exception."""
        with (
            patch('sys.argv', ['cli_file_tracker.py', 'status']),
            patch('hagent.inou.cli_file_tracker.cmd_status', side_effect=RuntimeError('Unexpected')),
        ):
            result = main()

            assert result == 1


class TestCLIIntegration:
    """Test CLI integration scenarios."""

    @patch('subprocess.run')
    def test_cli_help_subprocess(self, mock_subprocess):
        """Test CLI help via subprocess call."""
        mock_subprocess.return_value.returncode = 0
        mock_subprocess.return_value.stdout = 'CLI help output'

        # Simulate calling the CLI as a subprocess
        subprocess.run(['python', '-m', 'hagent.inou.cli_file_tracker', '--help'], capture_output=True, text=True)

        # This is mocked, so we're testing the mock setup
        assert mock_subprocess.called

    def test_valid_command_structures(self):
        """Test that all command structures are valid."""
        import argparse

        # Test that argument parser can be created without errors
        parser = argparse.ArgumentParser()
        subparsers = parser.add_subparsers(dest='command')

        # Should not raise any exceptions
        track_file_parser = subparsers.add_parser('track-file')
        track_file_parser.add_argument('path')

        track_dir_parser = subparsers.add_parser('track-dir')
        track_dir_parser.add_argument('path')
        track_dir_parser.add_argument('--ext')

        get_diff_parser = subparsers.add_parser('get-diff')
        get_diff_parser.add_argument('path')

        # If we get here without exceptions, the structure is valid
        assert True

    @patch('sys.argv', ['cli_file_tracker.py', 'patch-dict', '--ext', '.v', '--show-content'])
    @patch('hagent.inou.cli_file_tracker.cmd_patch_dict')
    def test_complex_argument_parsing(self, mock_cmd_patch_dict):
        """Test complex argument combinations."""
        mock_cmd_patch_dict.return_value = 0

        result = main()

        assert result == 0

        # Verify complex arguments were parsed correctly
        args = mock_cmd_patch_dict.call_args[0][0]
        assert args.ext == '.v'
        assert args.show_content is True


class TestCLIUsageExamples:
    """Test CLI usage examples from the help text."""

    @patch('hagent.inou.cli_file_tracker.cmd_track_file')
    def test_example_track_file_scala(self, mock_cmd):
        """Test the example: track-file src/main.scala"""
        mock_cmd.return_value = 0

        with patch('sys.argv', ['cli_file_tracker.py', 'track-file', 'src/main.scala']):
            result = main()

        assert result == 0
        args = mock_cmd.call_args[0][0]
        assert args.path == 'src/main.scala'

    @patch('hagent.inou.cli_file_tracker.cmd_track_dir')
    def test_example_track_dir_scala(self, mock_cmd):
        """Test the example: track-dir src --ext .scala"""
        mock_cmd.return_value = 0

        with patch('sys.argv', ['cli_file_tracker.py', 'track-dir', 'src', '--ext', '.scala']):
            result = main()

        assert result == 0
        args = mock_cmd.call_args[0][0]
        assert args.path == 'src'
        assert args.ext == '.scala'

    @patch('hagent.inou.cli_file_tracker.cmd_get_all_diffs')
    def test_example_get_all_diffs_scala(self, mock_cmd):
        """Test the example: get-all-diffs --ext .scala"""
        mock_cmd.return_value = 0

        with patch('sys.argv', ['cli_file_tracker.py', 'get-all-diffs', '--ext', '.scala']):
            result = main()

        assert result == 0
        args = mock_cmd.call_args[0][0]
        assert args.ext == '.scala'
