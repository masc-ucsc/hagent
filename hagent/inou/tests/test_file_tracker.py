"""
Tests for FileTracker

Tests git-based file tracking with stash snapshots, comprehensive tracking
functionality, and diff generation for both local and Docker execution modes.
"""

import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock
import pytest

from hagent.inou.file_tracker_local import FileTrackerLocal as FileTracker
from hagent.inou.path_manager import PathManager


@pytest.fixture(autouse=True)
def reset_docker_state():
    """Reset global Docker state and use PathManager.configured() for test isolation."""
    import hagent.inou.container_manager as cm
    import os

    # Store original environment
    original_env = {}
    hagent_vars = [k for k in os.environ.keys() if k.startswith('HAGENT_')]
    for key in hagent_vars:
        original_env[key] = os.environ[key]

    # Reset global state
    cm._docker_workspace_validated = False

    # Use PathManager.configured() for test isolation
    # Since these tests are mocked, we use local mode with temp paths
    with PathManager.configured():
        yield

    # Restore environment variables
    current_hagent_vars = [k for k in os.environ.keys() if k.startswith('HAGENT_')]
    for key in current_hagent_vars:
        if key not in original_env:
            del os.environ[key]
    for key, value in original_env.items():
        os.environ[key] = value

    # Reset global state again
    cm._docker_workspace_validated = False


class TestFileTrackerInitialization:
    """Test FileTracker initialization and validation."""

    @patch('hagent.inou.file_tracker_local.subprocess.run')
    @patch('pathlib.Path.exists')
    def test_successful_initialization(self, mock_exists, mock_subprocess):
        """Test successful FileTracker initialization."""

        # Mock git repository validation - directory and .git exist
        def mock_exists_func():
            return True  # Both repo dir and .git dir exist

        mock_exists.side_effect = mock_exists_func

        # Mock git commands
        mock_subprocess.side_effect = [
            MagicMock(returncode=0, stdout='/test/repo/.git'),  # git rev-parse
            MagicMock(returncode=0, stdout='git version 2.34.1'),  # git --version
            MagicMock(returncode=1, stdout=''),  # git diff-index (changes exist)
        ]

        with patch.object(FileTracker, '_create_baseline_snapshot', return_value='abc123'):
            tracker = FileTracker()

            assert tracker.path_manager is not None
            assert tracker._baseline_stash == 'abc123'
            assert len(tracker._tracked_files) == 0
            assert len(tracker._tracked_dirs) == 0

    @patch('hagent.inou.file_tracker_local.sys.exit')
    @patch('pathlib.Path.exists', return_value=False)
    def test_repo_dir_not_exists(self, mock_exists, mock_exit):
        """Test failure when repo directory doesn't exist."""
        FileTracker()

        mock_exit.assert_called_once_with(1)

    @patch('hagent.inou.file_tracker_local.sys.exit')
    @patch('pathlib.Path.exists')
    def test_not_git_repo(self, mock_exists, mock_exit):
        """Test failure when directory is not a git repository."""
        # Repo exists but .git doesn't
        mock_exists.side_effect = lambda: str(self) == '/test/repo'

        FileTracker()

        mock_exit.assert_called_once_with(1)

    @patch('hagent.inou.file_tracker_local.sys.exit')
    @patch('hagent.inou.file_tracker_local.subprocess.run')
    @patch('pathlib.Path.exists', return_value=True)
    def test_git_command_not_available(self, mock_exists, mock_subprocess, mock_exit):
        """Test failure when git command is not available."""
        # Git repository validation fails
        mock_subprocess.side_effect = [
            MagicMock(returncode=1, stderr='git command not found'),
            subprocess.CalledProcessError(1, 'git'),
        ]

        FileTracker()

        mock_exit.assert_called_once_with(1)


class TestSnapshotManagement:
    """Test git stash snapshot management."""

    @patch('hagent.inou.file_tracker_local.subprocess.run')
    def test_create_baseline_snapshot_with_changes(self, mock_subprocess):
        """Test baseline snapshot creation when changes exist."""
        with (
            patch.object(FileTracker, '_ensure_git_repo', return_value=True),
            patch.object(FileTracker, '_check_git_available', return_value=True),
        ):
            # Mock git commands for baseline snapshot creation
            mock_subprocess.side_effect = [
                MagicMock(returncode=1, stdout=''),  # diff-index (tracked changes exist)
                MagicMock(returncode=0, stdout=''),  # diff-index --cached (staged changes)
                MagicMock(returncode=0, stdout=''),  # ls-files --others (untracked files)
                MagicMock(returncode=0, stdout='abc123\n'),  # stash create
                MagicMock(returncode=0, stdout=''),  # stash store
            ]

            tracker = FileTracker()

            assert tracker._baseline_stash == 'abc123'
            assert 'abc123' in tracker._hagent_stashes

    @patch('hagent.inou.file_tracker_local.subprocess.run')
    def test_create_baseline_snapshot_no_changes(self, mock_subprocess):
        """Test baseline snapshot when no changes exist."""
        with (
            patch.object(FileTracker, '_ensure_git_repo', return_value=True),
            patch.object(FileTracker, '_check_git_available', return_value=True),
        ):
            # Mock git diff-index returning 0 (no changes)
            mock_subprocess.return_value = MagicMock(returncode=0, stdout='')

            tracker = FileTracker()

            assert tracker._baseline_stash is None
            assert len(tracker._hagent_stashes) == 0

    @patch('hagent.inou.file_tracker_local.subprocess.run')
    def test_create_snapshot(self, mock_subprocess):
        """Test creating a snapshot."""
        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            tracker = FileTracker()
            tracker.path_manager = PathManager()
            tracker.logger = MagicMock()

            # Mock successful stash creation
            mock_subprocess.return_value = MagicMock(returncode=0, stdout='def456\n')

            result = tracker._create_snapshot('test-message')

            assert result == 'def456'
            mock_subprocess.assert_called_once()

    @patch('hagent.inou.file_tracker_local.subprocess.run')
    def test_store_snapshot(self, mock_subprocess):
        """Test storing a snapshot."""
        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            tracker = FileTracker()
            tracker.path_manager = PathManager()
            tracker.logger = MagicMock()
            tracker._hagent_stashes = []

            # Mock successful stash store
            mock_subprocess.return_value = MagicMock(returncode=0)

            result = tracker._store_snapshot('def456', 'test-message')

            assert result is True
            assert 'def456' in tracker._hagent_stashes

    @patch('hagent.inou.file_tracker_local.subprocess.run')
    def test_cleanup_snapshots(self, mock_subprocess):
        """Test cleanup of snapshots."""
        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            tracker = FileTracker()
            tracker.path_manager = PathManager()
            tracker.logger = MagicMock()
            tracker._hagent_stashes = ['abc123', 'def456']

            # Mock stash list and drop
            mock_subprocess.side_effect = [
                MagicMock(returncode=0, stdout='abc123 stash@{0}\ndef456 stash@{1}\n'),  # stash list
                MagicMock(returncode=0),  # stash drop
                MagicMock(returncode=0, stdout='def456 stash@{0}\n'),  # stash list again
                MagicMock(returncode=0),  # stash drop
            ]

            tracker._cleanup_snapshots()

            assert len(tracker._hagent_stashes) == 0


class TestFileDirectoryTracking:
    """Test file and directory tracking functionality."""

    def setup_method(self):
        """Setup for each test method."""
        # Create tracker with mocked initialization
        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            self.tracker = FileTracker()
            self.tracker.path_manager = PathManager()
            self.tracker.logger = MagicMock()
            self.tracker._tracked_files = set()
            self.tracker._tracked_dirs = []

    def test_track_file_success(self):
        """Test successful file tracking."""
        with patch('pathlib.Path.exists', return_value=True):
            result = self.tracker.track_file('src/main.py')

            assert result is True
            assert len(self.tracker._tracked_files) == 1
            tracked_path = next(iter(self.tracker._tracked_files))
            assert 'src/main.py' in tracked_path

    def test_track_file_absolute_path(self):
        """Test tracking file with absolute path."""
        with patch('pathlib.Path.exists', return_value=True):
            result = self.tracker.track_file('/absolute/path/file.py')

            assert result is True
            assert '/absolute/path/file.py' in self.tracker._tracked_files

    def test_track_dir_success(self):
        """Test successful directory tracking."""
        with patch('pathlib.Path.exists', return_value=True):
            result = self.tracker.track_dir('src', '.py')

            assert result is True
            assert len(self.tracker._tracked_dirs) == 1
            assert self.tracker._tracked_dirs[0]['ext'] == '.py'

    def test_track_dir_no_extension(self):
        """Test directory tracking without extension filter."""
        with patch('pathlib.Path.exists', return_value=True):
            result = self.tracker.track_dir('src')

            assert result is True
            assert len(self.tracker._tracked_dirs) == 1
            assert self.tracker._tracked_dirs[0]['ext'] is None

    def test_get_tracked_files_empty(self):
        """Test getting tracked files when none are tracked."""
        result = self.tracker.get_tracked_files()

        assert isinstance(result, set)
        assert len(result) == 0

    def test_get_tracked_files_with_directory(self):
        """Test getting tracked files from directory tracking."""
        # Setup directory tracking
        self.tracker._tracked_dirs = [{'path': '/test/repo/src', 'ext': '.py'}]

        # Mock the helper methods directly
        with patch.object(self.tracker, '_find_files_in_dir', return_value=['/test/repo/src/main.py']):
            with patch('pathlib.Path.exists', return_value=True):
                result = self.tracker.get_tracked_files('.py')

                assert len(result) == 1  # Only .py file should match
                assert '/test/repo/src/main.py' in result


class TestUnifiedGitTracking:
    """Test unified git-based tracking (replaces build directory tracking)."""

    def setup_method(self):
        """Setup for each test method."""
        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            self.tracker = FileTracker()
            self.tracker.path_manager = PathManager()
            self.tracker.logger = MagicMock()

    def test_unified_tracking_any_file_type(self):
        """Test that any file type can be tracked with git (repo or build files)."""
        # With always-use-git strategy, all files are tracked the same way
        self.tracker._tracked_files = set()

        # Should be able to track any file - no distinction between repo/build files
        repo_file = '/test/repo/src/main.py'
        build_file = '/test/repo/build/output.txt'  # Note: everything is relative to repo now

        with (
            patch.object(self.tracker, '_resolve_tracking_path') as mock_resolve,
            patch('pathlib.Path.exists', return_value=True),  # Mock file existence
            patch('pathlib.Path.parent'),  # Mock parent directory
        ):
            mock_resolve.side_effect = lambda x: x  # Return path as-is for this test

            result1 = self.tracker.track_file(repo_file)
            result2 = self.tracker.track_file(build_file)

            assert result1 is True
            assert result2 is True
            assert repo_file in self.tracker._tracked_files
            assert build_file in self.tracker._tracked_files

    def test_git_based_diff_generation(self):
        """Test that all diffs are generated using git, regardless of file location."""
        self.tracker._baseline_stash = 'abc123'

        with (
            patch.object(self.tracker, '_resolve_tracking_path', return_value='/test/repo/file.txt'),
            patch.object(self.tracker, '_get_snapshot_diff', return_value='mock diff content') as mock_diff,
        ):
            # Mock the Path.resolve chain properly to simulate file in repo directory
            with patch('pathlib.Path') as mock_path:
                mock_path.return_value.resolve.return_value = Path('/test/repo/file.txt')
                mock_path.return_value.relative_to.return_value = Path('file.txt')

                result = self.tracker.get_diff('file.txt')

                assert result == 'mock diff content'
                mock_diff.assert_called_once_with('abc123', ['file.txt'])


class TestDiffGeneration:
    """Test diff and patch generation functionality."""

    def setup_method(self):
        """Setup for each test method."""
        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            self.tracker = FileTracker()
            self.tracker.path_manager = PathManager()
            self.tracker.logger = MagicMock()
            self.tracker._baseline_stash = 'abc123'

    @patch.object(FileTracker, '_get_snapshot_diff')
    def test_get_diff_repo_file(self, mock_get_snapshot_diff):
        """Test getting diff for repository file."""
        mock_get_snapshot_diff.return_value = 'diff output'

        result = self.tracker.get_diff('src/main.py')

        assert result == 'diff output'
        mock_get_snapshot_diff.assert_called_once()

    def test_get_all_diffs_empty(self):
        """Test getting all diffs when no files tracked."""
        with patch.object(self.tracker, 'get_tracked_files', return_value=set()):
            result = self.tracker.get_all_diffs()

            assert isinstance(result, dict)
            assert len(result) == 0

    def test_get_patch_dict_structure(self):
        """Test patch dictionary structure."""
        with patch.object(self.tracker, 'get_all_diffs', return_value={}):
            result = self.tracker.get_patch_dict()

            assert 'full' in result
            assert 'patch' in result
            assert isinstance(result['full'], list)
            assert isinstance(result['patch'], list)

    @patch('builtins.open')
    def test_read_file_content_text_file(self, mock_open):
        """Test reading text file content."""
        mock_open.return_value.__enter__.return_value.read.return_value = 'file content'

        with patch.object(self.tracker, '_is_binary_file', return_value=False), patch('pathlib.Path.exists', return_value=True):
            result = self.tracker._read_file_content('/test/file.txt')

            assert result == 'file content'

    def test_is_binary_file_with_null_bytes(self):
        """Test binary file detection with null bytes."""
        with patch('builtins.open') as mock_open:
            mock_open.return_value.__enter__.return_value.read.return_value = b'text\x00binary'
            with patch('pathlib.Path.exists', return_value=True):
                result = self.tracker._is_binary_file('/test/file.bin')

                assert result is True

    def test_should_use_full_content_small_file(self):
        """Test using full content for small files."""
        diff_content = 'small diff'
        file_content = 'small file'  # Less than 1KB

        result = self.tracker._should_use_full_content(diff_content, file_content)

        assert result is True

    def test_should_use_full_content_large_diff(self):
        """Test using full content when diff is large relative to file."""
        diff_content = 'x' * 1000  # Large diff
        file_content = 'x' * 1500  # File content (diff > 50% of file)

        result = self.tracker._should_use_full_content(diff_content, file_content)

        assert result is True


class TestContextManagerAndCleanup:
    """Test context manager functionality and cleanup."""

    @patch.object(FileTracker, 'cleanup')
    def test_context_manager_success(self, mock_cleanup):
        """Test successful context manager usage."""

        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            tracker = FileTracker()
            tracker.path_manager = PathManager()

            with tracker as t:
                assert t is tracker

            mock_cleanup.assert_called_once()

    @patch.object(FileTracker, 'cleanup')
    def test_context_manager_with_exception(self, mock_cleanup):
        """Test context manager cleanup on exception."""

        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            tracker = FileTracker()
            tracker.path_manager = PathManager()

            with pytest.raises(ValueError):
                with tracker:
                    raise ValueError('Test exception')

            mock_cleanup.assert_called_once()

    @patch.object(FileTracker, '_cleanup_snapshots')
    @patch.object(FileTracker, '_cleanup_temporary_git_repo')
    def test_cleanup_method(self, mock_cleanup_git_repo, mock_cleanup_snapshots):
        """Test cleanup method calls all cleanup functions."""

        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            tracker = FileTracker()
            tracker.path_manager = PathManager()
            tracker.logger = MagicMock()
            tracker._tracked_files = {'file1'}
            tracker._tracked_dirs = [{'path': 'dir1', 'ext': None}]
            tracker._baseline_stash = 'abc123'

            tracker.cleanup()

            mock_cleanup_snapshots.assert_called_once()
            mock_cleanup_git_repo.assert_called_once()
            assert len(tracker._tracked_files) == 0
            assert len(tracker._tracked_dirs) == 0
            assert tracker._baseline_stash is None

    @patch.object(FileTracker, 'cleanup')
    def test_destructor_cleanup(self, mock_cleanup):
        """Test cleanup is called in destructor."""

        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            tracker = FileTracker()
            del tracker

            # Cleanup should be called at least once
            assert mock_cleanup.call_count >= 1


class TestErrorHandling:
    """Test error handling and edge cases."""

    def test_track_file_with_exception(self):
        """Test track_file handles exceptions gracefully."""

        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            tracker = FileTracker()
            tracker.path_manager = PathManager()
            tracker.logger = MagicMock()
            tracker._tracked_files = set()

            with patch.object(tracker, '_resolve_tracking_path', side_effect=Exception('Test error')):
                result = tracker.track_file('test.py')

                assert result is False

    def test_get_diff_no_baseline_stash(self):
        """Test get_diff when no baseline stash exists."""

        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            tracker = FileTracker()
            tracker._baseline_stash = None

            result = tracker.get_diff('test.py')

            assert result == ''

    def test_cleanup_with_subprocess_error(self):
        """Test cleanup handles subprocess errors gracefully."""

        with patch.object(FileTracker, '__init__', lambda self, cm=None: None):
            tracker = FileTracker()
            tracker.logger = MagicMock()
            tracker._tracked_files = set()
            tracker._tracked_dirs = []
            tracker._baseline_stash = None

            with (
                patch.object(tracker, '_cleanup_snapshots', side_effect=Exception('Git error')),
                patch.object(tracker, '_cleanup_temporary_git_repo'),
            ):
                # Should not raise exception
                tracker.cleanup()

                # Should still clear tracking state
                assert len(tracker._tracked_files) == 0
