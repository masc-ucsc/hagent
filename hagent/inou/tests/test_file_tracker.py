"""
Tests for FileTracker

Tests git-based file tracking with stash snapshots, directory tracking,
and build directory synchronization for both local and Docker modes.
"""

from pathlib import Path
from unittest.mock import patch, MagicMock

from hagent.inou.file_tracker import FileTracker


class TestFileTracker:
    """Test FileTracker functionality."""

    def test_initialization_without_path_manager(self):
        """Test FileTracker initialization without providing path manager."""
        with patch('hagent.inou.file_tracker.PathManager') as mock_pm_class:
            mock_pm = MagicMock()
            mock_pm_class.return_value = mock_pm

            with patch.object(FileTracker, '_initialize_session'):
                tracker = FileTracker()
                assert tracker.path_manager == mock_pm
                mock_pm_class.assert_called_once()

    def test_initialization_with_path_manager(self):
        """Test FileTracker initialization with provided path manager."""
        mock_pm = MagicMock()

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)
            assert tracker.path_manager == mock_pm
            assert tracker._tracked_paths == set()
            assert tracker._stash_name is None
            assert tracker._stash_created is False

    @patch('subprocess.run')
    def test_initialize_session_with_changes(self, mock_subprocess):
        """Test session initialization when there are changes to stash."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')
        mock_pm.is_local_mode.return_value = False

        # Mock git stash create success
        mock_subprocess.side_effect = [
            MagicMock(returncode=0, stdout='abc123def456'),  # stash create
            MagicMock(returncode=0),  # stash store
        ]

        tracker = FileTracker(mock_pm)

        assert tracker._stash_created is True
        assert tracker._stash_name == 'stash@{0}'

        # Verify git commands were called
        assert mock_subprocess.call_count == 2
        mock_subprocess.assert_any_call(
            ['git', 'stash', 'create', 'pre-hagent-session'],
            cwd='/test/repo',
            capture_output=True,
            text=True,
        )

    @patch('subprocess.run')
    def test_initialize_session_no_changes(self, mock_subprocess):
        """Test session initialization when there are no changes."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')
        mock_pm.is_local_mode.return_value = False

        # Mock git stash create with no output (no changes)
        mock_subprocess.return_value = MagicMock(returncode=0, stdout='')

        with patch.object(FileTracker, '_create_empty_stash') as mock_empty_stash:
            FileTracker(mock_pm)
            mock_empty_stash.assert_called_once()

    @patch('subprocess.run')
    def test_create_empty_stash(self, mock_subprocess):
        """Test empty stash creation."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')
        mock_pm.is_local_mode.return_value = False

        # Mock successful empty stash creation
        mock_subprocess.side_effect = [
            MagicMock(returncode=0),  # git add
            MagicMock(returncode=0, stdout='empty123'),  # stash create
            MagicMock(returncode=0),  # stash store
            MagicMock(returncode=0),  # git reset
        ]

        with patch('pathlib.Path.write_text'):
            with patch('pathlib.Path.unlink'):
                tracker = FileTracker(mock_pm)
                tracker._create_empty_stash()

                assert tracker._stash_created is True
                assert tracker._stash_name == 'stash@{0}'

    @patch('shutil.copytree')
    @patch('shutil.rmtree')
    def test_sync_build_directory(self, mock_rmtree, mock_copytree):
        """Test build directory synchronization for local mode."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')
        mock_pm.build_dir = Path('/test/build')
        mock_pm.get_build_cache_dir.return_value = '/test/cache/build'
        mock_pm.is_local_mode.return_value = True

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        with patch('pathlib.Path.exists', return_value=True):
            tracker._sync_build_directory()

            mock_rmtree.assert_called_once_with(Path('/test/cache/build'))
            mock_copytree.assert_called_once_with(Path('/test/build'), Path('/test/cache/build'))
            assert tracker._build_cache_synced is True

    def test_track_file_absolute_path(self):
        """Test tracking file with absolute path."""
        mock_pm = MagicMock()

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        result = tracker.track_file('/absolute/path/file.txt')

        assert result is True
        assert str(Path('/absolute/path/file.txt').resolve()) in tracker._tracked_paths

    def test_track_file_relative_path_repo(self):
        """Test tracking file with relative path (found in repo)."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')
        mock_pm.build_dir = Path('/test/build')

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        with patch('pathlib.Path.exists', side_effect=lambda: True):
            result = tracker.track_file('src/main.py')

            assert result is True
            expected_path = str((mock_pm.repo_dir / 'src/main.py').resolve())
            assert expected_path in tracker._tracked_paths

    def test_track_file_relative_path_build(self):
        """Test tracking file with relative path (found in build)."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')
        mock_pm.build_dir = Path('/test/build')

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        def mock_exists(self):
            # Repo path doesn't exist, build path does
            return str(self).startswith('/test/build')

        with patch('pathlib.Path.exists', mock_exists):
            result = tracker.track_file('output/result.txt')

            assert result is True
            expected_path = str((mock_pm.build_dir / 'output/result.txt').resolve())
            assert expected_path in tracker._tracked_paths

    def test_track_dir_without_extension(self):
        """Test tracking directory without extension filter."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')
        mock_pm.build_dir = Path('/test/build')

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        with patch('pathlib.Path.exists', return_value=True):
            result = tracker.track_dir('src/main')

            assert result is True
            expected_path = str((mock_pm.repo_dir / 'src/main').resolve())
            assert expected_path in tracker._tracked_paths

    def test_track_dir_with_extension(self):
        """Test tracking directory with extension filter."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        with patch('pathlib.Path.exists', return_value=True):
            result = tracker.track_dir('src', '.py')

            assert result is True
            expected_pattern = str((mock_pm.repo_dir / 'src').resolve() / '*.py')
            assert expected_pattern in tracker._tracked_paths

    def test_track_file_error_handling(self):
        """Test track_file error handling."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')
        mock_pm.build_dir = Path('/test/build')

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        with patch('pathlib.Path.resolve', side_effect=Exception('Test error')):
            with patch('builtins.print') as mock_print:
                result = tracker.track_file('test.txt')

                assert result is False
                mock_print.assert_called()

    @patch('subprocess.run')
    def test_get_tracked_changes_with_changes(self, mock_subprocess):
        """Test getting tracked changes with repository changes."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')
        mock_pm.is_local_mode.return_value = False

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        # Set up tracking state
        tracker._stash_created = True
        tracker._stash_name = 'stash@{0}'
        tracker._tracked_paths = {'/test/repo/src/main.py'}

        # Mock git diff output
        mock_subprocess.return_value = MagicMock(
            returncode=0,
            stdout='diff --git a/src/main.py b/src/main.py\nindex abc123..def456 100644\n--- a/src/main.py\n+++ b/src/main.py\n@@ -1,3 +1,4 @@\n line1\n line2\n+new line\n line3',
        )

        result = tracker.get_tracked_changes()

        assert 'Repository Changes' in result
        assert 'diff --git a/src/main.py' in result

        # Verify git diff was called with correct arguments
        mock_subprocess.assert_called_once()
        args, kwargs = mock_subprocess.call_args
        assert args[0] == ['git', 'diff', 'stash@{0}', '--', 'src/main.py']
        assert kwargs['cwd'] == '/test/repo'

    def test_get_tracked_changes_no_stash(self):
        """Test getting tracked changes when no stash was created."""
        mock_pm = MagicMock()

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        # No stash created
        tracker._stash_created = False

        result = tracker.get_tracked_changes()
        assert result == ''

    def test_get_tracked_changes_no_tracked_paths(self):
        """Test getting tracked changes when no paths are tracked."""
        mock_pm = MagicMock()

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        tracker._stash_created = True
        tracker._stash_name = 'stash@{0}'
        tracker._tracked_paths = set()  # No tracked paths

        result = tracker.get_tracked_changes()
        assert result == ''

    @patch('subprocess.run')
    def test_get_tracked_changes_local_mode_with_build(self, mock_subprocess):
        """Test getting tracked changes in local mode with build changes."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')
        mock_pm.is_local_mode.return_value = True

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        tracker._stash_created = True
        tracker._stash_name = 'stash@{0}'
        tracker._tracked_paths = {'/test/repo/src/main.py'}
        tracker._build_cache_synced = True

        # Mock git diff for repo changes
        mock_subprocess.return_value = MagicMock(returncode=0, stdout='repo diff output')

        with patch.object(tracker, '_get_build_directory_changes', return_value='build diff output'):
            result = tracker.get_tracked_changes()

            assert 'Repository Changes' in result
            assert 'repo diff output' in result
            assert 'Build Directory Changes' in result
            assert 'build diff output' in result

    @patch('subprocess.run')
    def test_get_build_directory_changes(self, mock_subprocess):
        """Test getting build directory changes."""
        mock_pm = MagicMock()
        mock_pm.build_dir = Path('/test/build')
        mock_pm.get_build_cache_dir.return_value = '/test/cache/build'

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        tracker._tracked_paths = {'/test/build/output.txt'}

        with patch('pathlib.Path.exists', return_value=True):
            # Mock diff command success
            mock_subprocess.return_value = MagicMock(
                returncode=1,  # diff returns 1 when differences found
                stdout='diff -u /test/cache/build/output.txt /test/build/output.txt\n--- old\n+++ new\n@@ -1 +1 @@\n-old line\n+new line',
            )

            result = tracker._get_build_directory_changes()

            assert 'diff -u' in result
            assert 'output.txt' in result

            # Verify diff command was called
            mock_subprocess.assert_called_once()
            args = mock_subprocess.call_args[0][0]
            assert args[0] == 'diff'
            assert '-u' in args
            assert '-r' in args

    def test_get_tracked_paths(self):
        """Test getting list of tracked paths."""
        mock_pm = MagicMock()

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        tracker._tracked_paths = {'/path1', '/path2', '/path3'}

        result = tracker.get_tracked_paths()
        assert isinstance(result, list)
        assert set(result) == {'/path1', '/path2', '/path3'}

    @patch('subprocess.run')
    def test_cleanup(self, mock_subprocess):
        """Test cleanup method."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        # Set up state to cleanup
        tracker._stash_created = True
        tracker._stash_name = 'stash@{0}'
        tracker._tracked_paths = {'/some/path'}

        tracker.cleanup()

        # Verify git stash drop was called
        mock_subprocess.assert_called_once_with(
            ['git', 'stash', 'drop', 'stash@{0}'],
            cwd='/test/repo',
            capture_output=True,
        )

        # Verify state was cleared
        assert tracker._stash_created is False
        assert tracker._stash_name is None
        assert len(tracker._tracked_paths) == 0

    def test_cleanup_error_handling(self):
        """Test cleanup error handling."""
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/test/repo')

        with patch.object(FileTracker, '_initialize_session'):
            tracker = FileTracker(mock_pm)

        tracker._stash_created = True
        tracker._stash_name = 'stash@{0}'

        with patch('subprocess.run', side_effect=Exception('Git error')):
            with patch('builtins.print') as mock_print:
                tracker.cleanup()  # Should not raise exception
                mock_print.assert_called()

    def test_context_manager(self):
        """Test FileTracker as context manager."""
        mock_pm = MagicMock()

        with patch.object(FileTracker, '_initialize_session'):
            with patch.object(FileTracker, 'cleanup') as mock_cleanup:
                with FileTracker(mock_pm) as tracker:
                    assert isinstance(tracker, FileTracker)

                mock_cleanup.assert_called_once()

    def test_destructor_cleanup(self):
        """Test cleanup on object destruction."""
        mock_pm = MagicMock()

        with patch.object(FileTracker, '_initialize_session'):
            with patch.object(FileTracker, 'cleanup') as mock_cleanup:
                tracker = FileTracker(mock_pm)
                del tracker

                # Cleanup should be called at least once (may be called multiple times by garbage collector)
                assert mock_cleanup.call_count >= 1
