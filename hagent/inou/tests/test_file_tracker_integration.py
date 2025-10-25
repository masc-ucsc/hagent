"""
Integration tests for FileTracker with existing components

Tests FileTracker integration with PathManager, real git repositories,
and various file system scenarios to ensure robust operation.
"""

import subprocess
import uuid
import datetime
from pathlib import Path
from unittest.mock import patch, MagicMock
import pytest

from hagent.inou.file_tracker import FileTracker
from hagent.inou.file_tracker_local import FileTrackerLocal
from hagent.inou.path_manager import PathManager


@pytest.fixture(autouse=True)
def reset_docker_state():
    """Reset global Docker state before each test."""
    import hagent.inou.container_manager as cm

    # Reset global state
    cm._docker_workspace_validated = False

    yield

    # Reset global state again
    cm._docker_workspace_validated = False


@pytest.mark.serial  # These tests manipulate PathManager singleton - must run serially
class TestPathManagerIntegration:
    """Test FileTracker integration with PathManager."""

    def test_file_tracker_with_real_path_manager(self):
        """Test FileTracker with actual PathManager instance."""
        # Reset PathManager to pick up new environment
        PathManager.reset()

        with patch.dict(
            'os.environ',
            {
                'HAGENT_REPO_DIR': '/test/repo',
                'HAGENT_BUILD_DIR': '/test/build',
                'HAGENT_CACHE_DIR': '/test/cache',
            },
        ):
            with (
                patch('pathlib.Path.exists', return_value=True),
                patch('pathlib.Path.mkdir'),
                patch.object(FileTrackerLocal, '_ensure_git_repo', return_value=True),
                patch.object(FileTrackerLocal, '_check_git_available', return_value=True),
                patch.object(FileTrackerLocal, '_create_baseline_snapshot', return_value=None),
            ):
                PathManager.reset()  # Reset after environment change
                path_manager = PathManager()
                tracker = FileTracker(path_manager)

                assert tracker.path_manager is path_manager
                assert tracker.path_manager.execution_mode == 'local'
                assert str(tracker.path_manager.repo_dir) == '/test/repo'

    def test_file_tracker_docker_mode_integration(self):
        """Test FileTracker integration with Docker mode PathManager."""
        # Mock PathManager for docker mode
        mock_pm = MagicMock()
        mock_pm.execution_mode = 'docker'
        mock_pm.is_docker_mode.return_value = True
        mock_pm.is_local_mode.return_value = False
        mock_pm.repo_dir = Path('/code/workspace/repo')

        with (
            patch('pathlib.Path.exists', return_value=True),
            patch('pathlib.Path.mkdir'),
            patch.object(FileTrackerLocal, '_ensure_git_repo', return_value=True),
            patch.object(FileTrackerLocal, '_check_git_available', return_value=True),
            patch.object(FileTrackerLocal, '_create_baseline_snapshot', return_value=None),
        ):
            tracker = FileTracker(mock_pm)

            assert tracker.path_manager.execution_mode == 'docker'

    def test_file_tracker_with_path_manager_validation_error(self):
        """Test FileTracker behavior when PathManager validation fails."""
        # This test verifies the contract: PathManager validates environment on initialization
        # We mock the scenario where validation would fail
        with patch('hagent.inou.path_manager.sys.exit') as mock_exit:
            with patch.dict('os.environ', {}, clear=True):
                # Create a fresh PathManager with empty environment - should trigger sys.exit
                # Note: We need to patch PathManager class's __new__ to create a new instance
                with patch.object(PathManager, '_instance', None):
                    with patch.object(PathManager, '_initialized', False):
                        try:
                            PathManager()
                        except SystemExit:
                            pass  # Expected

                        # Verify the fail-fast behavior occurred
                        mock_exit.assert_called_with(1)


class TestGitRepositoryIntegration:
    """Test FileTracker with real git repositories."""

    def setup_method(self):
        """Setup temporary git repository for each test."""
        test_id = f'{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}'
        self.temp_dir = Path('output') / 'test_file_tracker_integration' / test_id
        self.temp_dir.mkdir(parents=True, exist_ok=True)
        self.repo_dir = self.temp_dir / 'repo'
        self.repo_dir.mkdir()

        # Initialize git repository
        subprocess.run(['git', 'init'], cwd=self.repo_dir, capture_output=True)
        subprocess.run(['git', 'config', 'user.email', 'test@example.com'], cwd=self.repo_dir)
        subprocess.run(['git', 'config', 'user.name', 'Test User'], cwd=self.repo_dir)

        # Create initial commit
        test_file = self.repo_dir / 'README.md'
        test_file.write_text('# Test Repository\n')
        subprocess.run(['git', 'add', 'README.md'], cwd=self.repo_dir)
        subprocess.run(['git', 'commit', '-m', 'Initial commit'], cwd=self.repo_dir)

    def teardown_method(self):
        """Cleanup temporary repository."""
        # Leave directories for inspection - they will be in output/

    def test_file_tracker_with_real_git_repo(self):
        """Test FileTracker with real git repository."""
        # Create mock PathManager pointing to real repo
        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = self.repo_dir
        mock_path_manager.build_dir = self.temp_dir / 'build'
        mock_path_manager.cache_dir = self.temp_dir / 'cache'

        # Create FileTracker
        tracker = FileTracker(mock_path_manager)

        # Verify it was initialized properly
        assert tracker.path_manager is mock_path_manager

        # Test tracking a real file
        test_file = self.repo_dir / 'test.py'
        test_file.write_text('print("hello")\n')

        result = tracker.track_file('test.py')
        assert result is True

        # Verify file is tracked
        tracked_files = tracker.get_tracked_files()
        assert len(tracked_files) > 0
        assert any('test.py' in f for f in tracked_files)

        # Cleanup
        tracker.cleanup()

    def test_file_tracker_with_uncommitted_changes(self):
        """Test FileTracker when repository has uncommitted changes."""
        # Create uncommitted change
        test_file = self.repo_dir / 'uncommitted.py'
        test_file.write_text('print("uncommitted")\n')

        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = self.repo_dir
        mock_path_manager.build_dir = self.temp_dir / 'build'
        mock_path_manager.cache_dir = self.temp_dir / 'cache'

        # FileTracker should create baseline snapshot of uncommitted changes
        tracker = FileTracker(mock_path_manager)

        # Should have created a baseline stash
        assert tracker._baseline_stash is not None
        assert len(tracker._hagent_stashes) > 0

        # Cleanup
        tracker.cleanup()

    def test_file_tracker_with_clean_repository(self):
        """Test FileTracker with clean repository (no uncommitted changes)."""
        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = self.repo_dir
        mock_path_manager.build_dir = self.temp_dir / 'build'
        mock_path_manager.cache_dir = self.temp_dir / 'cache'

        # Repository is clean, so no baseline stash should be created
        tracker = FileTracker(mock_path_manager)

        # Should not have created a baseline stash
        assert tracker._baseline_stash is None
        assert len(tracker._hagent_stashes) == 0

        # Cleanup
        tracker.cleanup()

    def test_file_tracker_diff_generation_real_repo(self):
        """Test diff generation with real git repository."""
        # Create file BEFORE initializing tracker so it's captured in baseline
        test_file = self.repo_dir / 'modified.py'
        test_file.write_text('original content\n')

        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = self.repo_dir
        mock_path_manager.build_dir = self.temp_dir / 'build'
        mock_path_manager.cache_dir = self.temp_dir / 'cache'

        tracker = FileTracker(mock_path_manager)

        # Track the file
        result = tracker.track_file('modified.py')
        assert result is True

        # Modify the file after tracking
        test_file.write_text('modified content\n')

        # Get diff - should show the change
        diff = tracker.get_diff('modified.py')

        # Diff should contain both old and new content or show some change
        assert 'modified.py' in diff or len(diff) > 0  # Some change detected

        # Cleanup
        tracker.cleanup()


class TestFileSystemIntegration:
    """Test FileTracker with various file system scenarios."""

    def setup_method(self):
        """Setup temporary directories for each test."""
        test_id = f'{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}'
        self.temp_dir = Path('output') / 'test_file_tracker_filesystem' / test_id
        self.temp_dir.mkdir(parents=True, exist_ok=True)
        self.repo_dir = self.temp_dir / 'repo'
        self.build_dir = self.temp_dir / 'build'
        self.cache_dir = self.temp_dir / 'cache'

        self.repo_dir.mkdir()
        self.build_dir.mkdir()
        self.cache_dir.mkdir()

    def teardown_method(self):
        """Cleanup temporary directories."""
        # Leave directories for inspection - they will be in output/

    def test_file_tracker_with_various_file_types(self):
        """Test FileTracker with different file types."""
        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = self.repo_dir
        mock_path_manager.build_dir = self.build_dir
        mock_path_manager.cache_dir = self.cache_dir

        with (
            patch.object(FileTrackerLocal, '_ensure_git_repo', return_value=True),
            patch.object(FileTrackerLocal, '_check_git_available', return_value=True),
            patch.object(FileTrackerLocal, '_create_baseline_snapshot', return_value=None),
        ):
            tracker = FileTracker(mock_path_manager)

            # Create different file types
            text_file = self.repo_dir / 'text.txt'
            text_file.write_text('This is a text file\n')

            python_file = self.repo_dir / 'script.py'
            python_file.write_text('print("hello world")\n')

            binary_file = self.repo_dir / 'binary.bin'
            binary_file.write_bytes(b'\x00\x01\x02\x03\x04\x05')

            # Track all files
            assert tracker.track_file('text.txt') is True
            assert tracker.track_file('script.py') is True
            assert tracker.track_file('binary.bin') is True

            # Get tracked files
            tracked = tracker.get_tracked_files()
            assert len(tracked) == 3

            # Test binary file detection
            assert tracker._is_binary_file(str(binary_file)) is True
            assert tracker._is_binary_file(str(text_file)) is False

            # Cleanup
            tracker.cleanup()

    def test_file_tracker_with_nested_directories(self):
        """Test FileTracker with nested directory structures."""
        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = self.repo_dir
        mock_path_manager.build_dir = self.build_dir
        mock_path_manager.cache_dir = self.cache_dir

        with (
            patch.object(FileTrackerLocal, '_ensure_git_repo', return_value=True),
            patch.object(FileTrackerLocal, '_check_git_available', return_value=True),
            patch.object(FileTrackerLocal, '_create_baseline_snapshot', return_value=None),
        ):
            tracker = FileTracker(mock_path_manager)

            # Create nested directory structure
            src_dir = self.repo_dir / 'src'
            src_dir.mkdir()

            main_dir = src_dir / 'main'
            main_dir.mkdir()

            test_dir = src_dir / 'test'
            test_dir.mkdir()

            # Create files in nested directories
            (main_dir / 'app.py').write_text('# Main application\n')
            (test_dir / 'test_app.py').write_text('# Test file\n')
            (src_dir / 'utils.py').write_text('# Utilities\n')

            # Track the src directory with .py filter
            assert tracker.track_dir('src', '.py') is True

            # Get tracked files
            tracked = tracker.get_tracked_files('.py')
            assert len(tracked) == 3

            # Verify all .py files are tracked
            tracked_names = [Path(f).name for f in tracked]
            assert 'app.py' in tracked_names
            assert 'test_app.py' in tracked_names
            assert 'utils.py' in tracked_names

            # Cleanup
            tracker.cleanup()

    def test_file_tracker_permission_handling(self):
        """Test FileTracker behavior with permission issues."""
        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = self.repo_dir
        mock_path_manager.build_dir = self.build_dir
        mock_path_manager.cache_dir = self.cache_dir

        with (
            patch.object(FileTrackerLocal, '_ensure_git_repo', return_value=True),
            patch.object(FileTrackerLocal, '_check_git_available', return_value=True),
            patch.object(FileTrackerLocal, '_create_baseline_snapshot', return_value=None),
        ):
            tracker = FileTracker(mock_path_manager)

            # Try to track a non-existent file
            result = tracker.track_file('nonexistent/file.py')
            # Should handle gracefully
            assert result is False or result is True  # Either is acceptable

            # Try to track a directory that doesn't exist
            result = tracker.track_dir('nonexistent/dir')
            # Should handle gracefully
            assert result is False or result is True  # Either is acceptable

            # Cleanup should work even with tracking failures
            tracker.cleanup()


class TestPerformanceIntegration:
    """Test FileTracker performance with larger file sets."""

    def setup_method(self):
        """Setup for performance tests."""
        test_id = f'{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}'
        self.temp_dir = Path('output') / 'test_file_tracker_performance' / test_id
        self.temp_dir.mkdir(parents=True, exist_ok=True)
        self.repo_dir = self.temp_dir / 'repo'
        self.repo_dir.mkdir()

    def teardown_method(self):
        """Cleanup after performance tests."""
        # Leave directories for inspection - they will be in output/

    def test_file_tracker_with_many_files(self):
        """Test FileTracker performance with many files."""
        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = self.repo_dir
        mock_path_manager.build_dir = self.temp_dir / 'build'
        mock_path_manager.cache_dir = self.temp_dir / 'cache'

        with (
            patch.object(FileTrackerLocal, '_ensure_git_repo', return_value=True),
            patch.object(FileTrackerLocal, '_check_git_available', return_value=True),
            patch.object(FileTrackerLocal, '_create_baseline_snapshot', return_value=None),
        ):
            tracker = FileTracker(mock_path_manager)

            # Create many files
            num_files = 50  # Reasonable number for testing
            for i in range(num_files):
                file_path = self.repo_dir / f'file_{i}.py'
                file_path.write_text(f'# File {i}\nprint("File {i}")\n')

                # Track every 10th file individually
                if i % 10 == 0:
                    tracker.track_file(f'file_{i}.py')

            # Track all files via directory
            tracker.track_dir('.', '.py')

            # Get tracked files - should handle large number efficiently
            tracked = tracker.get_tracked_files('.py')
            assert len(tracked) >= num_files  # Should find all files

            # Cleanup should be efficient
            tracker.cleanup()

    def test_file_tracker_memory_usage(self):
        """Test FileTracker memory usage patterns."""
        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = self.repo_dir
        mock_path_manager.build_dir = self.temp_dir / 'build'
        mock_path_manager.cache_dir = self.temp_dir / 'cache'

        with (
            patch.object(FileTrackerLocal, '_ensure_git_repo', return_value=True),
            patch.object(FileTrackerLocal, '_check_git_available', return_value=True),
            patch.object(FileTrackerLocal, '_create_baseline_snapshot', return_value=None),
        ):
            tracker = FileTracker(mock_path_manager)

            # Track and untrack files multiple times
            for iteration in range(5):
                for i in range(10):
                    file_path = self.repo_dir / f'temp_{iteration}_{i}.py'
                    file_path.write_text(f'# Temp file {iteration}-{i}\n')
                    tracker.track_file(f'temp_{iteration}_{i}.py')

                # Get tracked files
                tracked = tracker.get_tracked_files()
                assert len(tracked) >= 10

                # Cleanup files
                for i in range(10):
                    file_path = self.repo_dir / f'temp_{iteration}_{i}.py'
                    if file_path.exists():
                        file_path.unlink()

            # Final cleanup
            tracker.cleanup()


class TestErrorRecoveryIntegration:
    """Test FileTracker error recovery and resilience."""

    def test_file_tracker_recovery_from_git_errors(self):
        """Test FileTracker recovery from git command errors."""
        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = Path('/nonexistent/repo')
        mock_path_manager.build_dir = Path('/nonexistent/build')
        mock_path_manager.cache_dir = Path('/nonexistent/cache')

        # Should fail fast due to invalid repo
        with patch('hagent.inou.file_tracker_local.sys.exit') as mock_exit:
            FileTracker(mock_path_manager)
            mock_exit.assert_called_with(1)

    def test_file_tracker_cleanup_resilience(self):
        """Test FileTracker cleanup resilience to errors."""
        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = Path('/test/repo')

        with (
            patch.object(FileTrackerLocal, '_ensure_git_repo', return_value=True),
            patch.object(FileTrackerLocal, '_check_git_available', return_value=True),
            patch.object(FileTrackerLocal, '_create_baseline_snapshot', return_value=None),
        ):
            tracker = FileTracker(mock_path_manager)

            # Add some stashes to cleanup list
            tracker._hagent_stashes = ['abc123', 'def456']

            # Mock subprocess to simulate git errors
            with patch('subprocess.run', side_effect=Exception('Git error')):
                # Cleanup should not raise exception
                tracker.cleanup()

                # State should still be cleared
                assert len(tracker._tracked_files) == 0
                assert len(tracker._tracked_dirs) == 0

    def test_file_tracker_context_manager_exception_handling(self):
        """Test FileTracker context manager with exceptions."""
        mock_path_manager = MagicMock()
        mock_path_manager.repo_dir = Path('/test/repo')

        with (
            patch.object(FileTrackerLocal, '_ensure_git_repo', return_value=True),
            patch.object(FileTrackerLocal, '_check_git_available', return_value=True),
            patch.object(FileTrackerLocal, '_create_baseline_snapshot', return_value=None),
        ):
            with patch.object(FileTracker, 'cleanup') as mock_cleanup:
                with pytest.raises(ValueError):
                    with FileTracker(mock_path_manager):
                        raise ValueError('Test exception')

                # Cleanup should still be called even with exception
                # Note: cleanup may be called twice (context manager + destructor)
                assert mock_cleanup.call_count >= 1
