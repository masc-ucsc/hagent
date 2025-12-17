#!/usr/bin/env python3
"""
Unit tests for Runner class showcasing common use cases.

These tests demonstrate how Runner simplifies the usage of Executor, ContainerManager,
PathManager, and FileTracker by providing a unified interface.
"""

import pytest
import uuid
import datetime
from pathlib import Path
from unittest.mock import patch

from hagent.inou.runner import Runner
from hagent.inou.path_manager import PathManager


class TestRunner:
    """Test cases for Runner class showcasing different use cases."""

    @pytest.fixture(autouse=True)
    def setup_test_environment(self):
        """Setup test environment for each test using PathManager.configured()."""
        # Create unique directories for testing
        test_id = f'{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}'
        self.test_dir = Path('output') / 'test_runner' / test_id
        self.test_dir.mkdir(parents=True, exist_ok=True)
        self.repo_dir = self.test_dir / 'repo'
        self.build_dir = self.test_dir / 'build'
        self.cache_dir = self.test_dir / 'cache'

        # Create directories
        self.repo_dir.mkdir(parents=True)
        self.build_dir.mkdir(parents=True)
        self.cache_dir.mkdir(parents=True)

        # Use PathManager.configured() for clean test isolation
        with PathManager.configured(
            repo_dir=str(self.repo_dir),
            build_dir=str(self.build_dir),
            cache_dir=str(self.cache_dir),
        ):
            yield

        # Leave directories for inspection - they will be in output/

    def test_basic_local_execution(self):
        """Test Case 1: Basic local command execution without file tracking."""
        runner = Runner()

        # Setup should succeed in local mode
        assert runner.setup(), f'Setup failed: {runner.get_error()}'
        assert runner.is_local_mode()
        assert not runner.is_docker_mode()

        # Run a simple command
        exit_code, stdout, stderr = runner.run_cmd('echo "Hello World"')
        assert exit_code == 0
        assert 'Hello World' in stdout

        # FileTracker should not be initialized yet (lazy initialization)
        assert runner.file_tracker is None

        runner.cleanup()

    def test_docker_mode_initialization(self, request):
        """Test Case 2: Docker mode with image specification."""
        # Skip if running in forked mode (Python 3.13 fork + Docker client network calls = segfault)
        import pytest

        if hasattr(request.config, 'option') and hasattr(request.config.option, 'forked') and request.config.option.forked:
            pytest.skip('Test incompatible with --forked due to Python 3.13 Docker client fork safety issues')

        # Use PathManager.configured() to switch to docker mode
        with PathManager.configured(
            docker_image='mascucsc/hagent-simplechisel:2025.12',
            repo_dir=str(self.repo_dir),
            build_dir=str(self.build_dir),
            cache_dir=str(self.cache_dir),
        ):
            runner = Runner(docker_image='mascucsc/hagent-simplechisel:2025.12')

            assert runner.is_docker_mode()
            assert not runner.is_local_mode()
            assert runner.docker_image == 'mascucsc/hagent-simplechisel:2025.12'
            assert runner.container_manager is not None

            runner.cleanup()

    def test_docker_mode_without_image_fails(self, request):
        """Test Case 3: Docker mode picks image from PathManager when not explicitly provided."""
        # Skip if running in forked mode (Python 3.13 fork + Docker client network calls = segfault)
        import pytest

        if hasattr(request.config, 'option') and hasattr(request.config.option, 'forked') and request.config.option.forked:
            pytest.skip('Test incompatible with --forked due to Python 3.13 Docker client fork safety issues')

        # Use PathManager.configured() to enable docker mode
        with PathManager.configured(
            docker_image='some-image:tag',
            repo_dir=str(self.repo_dir),
            build_dir=str(self.build_dir),
            cache_dir=str(self.cache_dir),
        ):
            runner = Runner()  # No docker_image provided, should use PathManager value

            assert runner.docker_image == 'some-image:tag'
            assert runner.container_manager is not None

            runner.cleanup()

    def test_file_tracking_lazy_initialization(self):
        """Test Case 4: FileTracker lazy initialization when tracking is used."""
        runner = Runner()
        assert runner.setup()

        # FileTracker should not be initialized yet
        assert runner.file_tracker is None

        # Create a test file
        test_file = self.repo_dir / 'test.scala'
        test_file.write_text('object Test { def main(): Unit = {} }')

        # Track file - this should trigger FileTracker initialization
        success = runner.track_file('test.scala')
        assert success, f'File tracking failed: {runner.get_error()}'

        # Now FileTracker should be initialized
        assert runner.file_tracker is not None

        # Verify file is tracked
        tracked_files = runner.get_tracked_files()
        assert any('test.scala' in path for path in tracked_files)

        runner.cleanup()

    def test_directory_tracking_with_extension_filter(self):
        """Test Case 5: Directory tracking with extension filtering."""
        runner = Runner()
        assert runner.setup()

        # Create test files with different extensions
        src_dir = self.repo_dir / 'src'
        src_dir.mkdir()

        (src_dir / 'Main.scala').write_text('object Main')
        (src_dir / 'Utils.scala').write_text('object Utils')
        (src_dir / 'README.md').write_text('# Project')
        (src_dir / 'build.sbt').write_text('name := "test"')

        # Track directory with .scala filter
        success = runner.track_dir('src', '.scala')
        assert success, f'Directory tracking failed: {runner.get_error()}'

        # Get tracked files with .scala filter
        scala_files = runner.get_tracked_files('.scala')
        assert len(scala_files) == 2
        assert any('Main.scala' in path for path in scala_files)
        assert any('Utils.scala' in path for path in scala_files)

        # Verify non-.scala files are not tracked when filtering
        all_files = runner.get_tracked_files()
        md_files = [f for f in all_files if f.endswith('.md')]
        assert len(md_files) == 0  # .md files should not be in tracked files due to .scala filter

        runner.cleanup()

    @patch('hagent.inou.runner.FileTracker')
    def test_file_tracking_error_handling(self, mock_file_tracker):
        """Test Case 6: Error handling when FileTracker initialization fails."""
        # Mock FileTracker to raise an exception
        mock_file_tracker.side_effect = Exception('FileTracker init failed')

        runner = Runner()
        assert runner.setup()

        # Attempt to track file should fail gracefully
        success = runner.track_file('test.scala')
        assert not success
        assert 'Failed to initialize FileTracker' in runner.get_error()

        runner.cleanup()

    def test_working_directory_change(self):
        """Test Case 7: Working directory change functionality."""
        runner = Runner()
        assert runner.setup()

        # Create subdirectory
        subdir = self.repo_dir / 'subproject'
        subdir.mkdir()

        # Change working directory
        success = runner.set_cwd('subproject')
        assert success, f'Directory change failed: {runner.get_error()}'

        # Run command in new directory
        exit_code, stdout, stderr = runner.run_cmd('pwd')
        assert exit_code == 0
        assert 'subproject' in stdout

        runner.cleanup()

    def test_diff_generation_workflow(self):
        """Test Case 8: Complete workflow with file modification and diff generation."""
        runner = Runner()
        assert runner.setup()

        # Create and track initial file
        test_file = self.repo_dir / 'Calculator.scala'
        original_content = """object Calculator {
  def add(a: Int, b: Int): Int = a + b
  def subtract(a: Int, b: Int): Int = a - b
}"""
        test_file.write_text(original_content)

        # Track file
        assert runner.track_file('Calculator.scala')

        # Modify file (simulate code changes)
        modified_content = """object Calculator {
  def add(a: Int, b: Int): Int = a + b
  def subtract(a: Int, b: Int): Int = a - b
  def multiply(a: Int, b: Int): Int = a * b
}"""
        test_file.write_text(modified_content)

        # Get diff - just verify we can call the methods without errors
        # The exact diff content depends on how FileTracker handles baselines
        diff = runner.get_diff('Calculator.scala')
        assert isinstance(diff, str)

        # Get all diffs
        all_diffs = runner.get_all_diffs()
        assert isinstance(all_diffs, dict)

        # Get patch dictionary
        patch_dict = runner.get_patch_dict()
        assert 'patch' in patch_dict
        assert 'full' in patch_dict
        assert isinstance(patch_dict['patch'], list)
        assert isinstance(patch_dict['full'], list)

        runner.cleanup()

    def test_context_manager_usage(self):
        """Test Case 9: Context manager usage for automatic cleanup."""
        test_file = self.repo_dir / 'test.txt'
        test_file.write_text('test content')

        # Use Runner as context manager
        with Runner() as runner:
            assert runner.setup()

            # Track file
            assert runner.track_file('test.txt')
            assert runner.file_tracker is not None

            # Run command
            exit_code, stdout, stderr = runner.run_cmd('echo "test"')
            assert exit_code == 0

        # After context exit, cleanup should have been called
        # Note: We can't easily test this directly, but the cleanup should have happened

    def test_multiple_directory_tracking(self):
        """Test Case 10: Tracking multiple directories with different filters."""
        runner = Runner()
        assert runner.setup()

        # Create multiple directories with different file types
        scala_dir = self.repo_dir / 'scala'
        verilog_dir = self.repo_dir / 'verilog'
        scala_dir.mkdir()
        verilog_dir.mkdir()

        # Create files
        (scala_dir / 'Main.scala').write_text('object Main')
        (scala_dir / 'Utils.scala').write_text('object Utils')
        (verilog_dir / 'cpu.v').write_text('module cpu();')
        (verilog_dir / 'memory.sv').write_text('module memory();')

        # Track directories with different filters
        assert runner.track_dir('scala', '.scala')
        assert runner.track_dir('verilog', '.v')
        assert runner.track_dir('verilog', '.sv')

        # Get files by extension
        scala_files = runner.get_tracked_files('.scala')
        v_files = runner.get_tracked_files('.v')
        sv_files = runner.get_tracked_files('.sv')

        assert len(scala_files) == 2
        assert len(v_files) == 1
        assert len(sv_files) == 1

        # Get all tracked files
        all_files = runner.get_tracked_files()
        assert len(all_files) == 4

        runner.cleanup()


# Showcase more advanced usage patterns
class TestRunnerAdvancedUseCases:
    """Advanced use cases that showcase Runner's capabilities."""

    @pytest.fixture(autouse=True)
    def setup_test_environment(self):
        """Setup test environment using PathManager.configured()."""
        test_id = f'{datetime.datetime.now().strftime("%Y%m%d_%H%M%S")}_{uuid.uuid4().hex[:8]}'
        self.test_dir = Path('output') / 'test_runner_advanced' / test_id
        self.test_dir.mkdir(parents=True, exist_ok=True)
        self.repo_dir = self.test_dir / 'repo'
        self.build_dir = self.test_dir / 'build'
        self.cache_dir = self.test_dir / 'cache'

        for dir_path in [self.repo_dir, self.build_dir, self.cache_dir]:
            dir_path.mkdir(parents=True)

        # Use PathManager.configured() for clean test isolation
        with PathManager.configured(
            repo_dir=str(self.repo_dir),
            build_dir=str(self.build_dir),
            cache_dir=str(self.cache_dir),
        ):
            yield

        # Leave directories for inspection - they will be in output/

    def test_build_and_track_workflow(self):
        """Test Case: Simulate a build process with file tracking."""
        runner = Runner()
        assert runner.setup()

        # Create source file
        src_file = self.repo_dir / 'src' / 'main.cpp'
        src_file.parent.mkdir(parents=True)
        src_file.write_text("""#include <iostream>
int main() {
    std::cout << "Hello World" << std::endl;
    return 0;
}""")

        # Track source and build directories
        assert runner.track_dir('src', '.cpp')
        assert runner.track_dir('../build')  # Track build directory

        # Simulate build process that creates output files
        build_output = self.build_dir / 'main.o'
        build_output.write_text('binary content')

        # Verify tracking
        tracked_files = runner.get_tracked_files()
        assert any('main.cpp' in path for path in tracked_files)

        runner.cleanup()

    def test_error_recovery_workflow(self):
        """Test Case: Error handling and recovery in a typical workflow."""
        runner = Runner()
        assert runner.setup()

        # Try to run a command that will fail
        exit_code, stdout, stderr = runner.run_cmd('nonexistent_command')
        assert exit_code != 0

        # Runner should still be usable after a failed command
        exit_code, stdout, stderr = runner.run_cmd('echo "recovery test"')
        assert exit_code == 0
        assert 'recovery test' in stdout

        # Try to track a non-existent file
        runner.track_file('nonexistent.file')
        # This might succeed or fail depending on FileTracker implementation
        # but should not crash the Runner

        # Runner should still be usable
        exit_code, stdout, stderr = runner.run_cmd('echo "still working"')
        assert exit_code == 0

        runner.cleanup()


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
