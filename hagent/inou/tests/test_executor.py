"""
Blackbox tests for Executor

Tests the executor module internal classes:
- ExecutorFactory.create_executor()
- LocalExecutor operations (run_cmd, set_cwd, get_cwd)
- DockerExecutor operations (run_cmd, set_cwd, get_cwd)

Note: Executors are internal classes used by Runner. For end-user code,
use Runner or Builder instead of calling executors directly.

Tests both local and Docker execution modes with actual command execution
where practical.
"""

import tempfile
from pathlib import Path
from unittest.mock import patch, MagicMock

from hagent.inou.executor import ExecutorFactory
from hagent.inou.executor_local import LocalExecutor
from hagent.inou.executor_docker import DockerExecutor
from hagent.inou.path_manager import PathManager


class TestExecutorFactory:
    """Test ExecutorFactory.create_executor() factory method."""

    def test_create_executor_local_mode(self):
        """Test ExecutorFactory returns LocalExecutor in local mode."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            with PathManager.configured(
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor()
                assert isinstance(executor, LocalExecutor)

    def test_create_executor_docker_mode_without_container_manager(self):
        """Test ExecutorFactory returns DockerExecutor in docker mode without container_manager."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            with PathManager.configured(
                docker_image='mascucsc/hagent-simplechisel:2025.11',
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                # Mock ContainerManager creation in the executor module
                with patch('hagent.inou.executor.ContainerManager') as mock_cm_class:
                    mock_cm = MagicMock()
                    mock_cm_class.return_value = mock_cm

                    executor = ExecutorFactory.create_executor()
                    assert isinstance(executor, DockerExecutor)
                    mock_cm_class.assert_called_once()

    def test_create_executor_with_container_manager(self):
        """Test ExecutorFactory returns DockerExecutor when container_manager is provided."""
        mock_cm = MagicMock()

        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            with PathManager.configured(
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor(container_manager=mock_cm)
                assert isinstance(executor, DockerExecutor)
                assert executor.container_manager == mock_cm


class TestLocalExecutorOperations:
    """Test LocalExecutor operations (run_cmd, set_cwd, get_cwd)."""

    def test_run_cmd_simple_command(self):
        """Test run_cmd executes a simple command successfully."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            with PathManager.configured(
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor()

                # Test simple echo command
                exit_code, stdout, stderr = executor.run_cmd('echo "Hello World"', quiet=True)

                assert exit_code == 0
                assert 'Hello World' in stdout
                assert stderr == '' or stderr.strip() == ''

    def test_run_cmd_with_cwd(self):
        """Test run_cmd respects working directory."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()
            subdir = repo_dir / 'subdir'
            subdir.mkdir()

            with PathManager.configured(
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor()

                # Create a file in subdir and try to read it from there
                test_file = subdir / 'test.txt'
                test_file.write_text('test content')

                # Run command in the subdir
                exit_code, stdout, stderr = executor.run_cmd('cat test.txt', cwd=str(subdir), quiet=True)

                assert exit_code == 0
                assert 'test content' in stdout

    def test_run_cmd_with_env_vars(self):
        """Test run_cmd passes environment variables."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            with PathManager.configured(
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor()

                # Test environment variable
                exit_code, stdout, stderr = executor.run_cmd('echo $TEST_VAR', env={'TEST_VAR': 'test_value'}, quiet=True)

                assert exit_code == 0
                assert 'test_value' in stdout

    def test_run_cmd_failing_command(self):
        """Test run_cmd returns non-zero exit code for failing command."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            with PathManager.configured(
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor()

                # Command that should fail
                exit_code, stdout, stderr = executor.run_cmd('exit 42', quiet=True)

                assert exit_code == 42

    def test_run_cmd_nonexistent_directory(self):
        """Test run_cmd handles nonexistent working directory."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            with PathManager.configured(
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor()

                # Try to run in nonexistent directory
                exit_code, stdout, stderr = executor.run_cmd('echo test', cwd='/nonexistent/directory', quiet=True)

                assert exit_code == -1
                assert 'does not exist' in stderr.lower()

    def test_set_cwd_and_get_cwd(self):
        """Test set_cwd and get_cwd work together."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()
            subdir = repo_dir / 'subdir'
            subdir.mkdir()

            with PathManager.configured(
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor()

                # Initial cwd should be repo_dir
                initial_cwd = executor.get_cwd()
                assert Path(initial_cwd).resolve() == repo_dir.resolve()

                # Change to subdir
                success = executor.set_cwd(str(subdir))
                assert success is True

                # Verify new cwd
                new_cwd = executor.get_cwd()
                assert Path(new_cwd).resolve() == subdir.resolve()

    def test_set_cwd_nonexistent_directory(self):
        """Test set_cwd fails for nonexistent directory."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            with PathManager.configured(
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor()

                # Try to change to nonexistent directory
                success = executor.set_cwd('/nonexistent/directory')
                assert success is False

    def test_set_cwd_relative_path(self):
        """Test set_cwd works with relative paths."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()
            subdir = repo_dir / 'subdir'
            subdir.mkdir()

            with PathManager.configured(
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor()

                # Change using relative path
                success = executor.set_cwd('subdir')
                assert success is True

                # Verify new cwd
                new_cwd = executor.get_cwd()
                assert Path(new_cwd).resolve() == subdir.resolve()


class TestDockerExecutorOperations:
    """Test DockerExecutor operations with mocked container."""

    def test_run_cmd_uses_container_manager(self):
        """Test DockerExecutor delegates to container_manager."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            # Mock container manager
            mock_cm = MagicMock()
            mock_cm.run_cmd.return_value = (0, 'docker output', '')
            mock_cm.get_cwd.return_value = '/code/workspace/repo'

            with PathManager.configured(
                docker_image='mascucsc/hagent-simplechisel:2025.11',
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor(container_manager=mock_cm)

                # Run command
                exit_code, stdout, stderr = executor.run_cmd('echo test', quiet=True)

                # Verify container_manager was called
                assert exit_code == 0
                assert stdout == 'docker output'
                mock_cm.run_cmd.assert_called_once()

    def test_run_cmd_with_env_sets_environment(self):
        """Test DockerExecutor sets environment variables."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            # Mock container manager
            mock_cm = MagicMock()
            mock_cm.run_cmd.return_value = (0, 'output', '')

            with PathManager.configured(
                docker_image='mascucsc/hagent-simplechisel:2025.11',
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor(container_manager=mock_cm)

                # Run command with env
                import os

                original_value = os.environ.get('TEST_DOCKER_VAR')
                try:
                    executor.run_cmd('echo test', env={'TEST_DOCKER_VAR': 'test_value'}, quiet=True)

                    # During execution, the env var should be set
                    # After execution, it should be restored
                    assert os.environ.get('TEST_DOCKER_VAR') == original_value
                finally:
                    # Cleanup
                    if original_value is None:
                        os.environ.pop('TEST_DOCKER_VAR', None)
                    else:
                        os.environ['TEST_DOCKER_VAR'] = original_value

    def test_set_cwd_delegates_to_container_manager(self):
        """Test DockerExecutor delegates set_cwd to container_manager."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            # Mock container manager
            mock_cm = MagicMock()
            mock_cm.set_cwd.return_value = True

            with PathManager.configured(
                docker_image='mascucsc/hagent-simplechisel:2025.11',
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor(container_manager=mock_cm)

                # Set cwd
                success = executor.set_cwd('/code/workspace/repo/subdir')

                assert success is True
                mock_cm.set_cwd.assert_called_once_with('/code/workspace/repo/subdir')

    def test_get_cwd_delegates_to_container_manager(self):
        """Test DockerExecutor delegates get_cwd to container_manager."""
        with tempfile.TemporaryDirectory() as temp_dir:
            repo_dir = Path(temp_dir) / 'repo'
            repo_dir.mkdir()

            # Mock container manager
            mock_cm = MagicMock()
            mock_cm.get_cwd.return_value = '/code/workspace/repo'

            with PathManager.configured(
                docker_image='mascucsc/hagent-simplechisel:2025.11',
                repo_dir=str(repo_dir),
                build_dir=str(Path(temp_dir) / 'build'),
                cache_dir=str(Path(temp_dir) / 'cache'),
            ):
                executor = ExecutorFactory.create_executor(container_manager=mock_cm)

                # Get cwd
                cwd = executor.get_cwd()

                assert cwd == '/code/workspace/repo'
                mock_cm.get_cwd.assert_called_once()
