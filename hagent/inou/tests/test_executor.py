"""
Tests for Executor

Tests execution strategies for both local and Docker execution modes,
including command execution, environment handling, and path translation.
"""

import os
import tempfile
import pytest
from pathlib import Path
from unittest.mock import patch, MagicMock

from hagent.inou.executor import ExecutorFactory, create_executor, run_cmd
from hagent.inou.executor_local import LocalExecutor
from hagent.inou.executor_docker import DockerExecutor


class TestLocalExecutor:
    """Test LocalExecutor functionality."""

    def test_initialization(self):
        """Test LocalExecutor initialization."""
        with patch('hagent.inou.executor_local.PathManager') as mock_pm_class:
            mock_pm = MagicMock()
            mock_pm_class.return_value = mock_pm

            executor = LocalExecutor()
            assert executor.path_manager == mock_pm
            mock_pm_class.assert_called_once()

    def test_initialization_with_path_manager(self):
        """Test LocalExecutor initialization with provided path manager."""
        mock_pm = MagicMock()
        executor = LocalExecutor(mock_pm)
        assert executor.path_manager == mock_pm

    def test_run_quiet_success(self):
        """Test LocalExecutor.run with quiet mode and successful command."""
        with tempfile.TemporaryDirectory() as temp_dir:
            mock_pm = MagicMock()
            executor = LocalExecutor(mock_pm)

            with patch('subprocess.run') as mock_run:
                mock_result = MagicMock()
                mock_result.returncode = 0
                mock_result.stdout = 'test output'
                mock_result.stderr = 'test error'
                mock_run.return_value = mock_result

                exit_code, stdout, stderr = executor.run_cmd('echo test', temp_dir, {'TEST_VAR': 'value'}, quiet=True)

                assert exit_code == 0
                assert stdout == 'test output'
                assert stderr == 'test error'

                # Verify subprocess.run was called correctly
                mock_run.assert_called_once()
                args, kwargs = mock_run.call_args
                assert kwargs['shell'] is True
                assert kwargs['cwd'] == str(Path(temp_dir).resolve())
                assert kwargs['capture_output'] is True
                assert kwargs['text'] is True
                assert 'TEST_VAR' in kwargs['env']
                assert kwargs['env']['TEST_VAR'] == 'value'

    def test_run_nonexistent_directory(self):
        """Test LocalExecutor.run with non-existent working directory."""
        mock_pm = MagicMock()
        executor = LocalExecutor(mock_pm)

        exit_code, stdout, stderr = executor.run_cmd('echo test', '/nonexistent/directory', {}, quiet=True)

        assert exit_code == -1
        assert stdout == ''
        assert 'Working directory does not exist' in stderr

    def test_run_not_directory(self):
        """Test LocalExecutor.run with file path instead of directory."""
        with tempfile.NamedTemporaryFile() as temp_file:
            mock_pm = MagicMock()
            executor = LocalExecutor(mock_pm)

            exit_code, stdout, stderr = executor.run_cmd('echo test', temp_file.name, {}, quiet=True)

            assert exit_code == -1
            assert stdout == ''
            assert 'not a directory' in stderr

    def test_run_streaming_mode(self):
        """Test LocalExecutor.run with streaming output."""
        with tempfile.TemporaryDirectory() as temp_dir:
            mock_pm = MagicMock()
            executor = LocalExecutor(mock_pm)

            with patch('subprocess.Popen') as mock_popen:
                mock_process = MagicMock()
                mock_process.poll.side_effect = [None, None, 0]  # Running, then finished
                mock_process.stdout.readline.side_effect = ['line1\n', 'line2\n', '']
                mock_process.stderr.readline.side_effect = ['error1\n', '']
                mock_process.stdout.read.return_value = ''
                mock_process.stderr.read.return_value = ''
                mock_process.wait.return_value = 0
                mock_popen.return_value = mock_process

                with patch('builtins.print') as mock_print:
                    exit_code, stdout, stderr = executor.run_cmd('echo test', temp_dir, {}, quiet=False)

                assert exit_code == 0
                assert 'line1\n' in stdout
                assert 'line2\n' in stdout
                assert 'error1\n' in stderr

                # Verify streaming output was printed
                mock_print.assert_any_call('local:run: line1')
                mock_print.assert_any_call('local:run: line2')

    def test_run_exception_handling(self):
        """Test LocalExecutor.run exception handling."""
        with tempfile.TemporaryDirectory() as temp_dir:
            mock_pm = MagicMock()
            executor = LocalExecutor(mock_pm)

            with patch('subprocess.run', side_effect=Exception('Test error')):
                exit_code, stdout, stderr = executor.run_cmd('echo test', temp_dir, {}, quiet=True)

                assert exit_code == -1
                assert stdout == ''
                assert 'Command execution failed: Test error' in stderr


class TestDockerExecutor:
    """Test DockerExecutor functionality."""

    def test_initialization_with_file_manager(self):
        """Test DockerExecutor initialization without managers (creates default container_manager)."""
        with patch('hagent.inou.container_manager.ContainerManager') as mock_cm_class:
            with patch('hagent.inou.executor_docker.PathManager') as mock_pm_class:
                mock_cm = MagicMock()
                mock_pm = MagicMock()
                mock_cm_class.return_value = mock_cm
                mock_pm_class.return_value = mock_pm

                executor = DockerExecutor()
                assert executor.container_manager == mock_cm
                assert executor.path_manager == mock_pm
                mock_cm_class.assert_called_once_with(image='mascucsc/hagent-simplechisel:2025.09r', path_manager=mock_pm)

    def test_initialization_with_container_manager(self):
        """Test DockerExecutor initialization with container_manager (preferred)."""
        mock_cm = MagicMock()
        mock_pm = MagicMock()
        executor = DockerExecutor(container_manager=mock_cm, path_manager=mock_pm)
        assert executor.container_manager == mock_cm
        assert executor.path_manager == mock_pm

    def test_initialization_with_both_managers(self):
        """Test DockerExecutor initialization with both container and path managers."""
        mock_cm = MagicMock()
        mock_pm = MagicMock()
        executor = DockerExecutor(container_manager=mock_cm, path_manager=mock_pm)
        assert executor.container_manager == mock_cm
        assert executor.path_manager == mock_pm

    def test_initialization_no_managers(self):
        """Test DockerExecutor initialization without managers (creates container_manager)."""
        with patch('hagent.inou.container_manager.ContainerManager') as mock_cm_class:
            with patch('hagent.inou.executor_docker.PathManager') as mock_pm_class:
                mock_cm = MagicMock()
                mock_pm = MagicMock()
                mock_cm_class.return_value = mock_cm
                mock_pm_class.return_value = mock_pm

                executor = DockerExecutor()
                assert executor.container_manager == mock_cm
                mock_cm_class.assert_called_once_with(image='mascucsc/hagent-simplechisel:2025.09r', path_manager=mock_pm)

    def test_run_basic_with_file_manager(self):
        """Test DockerExecutor.run basic functionality with container_manager."""
        mock_cm = MagicMock()
        mock_pm = MagicMock()
        mock_cm.run_cmd.return_value = (0, 'output', 'error')

        executor = DockerExecutor(container_manager=mock_cm, path_manager=mock_pm)

        with patch.dict(os.environ, {}, clear=True):
            exit_code, stdout, stderr = executor.run_cmd('echo test', '/test/path', {'TEST_VAR': 'value'}, quiet=True)

        assert exit_code == 0
        assert stdout == 'output'
        assert stderr == 'error'

        # Verify container_manager.run was called
        mock_cm.run_cmd.assert_called_once_with('echo test', '/test/path', True)

    def test_run_basic_with_container_manager(self):
        """Test DockerExecutor.run basic functionality with container_manager."""
        mock_cm = MagicMock()
        mock_pm = MagicMock()
        mock_cm.run_cmd.return_value = (0, 'output', 'error')

        executor = DockerExecutor(container_manager=mock_cm, path_manager=mock_pm)

        with patch.dict(os.environ, {}, clear=True):
            exit_code, stdout, stderr = executor.run_cmd('echo test', '/test/path', {'TEST_VAR': 'value'}, quiet=True)

        assert exit_code == 0
        assert stdout == 'output'
        assert stderr == 'error'

        # Verify container_manager.run was called
        mock_cm.run_cmd.assert_called_once_with('echo test', '/test/path', True)

    def test_run_environment_restoration(self):
        """Test DockerExecutor.run environment variable restoration."""
        mock_cm = MagicMock()
        mock_pm = MagicMock()
        mock_cm.run_cmd.return_value = (0, 'output', 'error')

        executor = DockerExecutor(container_manager=mock_cm, path_manager=mock_pm)

        # Set initial environment
        original_env = os.environ.copy()
        os.environ['EXISTING_VAR'] = 'original'

        try:
            exit_code, stdout, stderr = executor.run_cmd(
                'echo test', '/test/path', {'EXISTING_VAR': 'modified', 'NEW_VAR': 'new'}, quiet=True
            )

            # After execution, environment should be restored
            assert os.environ['EXISTING_VAR'] == 'original'
            assert 'NEW_VAR' not in os.environ

        finally:
            # Restore original environment
            os.environ.clear()
            os.environ.update(original_env)

    @patch('hagent.inou.executor_docker.is_docker_mode', return_value=True)
    def test_translate_path_to_container_repo_dir(self, mock_is_docker_mode):
        """Test path translation for repo directory."""
        mock_cm = MagicMock()
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/host/repo')
        mock_pm.build_dir = Path('/host/build')
        mock_pm.cache_dir = Path('/host/cache')

        executor = DockerExecutor(container_manager=mock_cm, path_manager=mock_pm)

        # Test repo dir path translation
        result = executor._translate_path_to_container('/host/repo/subdir')
        assert result == '/code/workspace/repo/subdir'

        # Test exact repo dir match
        result = executor._translate_path_to_container('/host/repo')
        assert result == '/code/workspace/repo'

    @patch('hagent.inou.executor_docker.is_docker_mode', return_value=True)
    def test_translate_path_to_container_build_dir(self, mock_is_docker_mode):
        """Test path translation for build directory."""
        mock_cm = MagicMock()
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/host/repo')
        mock_pm.build_dir = Path('/host/build')
        mock_pm.cache_dir = Path('/host/cache')

        executor = DockerExecutor(container_manager=mock_cm, path_manager=mock_pm)

        # Test build dir path translation
        result = executor._translate_path_to_container('/host/build/output')
        assert result == '/code/workspace/build/output'

    @patch('hagent.inou.executor_docker.is_docker_mode', return_value=True)
    def test_translate_path_to_container_cache_dir(self, mock_is_docker_mode):
        """Test path translation for cache directory."""
        mock_cm = MagicMock()
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/host/repo')
        mock_pm.build_dir = Path('/host/build')
        mock_pm.cache_dir = Path('/host/cache')

        executor = DockerExecutor(container_manager=mock_cm, path_manager=mock_pm)

        # Test cache dir path translation
        result = executor._translate_path_to_container('/host/cache/logs')
        assert result == '/code/workspace/cache/logs'

    @patch('hagent.inou.executor_docker.is_docker_mode', return_value=True)
    def test_translate_path_to_container_no_match(self, mock_is_docker_mode):
        """Test path translation for unknown path."""
        mock_cm = MagicMock()
        mock_pm = MagicMock()
        mock_pm.repo_dir = Path('/host/repo')
        mock_pm.build_dir = Path('/host/build')
        mock_pm.cache_dir = Path('/host/cache')

        executor = DockerExecutor(container_manager=mock_cm, path_manager=mock_pm)

        # Test unknown path - should return original
        result = executor._translate_path_to_container('/other/path')
        assert result == str(Path('/other/path').resolve())

    @patch('hagent.inou.executor_docker.is_docker_mode', return_value=False)
    def test_translate_path_to_container_non_docker_mode(self, mock_is_docker_mode):
        """Test path translation in non-Docker mode."""
        mock_cm = MagicMock()
        mock_pm = MagicMock()

        executor = DockerExecutor(container_manager=mock_cm, path_manager=mock_pm)

        result = executor._translate_path_to_container('/any/path')
        assert result == str(Path('/any/path').resolve())


class TestExecutorFactory:
    """Test ExecutorFactory functionality."""

    def test_create_executor_local_mode(self):
        """Test factory creates LocalExecutor for local mode."""
        mock_pm = MagicMock()
        mock_pm.execution_mode = 'local'

        with patch('hagent.inou.executor.LocalExecutor') as mock_local:
            mock_executor = MagicMock()
            mock_local.return_value = mock_executor

            result = ExecutorFactory.create_executor(path_manager=mock_pm)

            assert result == mock_executor
            mock_local.assert_called_once_with(mock_pm)

    def test_create_executor_docker_mode_with_file_manager(self):
        """Test factory creates DockerExecutor for Docker mode with container_manager."""
        mock_pm = MagicMock()
        mock_pm.execution_mode = 'docker'
        mock_cm = MagicMock()

        with patch('hagent.inou.executor.DockerExecutor') as mock_docker:
            mock_executor = MagicMock()
            mock_docker.return_value = mock_executor

            result = ExecutorFactory.create_executor(container_manager=mock_cm, path_manager=mock_pm)

            assert result == mock_executor
            mock_docker.assert_called_once_with(mock_cm, mock_pm)

    def test_create_executor_docker_mode_with_container_manager(self):
        """Test factory creates DockerExecutor for Docker mode with container_manager."""
        mock_pm = MagicMock()
        mock_pm.execution_mode = 'docker'
        mock_cm = MagicMock()

        with patch('hagent.inou.executor.DockerExecutor') as mock_docker:
            mock_executor = MagicMock()
            mock_docker.return_value = mock_executor

            result = ExecutorFactory.create_executor(container_manager=mock_cm, path_manager=mock_pm)

            assert result == mock_executor
            mock_docker.assert_called_once_with(mock_cm, mock_pm)

    def test_create_executor_docker_mode_no_managers(self):
        """Test factory creates DockerExecutor for Docker mode without managers (auto-creates container_manager)."""
        mock_pm = MagicMock()
        mock_pm.execution_mode = 'docker'

        with patch('hagent.inou.executor.DockerExecutor') as mock_docker:
            mock_executor = MagicMock()
            mock_docker.return_value = mock_executor

            result = ExecutorFactory.create_executor(path_manager=mock_pm)

            assert result == mock_executor
            mock_docker.assert_called_once_with(None, mock_pm)

    def test_create_executor_invalid_mode(self):
        """Test factory raises error for invalid execution mode."""
        mock_pm = MagicMock()
        mock_pm.execution_mode = 'invalid'

        with pytest.raises(ValueError, match='Invalid execution mode'):
            ExecutorFactory.create_executor(path_manager=mock_pm)

    def test_create_executor_default_path_manager(self):
        """Test factory creates default PathManager when none provided."""
        with patch('hagent.inou.executor.PathManager') as mock_pm_class:
            mock_pm = MagicMock()
            mock_pm.execution_mode = 'local'
            mock_pm_class.return_value = mock_pm

            with patch('hagent.inou.executor_local.LocalExecutor'):
                ExecutorFactory.create_executor()
                mock_pm_class.assert_called_once()


class TestConvenienceFunctions:
    """Test convenience functions."""

    def test_create_executor_function(self):
        """Test create_executor convenience function."""
        with patch('hagent.inou.executor.ExecutorFactory.create_executor') as mock_create:
            mock_executor = MagicMock()
            mock_create.return_value = mock_executor

            mock_cm = MagicMock()
            mock_pm = MagicMock()

            result = create_executor(mock_cm, mock_pm)

            assert result == mock_executor
            mock_create.assert_called_once_with(mock_cm, mock_pm)

    def test_run_command_function_with_defaults(self):
        """Test run_command convenience function with defaults."""
        with patch('hagent.inou.executor.create_executor') as mock_create:
            with patch('hagent.inou.executor.PathManager') as mock_pm_class:
                mock_executor = MagicMock()
                mock_executor.run_cmd.return_value = (0, 'output', 'error')
                mock_create.return_value = mock_executor

                mock_pm = MagicMock()
                mock_pm.repo_dir = Path('/test/repo')
                mock_pm_class.return_value = mock_pm

                result = run_cmd('echo test')

                assert result == (0, 'output', 'error')
                mock_executor.run_cmd.assert_called_once_with('echo test', '/test/repo', {}, False)

    def test_run_command_function_with_params(self):
        """Test run_command convenience function with all parameters."""
        with patch('hagent.inou.executor.create_executor') as mock_create:
            mock_executor = MagicMock()
            mock_executor.run_cmd.return_value = (0, 'output', 'error')
            mock_create.return_value = mock_executor

            mock_cm = MagicMock()
            mock_pm = MagicMock()
            env = {'TEST': 'value'}

            result = run_cmd(
                'echo test',
                cwd='/test/dir',
                env=env,
                quiet=True,
                container_manager=mock_cm,
                path_manager=mock_pm,
            )

            assert result == (0, 'output', 'error')
            mock_create.assert_called_once_with(mock_cm, mock_pm)
            mock_executor.run_cmd.assert_called_once_with('echo test', '/test/dir', env, True)
