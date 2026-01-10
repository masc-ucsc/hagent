"""
Tests for ContainerManager

Tests Docker container lifecycle management, mount point configuration,
environment variable injection, and workspace validation.
"""

import os
from unittest.mock import MagicMock, patch
import pytest

from hagent.inou.container_manager import ContainerManager
from hagent.inou.path_manager import PathManager


@pytest.fixture(autouse=True)
def reset_docker_state():
    """Reset global Docker state before each test."""
    import hagent.inou.container_manager as cm

    cm._docker_workspace_validated = False
    yield
    # Reset again after test
    cm._docker_workspace_validated = False


@pytest.fixture
def container_manager_with_cleanup():
    """
    Pytest fixture that creates a ContainerManager and ensures cleanup.
    Use this for tests that actually create containers to prevent docker container leaks.
    """
    managers = []

    def create_manager(*args, **kwargs):
        manager = ContainerManager(*args, **kwargs)
        managers.append(manager)
        return manager

    yield create_manager

    # Cleanup all created managers
    for manager in managers:
        try:
            manager.cleanup()
        except Exception as e:
            print(f'Warning: Failed to cleanup container manager: {e}')


@pytest.fixture(scope='function')
def setup_local_directory(tmp_path):
    """
    Setup unique test directory structure for each test.
    Creates a temporary directory structure:
    - <tmp_path>/repo (minimal test directory)
    - <tmp_path>/build (empty directory)
    - <tmp_path>/cache (empty directory)
    """
    # Use tmp_path for test isolation
    repo_dir = tmp_path / 'repo'
    build_dir = tmp_path / 'build'
    cache_dir = tmp_path / 'cache'

    # Create directories
    repo_dir.mkdir(exist_ok=True)
    build_dir.mkdir(exist_ok=True)
    cache_dir.mkdir(exist_ok=True)

    # Create minimal test file in repo
    (repo_dir / 'README.md').write_text('# Test Repository\n')

    # Create additional test directories
    (tmp_path / 'extra').mkdir(exist_ok=True)
    (tmp_path / 'test_path').mkdir(exist_ok=True)

    return {'local_dir': tmp_path, 'repo_dir': repo_dir, 'build_dir': build_dir, 'cache_dir': cache_dir}


class TestContainerManager:
    """Test ContainerManager functionality."""

    def test_initialization(self):
        """Test ContainerManager initialization."""
        with patch('hagent.inou.container_manager.PathManager') as mock_get_pm:
            with patch.object(ContainerManager, '_initialize_docker_client'):
                mock_pm = MagicMock()
                mock_get_pm.return_value = mock_pm

                manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                assert manager.image == 'mascucsc/hagent-simplechisel:2026.01'
                assert manager.path_manager == mock_pm
                assert manager._workdir == '/code/workspace/repo'
                mock_get_pm.assert_called_once()

    def test_initialization_uses_singleton(self):
        """Test ContainerManager initialization uses singleton PathManager."""
        with patch('hagent.inou.container_manager.PathManager') as mock_get_pm:
            mock_pm = MagicMock()
            mock_get_pm.return_value = mock_pm

            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                assert manager.image == 'mascucsc/hagent-simplechisel:2026.01'
                assert manager.path_manager == mock_pm
                mock_get_pm.assert_called_once()

    @patch('docker.from_env')
    def test_initialize_docker_client_success(self, mock_from_env):
        """Test successful Docker client initialization."""
        mock_client = MagicMock()
        mock_client.ping.return_value = True
        mock_from_env.return_value = mock_client

        with patch('hagent.inou.container_manager.PathManager'):
            manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

            assert manager.client == mock_client
            mock_from_env.assert_called_once()
            mock_client.ping.assert_called_once()

    @patch('docker.from_env', side_effect=Exception('Docker not available'))
    @patch('os.path.exists', return_value=True)
    @patch('docker.DockerClient')
    def test_initialize_docker_client_fallback(self, mock_docker_client, mock_exists, mock_from_env):
        """Test Docker client initialization with fallback to socket paths."""
        mock_client = MagicMock()
        mock_client.ping.return_value = True
        mock_docker_client.return_value = mock_client

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_get_docker_socket_paths', return_value=['/test/socket']):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                assert manager.client == mock_client
                mock_docker_client.assert_called_once_with(base_url='unix:///test/socket')

    @patch('docker.from_env', side_effect=Exception('Docker not available'))
    @patch('os.path.exists', return_value=False)
    def test_initialize_docker_client_failure(self, mock_exists, mock_from_env):
        """Test Docker client initialization failure."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_get_docker_socket_paths', return_value=['/test/socket']):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')
                assert manager.get_error(), 'Should have error message'
                assert 'Docker client initialization failed' in manager.get_error()

    def test_get_docker_socket_paths_darwin(self):
        """Test Docker socket path detection on macOS."""
        with patch('platform.system', return_value='Darwin'):
            with patch('os.getenv', return_value='testuser'):
                with patch('hagent.inou.container_manager.PathManager'):
                    with patch.object(ContainerManager, '_initialize_docker_client'):
                        manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                        paths = manager._get_docker_socket_paths()

                        assert '/Users/testuser/.colima/default/docker.sock' in paths
                        assert '/Users/testuser/.docker/run/docker.sock' in paths
                        assert '/var/run/docker.sock' in paths

    def test_get_docker_socket_paths_linux(self):
        """Test Docker socket path detection on Linux."""
        with patch('platform.system', return_value='Linux'):
            with patch('os.getuid', return_value=1000):
                with patch('hagent.inou.container_manager.PathManager'):
                    with patch.object(ContainerManager, '_initialize_docker_client'):
                        manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                        paths = manager._get_docker_socket_paths()

                        assert '/var/run/docker.sock' in paths
                        assert '/run/user/1000/docker.sock' in paths

    def test_get_docker_info_connected(self):
        """Test _get_docker_info when client is connected."""
        mock_client = MagicMock()
        mock_client.info.return_value = {'OSType': 'linux', 'Architecture': 'x86_64'}
        mock_client.version.return_value = {'Version': '20.10.0', 'ApiVersion': '1.41'}

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')
                manager.client = mock_client

                info = manager._get_docker_info()

                assert info['status'] == 'CONNECTED'
                assert info['docker_version'] == '20.10.0'
                assert info['platform'] == 'linux'

    def test_get_docker_info_not_connected(self):
        """Test _get_docker_info when client is not connected."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')
                manager.client = None

                info = manager._get_docker_info()

                assert info['status'] == 'ERROR'
                assert 'Docker client not initialized' in info['message']

    def test_get_image_user_removed(self):
        """Test that _get_image_user method was removed in root-based approach."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                # Verify the method no longer exists - this is expected in root-based approach
                assert not hasattr(manager, '_get_image_user')

    def test_docker_workspace_validation_success(self):
        """Test Docker workspace validation success using new centralized approach."""
        mock_container = MagicMock()
        # Mock successful exec_run calls for all workspace directories
        # Note: The number of calls depends on whether HAGENT_PRIVATE_DIR is set
        # We'll return success for any directory check
        mock_container.exec_run.return_value = MagicMock(exit_code=0)
        mock_container.reload.return_value = None
        mock_container.status = 'running'
        mock_container.attrs = {'State': {'Status': 'running', 'Health': None}}

        from hagent.inou.container_manager import _validate_docker_workspace

        # Ensure HAGENT_PRIVATE_DIR is not set for this test to have consistent behavior
        env_vars = {'HAGENT_DOCKER': 'test-image:latest'}
        with patch.dict('os.environ', env_vars, clear=False):
            if 'HAGENT_PRIVATE_DIR' in os.environ:
                del os.environ['HAGENT_PRIVATE_DIR']
            result = _validate_docker_workspace(mock_container)
            assert result is True

    def test_docker_workspace_validation_failure(self):
        """Test Docker workspace validation failure using new centralized approach."""
        mock_container = MagicMock()
        # Mock failure on second directory check
        mock_container.exec_run.side_effect = [
            MagicMock(exit_code=0),  # /code/workspace exists
            MagicMock(exit_code=1),  # /code/workspace/repo fails
        ]
        mock_container.reload.return_value = None
        mock_container.status = 'running'
        mock_container.attrs = {'State': {'Status': 'running', 'Health': None}}

        from hagent.inou.container_manager import _validate_docker_workspace

        with patch.dict('os.environ', {'HAGENT_DOCKER': 'test-image:latest'}):
            result = _validate_docker_workspace(mock_container)
            assert result is False

    def test_setup_mount_points(self, setup_local_directory):
        """Test setup of standard mount points."""
        local_dirs = setup_local_directory

        # Create a real PathManager with test environment
        # Use PathManager.configured() for clean test isolation
        with PathManager.configured(
            repo_dir=str(local_dirs['repo_dir']),
            build_dir=str(local_dirs['build_dir']),
            cache_dir=str(local_dirs['cache_dir']),
        ):
            mock_pm = PathManager()

            with patch.object(ContainerManager, '_initialize_docker_client'):
                with patch('hagent.inou.container_manager.PathManager', return_value=mock_pm):
                    manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                with patch('docker.types.Mount') as mock_mount:
                    mock_mount_obj = MagicMock()
                    mock_mount.return_value = mock_mount_obj

                    mounts = manager._setup_mount_points()

                    if mock_pm.is_local_mode():
                        # Local execution mode: no host mounts needed for ad-hoc Docker runs
                        assert mounts == []
                        mock_mount.assert_not_called()
                    else:
                        expected_mounts = 1  # /code/hagent
                        for attr in ('cache_mount_dir', 'repo_mount_dir', 'build_mount_dir', 'tech_mount_dir'):
                            if getattr(mock_pm, attr) is not None:
                                expected_mounts += 1

                        assert len(mounts) == expected_mounts
                        assert mock_mount.call_count == expected_mounts

                        # Verify mount calls
                        calls = mock_mount.call_args_list
                        mount_targets = [call[1]['target'] for call in calls]
                        assert '/code/hagent' in mount_targets
                        if mock_pm.cache_mount_dir is not None:
                            assert '/code/workspace/cache' in mount_targets
                        if mock_pm.repo_mount_dir is not None:
                            assert '/code/workspace/repo' in mount_targets
                        if mock_pm.build_mount_dir is not None:
                            assert '/code/workspace/build' in mount_targets
                        if mock_pm.tech_mount_dir is not None:
                            assert '/code/workspace/tech' in mount_targets

    @patch('docker.types.Mount')
    def test_setup_success(self, mock_mount, setup_local_directory):
        """Test successful container setup."""
        local_dirs = setup_local_directory

        # Create a real PathManager with test environment
        with patch.dict('os.environ', {'HAGENT_CACHE_DIR': str(local_dirs['cache_dir'])}):
            mock_pm = PathManager()

        mock_client = MagicMock()
        mock_image = MagicMock()
        mock_client.images.get.return_value = mock_image
        mock_container = MagicMock()

        # Align side effects with current root-based implementation:
        # - workspace validation handled separately; we'll stub it to True
        # - mkdir workdir
        # - permission fixes: test -d + chmod for repo/build/cache
        # - bash existence test
        mock_container.exec_run.side_effect = [
            MagicMock(exit_code=0),  # mkdir -p workdir
            MagicMock(exit_code=0),  # test -d /code/workspace/repo
            MagicMock(exit_code=0),  # chmod 755 repo
            MagicMock(exit_code=0),  # test -d /code/workspace/build
            MagicMock(exit_code=0),  # chmod 755 build
            MagicMock(exit_code=0),  # test -d /code/workspace/cache
            MagicMock(exit_code=0),  # chmod 755 cache
            MagicMock(exit_code=0),  # test -x /bin/bash
        ]
        mock_container.reload.return_value = None
        mock_container.status = 'running'
        mock_container.start.return_value = None
        mock_client.containers.create.return_value = mock_container

        with patch.object(ContainerManager, '_initialize_docker_client'):
            with patch('hagent.inou.container_manager.PathManager', return_value=mock_pm):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')
            manager.client = mock_client
            # Avoid dependence on global workspace flag by stubbing validation
            with patch.object(ContainerManager, '_setup_docker_workspace_if_needed', return_value=True):
                result = manager.setup()

            assert result is True
            assert manager.container == mock_container
            assert manager._has_bash is True

            # Verify container creation
            mock_client.containers.create.assert_called_once()
            mock_container.start.assert_called_once()

    def test_setup_image_pull_required(self, setup_local_directory):
        """Test setup when image needs to be pulled."""
        local_dirs = setup_local_directory

        # Keep the environment variables patched for the entire test
        with patch.dict('os.environ', {'HAGENT_CACHE_DIR': str(local_dirs['cache_dir'])}):
            mock_pm = PathManager()

            mock_client = MagicMock()
            from docker.errors import ImageNotFound

            mock_client.images.get.side_effect = [
                ImageNotFound('ImageNotFound'),  # First call fails
                MagicMock(),  # After pull succeeds
            ]
            mock_container = MagicMock()

            def exec_run_side_effect(command, *args, **kwargs):
                """Return deterministic mocks irrespective of call ordering."""
                cmd = kwargs.get('cmd', command)
                if isinstance(cmd, (list, tuple)):
                    cmd_str = ' '.join(cmd)
                else:
                    cmd_str = cmd

                if cmd_str.startswith('test -x /bin/bash'):
                    return MagicMock(exit_code=1, output=b'')

                if cmd_str.startswith('ls -la'):
                    return MagicMock(exit_code=0, output=b'')

                # Default successful command (workspace validation, mkdir, etc.)
                return MagicMock(exit_code=0, output=b'')

            mock_container.exec_run.side_effect = exec_run_side_effect
            mock_container.reload.return_value = None
            mock_container.status = 'running'
            mock_container.attrs = {'State': {'Status': 'running', 'Health': None}}
            mock_container.start.return_value = None
            mock_client.containers.create.return_value = mock_container

            with patch.object(ContainerManager, '_initialize_docker_client'):
                with patch.object(ContainerManager, '_pull_image_with_progress') as mock_pull:
                    with patch('hagent.inou.container_manager.PathManager', return_value=mock_pm):
                        manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')
                        manager.client = mock_client

                        result = manager.setup()

                        assert result is True
                        assert manager._has_bash is False  # bash test failed
                        mock_pull.assert_called_once_with('mascucsc/hagent-simplechisel:2026.01')

    def test_setup_pull_credential_error(self, setup_local_directory):
        """Test setup with credential error during pull."""
        local_dirs = setup_local_directory

        # Create a real PathManager with test environment
        with patch.dict('os.environ', {'HAGENT_CACHE_DIR': str(local_dirs['cache_dir'])}):
            mock_pm = PathManager()

        mock_client = MagicMock()
        from docker.errors import ImageNotFound

        mock_client.images.get.side_effect = ImageNotFound('ImageNotFound')

        with patch.object(ContainerManager, '_initialize_docker_client'):
            with patch.object(ContainerManager, '_pull_image_with_progress') as mock_pull:
                from docker.errors import APIError

                mock_pull.side_effect = APIError('credential issue detected')

                with patch('hagent.inou.container_manager.PathManager', return_value=mock_pm):
                    manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')
                    manager.client = mock_client

                    result = manager.setup()

                assert result is False

    def test_run_streaming_output(self):
        """Test running command with streaming output."""
        mock_container = MagicMock()
        mock_client = MagicMock()

        # Mock exec_create and exec_start for streaming
        mock_client.api.exec_create.return_value = {'Id': 'exec123'}
        mock_client.api.exec_start.return_value = [
            (b'line1\n', None),
            (None, b'error1\n'),
            (b'line2\n', None),
        ]
        mock_client.api.exec_inspect.return_value = {'ExitCode': 0}

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')
                manager.container = mock_container
                manager.client = mock_client
                manager._has_bash = True

                with patch('builtins.print') as mock_print:
                    exit_code, stdout, stderr = manager.run_cmd('echo test', quiet=False)

                assert exit_code == 0
                assert 'line1\n' in stdout
                assert 'line2\n' in stdout
                assert 'error1\n' in stderr

                # Verify streaming output was printed
                mock_print.assert_any_call('hagent-simplechisel:2026.01:run: line1')

    def test_run_no_container(self):
        """Test running command without container setup."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                exit_code, stdout, stderr = manager.run_cmd('echo test')
                assert exit_code == -1, 'Should return -1 exit code when no container'
                assert 'Container not set up' in manager.get_error()

    def test_image_checkpoint(self):
        """Test creating image checkpoint."""
        mock_container = MagicMock()
        mock_image = MagicMock()
        mock_image.id = 'img123'
        mock_container.commit.return_value = mock_image

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                with patch.object(ContainerManager, '_get_image_config', return_value={'Cmd': ['bash']}):
                    manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')
                    manager.container = mock_container
                    manager._has_bash = True

                    with patch('builtins.print'):
                        checkpoint_name = manager.image_checkpoint('test_checkpoint')

                    assert checkpoint_name == 'mascucsc/hagent-simplechisel:2026.01_checkpoint_test_checkpoint'
                    mock_container.commit.assert_called_once()

    def test_cleanup(self):
        """Test container cleanup."""
        mock_container = MagicMock()
        mock_container.status = 'running'  # Set status to running so kill() gets called
        mock_ref_container = MagicMock()
        mock_ref_container.status = 'running'  # Set status to running so kill() gets called

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                with patch.object(ContainerManager, '_cleanup_anonymous_checkpoints') as mock_cleanup_checkpoints:
                    manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')
                    manager.container = mock_container
                    manager._reference_container = mock_ref_container

                    manager.cleanup()

                    mock_container.kill.assert_called_once()
                    mock_container.remove.assert_called_once()
                    mock_ref_container.kill.assert_called_once()
                    mock_ref_container.remove.assert_called_once()
                    # cleanup may be called multiple times (explicit call + __del__)
                    assert mock_cleanup_checkpoints.call_count >= 1

                    assert manager.container is None
                    assert manager._reference_container is None

    def test_context_manager(self):
        """Test ContainerManager as context manager."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                with patch.object(ContainerManager, 'cleanup') as mock_cleanup:
                    with ContainerManager('mascucsc/hagent-simplechisel:2026.01') as manager:
                        assert isinstance(manager, ContainerManager)

                    mock_cleanup.assert_called_once()

    def test_destructor_cleanup(self):
        """Test cleanup on object destruction."""
        import gc

        # Force garbage collection to ensure previous test instances are cleaned up
        gc.collect()

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                with patch.object(ContainerManager, 'cleanup') as mock_cleanup:
                    manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                    # Reset mock call count to ensure we only count calls from this instance
                    mock_cleanup.reset_mock()

                    del manager

                    # Force garbage collection to trigger __del__ immediately
                    gc.collect()

                    mock_cleanup.assert_called_once()

    def test_setup_mount_points_relative_paths(self, setup_local_directory):
        """Test setup of mount points with relative paths."""
        # Create a real PathManager with test environment using relative paths
        # Use PathManager.configured() for clean test isolation
        with PathManager.configured(
            repo_dir='output/local/repo',
            build_dir='output/local/build',
            cache_dir='output/local/cache',
        ):
            mock_pm = PathManager()

            with patch.object(ContainerManager, '_initialize_docker_client'):
                with patch('hagent.inou.container_manager.PathManager', return_value=mock_pm):
                    manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                with patch('docker.types.Mount') as mock_mount:
                    mock_mount_obj = MagicMock()
                    mock_mount.return_value = mock_mount_obj

                    mounts = manager._setup_mount_points()

                    if mock_pm.is_local_mode():
                        assert mounts == []
                        mock_mount.assert_not_called()
                    else:
                        expected_mounts = 1  # /code/hagent
                        for attr in ('cache_mount_dir', 'repo_mount_dir', 'build_mount_dir', 'tech_mount_dir'):
                            if getattr(mock_pm, attr) is not None:
                                expected_mounts += 1

                        assert len(mounts) == expected_mounts
                        assert mock_mount.call_count == expected_mounts

                        calls = mock_mount.call_args_list
                        mount_targets = [call[1]['target'] for call in calls]
                        assert '/code/hagent' in mount_targets
                        if mock_pm.cache_mount_dir is not None:
                            assert '/code/workspace/cache' in mount_targets
                        if mock_pm.repo_mount_dir is not None:
                            assert '/code/workspace/repo' in mount_targets
                        if mock_pm.build_mount_dir is not None:
                            assert '/code/workspace/build' in mount_targets

    def test_setup_mount_points_absolute_paths(self, setup_local_directory):
        """Test setup of mount points with absolute paths."""
        local_dirs = setup_local_directory

        # Create a real PathManager with test environment
        # Use PathManager.configured() for clean test isolation
        with PathManager.configured(
            repo_dir=str(local_dirs['repo_dir'].resolve()),
            build_dir=str(local_dirs['build_dir'].resolve()),
            cache_dir=str(local_dirs['cache_dir'].resolve()),
        ):
            mock_pm = PathManager()

            with patch.object(ContainerManager, '_initialize_docker_client'):
                with patch('hagent.inou.container_manager.PathManager', return_value=mock_pm):
                    manager = ContainerManager('mascucsc/hagent-simplechisel:2026.01')

                with patch('docker.types.Mount') as mock_mount:
                    mock_mount_obj = MagicMock()
                    mock_mount.return_value = mock_mount_obj

                    mounts = manager._setup_mount_points()

                    if mock_pm.is_local_mode():
                        assert mounts == []
                        mock_mount.assert_not_called()
                    else:
                        expected_mounts = 1  # /code/hagent
                        for attr in ('cache_mount_dir', 'repo_mount_dir', 'build_mount_dir', 'tech_mount_dir'):
                            if getattr(mock_pm, attr) is not None:
                                expected_mounts += 1

                        assert len(mounts) == expected_mounts
                        assert mock_mount.call_count == expected_mounts

                        calls = mock_mount.call_args_list
                        mount_targets = [call[1]['target'] for call in calls]
                        assert '/code/hagent' in mount_targets
                        if mock_pm.cache_mount_dir is not None:
                            assert '/code/workspace/cache' in mount_targets
                        if mock_pm.repo_mount_dir is not None:
                            assert '/code/workspace/repo' in mount_targets
                        if mock_pm.build_mount_dir is not None:
                            assert '/code/workspace/build' in mount_targets

    @pytest.mark.skip(reason='Docker container setup fails with temporary directory mount issues')
    def test_mcp_build_script_execution(self, container_manager_with_cleanup, setup_local_directory, test_output_dir):
        """Test that mcp_build.py script can be executed directly inside the container."""
        local_dirs = setup_local_directory

        # Create container_manager_cache directory for persistent uv cache across test runs
        # This speeds up successive runs significantly by avoiding uv sync on each run
        container_cache_dir = test_output_dir / 'container_manager_cache'
        container_cache_dir.mkdir(parents=True, exist_ok=True)

        # Create a real PathManager with test environment
        # Use container_manager_cache for faster successive test runs
        with patch.dict(
            'os.environ',
            {
                'HAGENT_REPO_DIR': str(local_dirs['repo_dir']),
                'HAGENT_BUILD_DIR': str(local_dirs['build_dir']),
                'HAGENT_CACHE_DIR': str(container_cache_dir),
            },
        ):
            # Create container manager using the fixture for cleanup
            manager = container_manager_with_cleanup('mascucsc/hagent-simplechisel:2026.01')

            # Setup the container
            setup_result = manager.setup()
            assert setup_result is True, f'Container setup failed: {manager.get_error()}'

            # Run the mcp_build.py script directly to test the polyglot wrapper
            # The wrapper should automatically set UV_PROJECT_ENVIRONMENT=/code/workspace/cache/.venv
            # when /code/workspace/cache exists (Docker mode detection)
            exit_code, stdout, stderr = manager.run_cmd(
                '/code/hagent/hagent/mcp/mcp_build.py --help',
                quiet=True,
            )

            # Verify the script executed successfully
            assert exit_code == 0, f'Script execution failed with exit code {exit_code}\nstdout: {stdout}\nstderr: {stderr}'

            # Verify the expected usage message is in the output
            assert 'usage: mcp_build.py' in stdout, f'Expected usage message not found in stdout: {stdout}'
