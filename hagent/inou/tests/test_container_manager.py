"""
Tests for ContainerManager

Tests Docker container lifecycle management, mount point configuration,
environment variable injection, and workspace validation.
"""

import subprocess
from pathlib import Path
from unittest.mock import patch, MagicMock
import pytest

from hagent.inou.container_manager import ContainerManager
from hagent.inou.path_manager import PathManager


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


@pytest.fixture(scope='session')
def setup_local_directory():
    """
    Setup ./output/local directory structure for testing.
    Creates the directory structure if it doesn't exist:
    - ./output/local/repo (with simplechisel git clone)
    - ./output/local/build (empty directory)
    - ./output/local/cache (empty directory)
    """
    local_dir = Path('./output/local')
    repo_dir = local_dir / 'repo'
    build_dir = local_dir / 'build'
    cache_dir = local_dir / 'cache'

    # Create local directory if it doesn't exist
    if not local_dir.exists():
        print(f'Creating {local_dir} directory...')
        local_dir.mkdir(parents=True, exist_ok=True)

    # Setup repo directory with git clone if it doesn't exist or is empty
    if not repo_dir.exists() or not any(repo_dir.iterdir()):
        print(f'Setting up {repo_dir} with simplechisel repository... WARNING. THIS CAN CREATE A RACY CONDITION')

        # Clone the repository
        try:
            subprocess.run(
                ['git', 'clone', 'https://github.com/masc-ucsc/simplechisel.git', str(repo_dir)],
                check=True,
                capture_output=True,
                text=True,
            )
            print(f'Successfully cloned simplechisel to {repo_dir}')
        except subprocess.CalledProcessError as e:
            print(f'Warning: Failed to clone repository: {e}')
            # Create a basic directory structure as fallback
            repo_dir.mkdir(exist_ok=True)
            (repo_dir / 'README.md').write_text('# Test Repository\n')

    # Create build directory
    if not build_dir.exists():
        print(f'Creating {build_dir} directory...')
        build_dir.mkdir(exist_ok=True)

    # Create cache directory
    if not cache_dir.exists():
        print(f'Creating {cache_dir} directory...')
        cache_dir.mkdir(exist_ok=True)

    # Create additional test directories
    (local_dir / 'extra').mkdir(exist_ok=True)
    (local_dir / 'test_path').mkdir(exist_ok=True)

    return {'local_dir': local_dir, 'repo_dir': repo_dir, 'build_dir': build_dir, 'cache_dir': cache_dir}


class TestContainerManager:
    """Test ContainerManager functionality."""

    def test_initialization(self):
        """Test ContainerManager initialization."""
        with patch('hagent.inou.container_manager.PathManager') as mock_pm_class:
            with patch.object(ContainerManager, '_initialize_docker_client'):
                mock_pm = MagicMock()
                mock_pm_class.return_value = mock_pm

                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')

                assert manager.image == 'mascucsc/hagent-simplechisel:2025.08'
                assert manager.path_manager == mock_pm
                assert manager._workdir == '/code/workspace/repo'
                mock_pm_class.assert_called_once()

    def test_initialization_with_path_manager(self):
        """Test ContainerManager initialization with provided path manager."""
        mock_pm = MagicMock()

        with patch.object(ContainerManager, '_initialize_docker_client'):
            manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08', mock_pm)

            assert manager.image == 'mascucsc/hagent-simplechisel:2025.08'
            assert manager.path_manager == mock_pm

    @patch('docker.from_env')
    def test_initialize_docker_client_success(self, mock_from_env):
        """Test successful Docker client initialization."""
        mock_client = MagicMock()
        mock_client.ping.return_value = True
        mock_from_env.return_value = mock_client

        with patch('hagent.inou.container_manager.PathManager'):
            manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')

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
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')

                assert manager.client == mock_client
                mock_docker_client.assert_called_once_with(base_url='unix:///test/socket')

    @patch('docker.from_env', side_effect=Exception('Docker not available'))
    @patch('os.path.exists', return_value=False)
    def test_initialize_docker_client_failure(self, mock_exists, mock_from_env):
        """Test Docker client initialization failure."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_get_docker_socket_paths', return_value=['/test/socket']):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                assert manager.get_error(), 'Should have error message'
                assert 'Docker client initialization failed' in manager.get_error()

    def test_get_docker_socket_paths_darwin(self):
        """Test Docker socket path detection on macOS."""
        with patch('platform.system', return_value='Darwin'):
            with patch('os.getenv', return_value='testuser'):
                with patch('hagent.inou.container_manager.PathManager'):
                    with patch.object(ContainerManager, '_initialize_docker_client'):
                        manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')

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
                        manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')

                        paths = manager._get_docker_socket_paths()

                        assert '/var/run/docker.sock' in paths
                        assert '/run/user/1000/docker.sock' in paths

    def test_get_docker_info_connected(self):
        """Test get_docker_info when client is connected."""
        mock_client = MagicMock()
        mock_client.info.return_value = {'OSType': 'linux', 'Architecture': 'x86_64'}
        mock_client.version.return_value = {'Version': '20.10.0', 'ApiVersion': '1.41'}

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                manager.client = mock_client

                info = manager.get_docker_info()

                assert info['status'] == 'CONNECTED'
                assert info['docker_version'] == '20.10.0'
                assert info['platform'] == 'linux'

    def test_get_docker_info_not_connected(self):
        """Test get_docker_info when client is not connected."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                manager.client = None

                info = manager.get_docker_info()

                assert info['status'] == 'ERROR'
                assert 'Docker client not initialized' in info['message']

    def test_get_image_user(self):
        """Test getting image user configuration."""
        mock_client = MagicMock()
        mock_image = MagicMock()
        mock_image.attrs = {'Config': {'User': 'testuser'}}
        mock_client.images.get.return_value = mock_image

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                manager.client = mock_client

                user = manager._get_image_user()
                assert user == 'testuser'

                # Test caching
                user2 = manager._get_image_user()
                assert user2 == 'testuser'
                mock_client.images.get.assert_called_once()

    def test_validate_workspace_directory_success(self):
        """Test workspace directory validation success."""
        mock_container = MagicMock()
        mock_container.exec_run.return_value = MagicMock(exit_code=0)

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                manager.container = mock_container

                result = manager._validate_workspace_directory()

                assert result is True
                mock_container.exec_run.assert_called_once_with('test -d /code/workspace')

    def test_validate_workspace_directory_failure(self):
        """Test workspace directory validation failure."""
        mock_container = MagicMock()
        mock_container.exec_run.return_value = MagicMock(exit_code=1)

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                manager.container = mock_container

                result = manager._validate_workspace_directory()
                assert result is False, 'Should return False on validation failure'
                assert 'does not have /code/workspace/ directory' in manager.get_error()

    def test_setup_container_environment(self):
        """Test container environment variable setup."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')

                env_vars = manager._setup_container_environment()

                expected = {
                    'HAGENT_EXECUTION_MODE': 'docker',
                    'HAGENT_REPO_DIR': '/code/workspace/repo',
                    'HAGENT_BUILD_DIR': '/code/workspace/build',
                    'HAGENT_CACHE_DIR': '/code/workspace/cache',
                    'UV_PROJECT_ENVIRONMENT': '/code/workspace/cache/venv',
                }

                # Check that all expected variables are present with correct values
                for key, value in expected.items():
                    assert key in env_vars, f"Expected environment variable '{key}' not found"
                    assert env_vars[key] == value, f'Expected {key}={value}, got {env_vars[key]}'

    def test_setup_mount_points(self, setup_local_directory):
        """Test setup of standard mount points."""
        local_dirs = setup_local_directory

        # Create a real PathManager with test environment
        with patch.dict(
            'os.environ',
            {
                'HAGENT_EXECUTION_MODE': 'docker',
                'HAGENT_REPO_DIR': str(local_dirs['repo_dir']),
                'HAGENT_BUILD_DIR': str(local_dirs['build_dir']),
                'HAGENT_CACHE_DIR': str(local_dirs['cache_dir']),
            },
        ):
            mock_pm = PathManager()

        with patch.object(ContainerManager, '_initialize_docker_client'):
            manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08', mock_pm)

            with patch('docker.types.Mount') as mock_mount:
                mock_mount_obj = MagicMock()
                mock_mount.return_value = mock_mount_obj

                mounts = manager._setup_mount_points()

                # Should have 3 mounts (cache, repo, build)
                assert len(mounts) == 3
                assert mock_mount.call_count == 3

                # Verify mount calls
                calls = mock_mount.call_args_list
                mount_targets = [call[1]['target'] for call in calls]
                assert '/code/workspace/cache' in mount_targets
                assert '/code/workspace/repo' in mount_targets
                assert '/code/workspace/build' in mount_targets

    def test_setup_mount_points_with_additional_mounts(self, setup_local_directory):
        """Test setup with additional mounts."""
        local_dirs = setup_local_directory

        # Create a real PathManager with test environment (missing build_dir)
        with patch.dict(
            'os.environ',
            {
                'HAGENT_EXECUTION_MODE': 'docker',
                'HAGENT_REPO_DIR': str(local_dirs['repo_dir']),
                'HAGENT_CACHE_DIR': str(local_dirs['cache_dir']),
                # Note: HAGENT_BUILD_DIR is intentionally omitted
            },
        ):
            mock_pm = PathManager()

        with patch.object(ContainerManager, '_initialize_docker_client'):
            manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08', mock_pm)
            manager._mounts = [{'source': str(local_dirs['local_dir'] / 'extra'), 'target': '/container/extra'}]

            with patch('docker.types.Mount') as mock_mount:
                manager._setup_mount_points()

                # Should have 3 mounts (cache, repo, extra)
                assert mock_mount.call_count == 3

    def test_add_mount_before_setup(self, setup_local_directory):
        """Test adding mount before container setup."""
        local_dirs = setup_local_directory
        test_path = str(local_dirs['local_dir'] / 'test_path')

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')

                result = manager.add_mount(test_path, '/container/path')

                assert result is True
                assert len(manager._mounts) == 1
                assert manager._mounts[0]['source'] == test_path
                assert manager._mounts[0]['target'] == '/container/path'

    def test_add_mount_after_setup(self, setup_local_directory):
        """Test adding mount after container setup fails."""
        local_dirs = setup_local_directory
        test_path = str(local_dirs['local_dir'] / 'test_path')

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                manager.container = MagicMock()  # Simulate setup

                result = manager.add_mount(test_path, '/container/path')
                assert result is False, 'Should return False when called after setup'
                assert 'add_mount must be called before setup' in manager.get_error()

    @patch('docker.types.Mount')
    def test_setup_success(self, mock_mount, setup_local_directory):
        """Test successful container setup."""
        local_dirs = setup_local_directory

        # Create a real PathManager with test environment
        with patch.dict('os.environ', {'HAGENT_EXECUTION_MODE': 'docker', 'HAGENT_CACHE_DIR': str(local_dirs['cache_dir'])}):
            mock_pm = PathManager()

        mock_client = MagicMock()
        mock_image = MagicMock()
        mock_client.images.get.return_value = mock_image
        mock_container = MagicMock()
        # Mock UID/GID output for permission fixing
        uid_result = MagicMock(exit_code=0)
        uid_result.output.decode.return_value = '9001'
        gid_result = MagicMock(exit_code=0)
        gid_result.output.decode.return_value = '9001'

        mock_container.exec_run.side_effect = [
            MagicMock(exit_code=0),  # workspace validation
            MagicMock(exit_code=0),  # mkdir workdir
            uid_result,  # id -u for permission fix
            gid_result,  # id -g for permission fix
            MagicMock(exit_code=0),  # test -d /code/workspace/repo
            MagicMock(exit_code=0),  # chown repo directory
            MagicMock(exit_code=0),  # test -d /code/workspace/build
            MagicMock(exit_code=0),  # chown build directory
            MagicMock(exit_code=0),  # test -d /code/workspace/cache
            MagicMock(exit_code=0),  # chown cache directory
            MagicMock(exit_code=0),  # bash test
        ]
        mock_client.containers.create.return_value = mock_container

        with patch.object(ContainerManager, '_initialize_docker_client'):
            manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08', mock_pm)
            manager.client = mock_client

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

        # Create a real PathManager with test environment
        with patch.dict('os.environ', {'HAGENT_EXECUTION_MODE': 'docker', 'HAGENT_CACHE_DIR': str(local_dirs['cache_dir'])}):
            mock_pm = PathManager()

        mock_client = MagicMock()
        from docker.errors import ImageNotFound

        mock_client.images.get.side_effect = [
            ImageNotFound('ImageNotFound'),  # First call fails
            MagicMock(),  # After pull succeeds
        ]
        mock_container = MagicMock()
        # Mock UID/GID output for permission fixing
        uid_result = MagicMock(exit_code=0)
        uid_result.output.decode.return_value = '9001'
        gid_result = MagicMock(exit_code=0)
        gid_result.output.decode.return_value = '9001'

        mock_container.exec_run.side_effect = [
            MagicMock(exit_code=0),  # workspace validation
            MagicMock(exit_code=0),  # mkdir workdir
            uid_result,  # id -u for permission fix
            gid_result,  # id -g for permission fix
            MagicMock(exit_code=0),  # test -d /code/workspace/repo
            MagicMock(exit_code=0),  # chown repo directory
            MagicMock(exit_code=0),  # test -d /code/workspace/build
            MagicMock(exit_code=0),  # chown build directory
            MagicMock(exit_code=0),  # test -d /code/workspace/cache
            MagicMock(exit_code=0),  # chown cache directory
            MagicMock(exit_code=1),  # bash test fails
        ]
        mock_client.containers.create.return_value = mock_container

        with patch.object(ContainerManager, '_initialize_docker_client'):
            with patch.object(ContainerManager, '_pull_image_with_progress') as mock_pull:
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08', mock_pm)
                manager.client = mock_client

                result = manager.setup()

                assert result is True
                assert manager._has_bash is False  # bash test failed
                mock_pull.assert_called_once_with('mascucsc/hagent-simplechisel:2025.08')

    def test_setup_pull_credential_error(self, setup_local_directory):
        """Test setup with credential error during pull."""
        local_dirs = setup_local_directory

        # Create a real PathManager with test environment
        with patch.dict('os.environ', {'HAGENT_EXECUTION_MODE': 'docker', 'HAGENT_CACHE_DIR': str(local_dirs['cache_dir'])}):
            mock_pm = PathManager()

        mock_client = MagicMock()
        from docker.errors import ImageNotFound

        mock_client.images.get.side_effect = ImageNotFound('ImageNotFound')

        with patch.object(ContainerManager, '_initialize_docker_client'):
            with patch.object(ContainerManager, '_pull_image_with_progress') as mock_pull:
                from docker.errors import APIError

                mock_pull.side_effect = APIError('credential issue detected')

                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08', mock_pm)
                manager.client = mock_client

                result = manager.setup()

                assert result is False

    def test_run_basic_command(self):
        """Test running basic command in container."""
        mock_container = MagicMock()
        mock_result = MagicMock()
        mock_result.exit_code = 0
        mock_result.output = (b'stdout output', b'stderr output')
        mock_container.exec_run.return_value = mock_result

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                manager.container = mock_container
                manager._has_bash = True

                exit_code, stdout, stderr = manager.run('echo test', quiet=True)

                assert exit_code == 0
                assert stdout == 'stdout output'
                assert stderr == 'stderr output'

                # Verify exec_run was called with bash
                mock_container.exec_run.assert_called_once()
                args, kwargs = mock_container.exec_run.call_args
                assert args[0] == ['/bin/bash', '--login', '-c', 'echo test']

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
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                manager.container = mock_container
                manager.client = mock_client
                manager._has_bash = True

                with patch('builtins.print') as mock_print:
                    exit_code, stdout, stderr = manager.run('echo test', quiet=False)

                assert exit_code == 0
                assert 'line1\n' in stdout
                assert 'line2\n' in stdout
                assert 'error1\n' in stderr

                # Verify streaming output was printed
                mock_print.assert_any_call('hagent-simplechisel:2025.08:run: line1')

    def test_run_with_config_sources(self):
        """Test running command with config sources."""
        mock_container = MagicMock()
        mock_result = MagicMock()
        mock_result.exit_code = 0
        mock_result.output = (b'output', b'')
        mock_container.exec_run.return_value = mock_result

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                manager.container = mock_container
                manager._has_bash = True

                manager.run('echo test', config_sources=['/etc/config1', '/etc/config2'], quiet=True)

                # Verify exec_run was called with sourced configs
                args, kwargs = mock_container.exec_run.call_args
                command = args[0][2]  # The -c argument
                assert "source '/etc/config1'" in command
                assert "source '/etc/config2'" in command
                assert 'echo test' in command

    def test_run_without_bash(self):
        """Test running command when bash is not available."""
        mock_container = MagicMock()
        mock_result = MagicMock()
        mock_result.exit_code = 0
        mock_result.output = (b'output', b'')
        mock_container.exec_run.return_value = mock_result

        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                manager.container = mock_container
                manager._has_bash = False

                manager.run('echo test', quiet=True)

                # Verify exec_run was called with sh
                args, kwargs = mock_container.exec_run.call_args
                assert args[0][0] == '/bin/sh'
                # Should include profile sourcing when no config sources
                command = args[0][2]
                assert 'source /etc/profile' in command

    def test_run_no_container(self):
        """Test running command without container setup."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')

                exit_code, stdout, stderr = manager.run('echo test')
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
                    manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                    manager.container = mock_container
                    manager._has_bash = True

                    with patch('builtins.print'):
                        checkpoint_name = manager.image_checkpoint('test_checkpoint')

                    assert checkpoint_name == 'mascucsc/hagent-simplechisel:2025.08_checkpoint_test_checkpoint'
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
                    manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                    manager.container = mock_container
                    manager._reference_container = mock_ref_container

                    manager.cleanup()

                    mock_container.kill.assert_called_once()
                    mock_container.remove.assert_called_once()
                    mock_ref_container.kill.assert_called_once()
                    mock_ref_container.remove.assert_called_once()
                    mock_cleanup_checkpoints.assert_called_once()

                    assert manager.container is None
                    assert manager._reference_container is None

    def test_context_manager(self):
        """Test ContainerManager as context manager."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                with patch.object(ContainerManager, 'cleanup') as mock_cleanup:
                    with ContainerManager('mascucsc/hagent-simplechisel:2025.08') as manager:
                        assert isinstance(manager, ContainerManager)

                    mock_cleanup.assert_called_once()

    def test_destructor_cleanup(self):
        """Test cleanup on object destruction."""
        with patch('hagent.inou.container_manager.PathManager'):
            with patch.object(ContainerManager, '_initialize_docker_client'):
                with patch.object(ContainerManager, 'cleanup') as mock_cleanup:
                    manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08')
                    del manager

                    mock_cleanup.assert_called_once()

    def test_setup_mount_points_relative_paths(self, setup_local_directory):
        """Test setup of mount points with relative paths."""
        # Create a real PathManager with test environment using relative paths
        with patch.dict(
            'os.environ',
            {
                'HAGENT_EXECUTION_MODE': 'docker',
                'HAGENT_REPO_DIR': 'output/local/repo',
                'HAGENT_BUILD_DIR': 'output/local/build',
                'HAGENT_CACHE_DIR': 'output/local/cache',
            },
        ):
            mock_pm = PathManager()

        with patch.object(ContainerManager, '_initialize_docker_client'):
            manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08', mock_pm)

            with patch('docker.types.Mount') as mock_mount:
                mock_mount_obj = MagicMock()
                mock_mount.return_value = mock_mount_obj

                mounts = manager._setup_mount_points()

                # Should have 3 mounts (cache, repo, build)
                assert len(mounts) == 3
                assert mock_mount.call_count == 3

                # Verify mount calls
                calls = mock_mount.call_args_list
                mount_targets = [call[1]['target'] for call in calls]
                assert '/code/workspace/cache' in mount_targets
                assert '/code/workspace/repo' in mount_targets
                assert '/code/workspace/build' in mount_targets

    def test_setup_mount_points_absolute_paths(self, setup_local_directory):
        """Test setup of mount points with absolute paths."""
        local_dirs = setup_local_directory

        # Create a real PathManager with test environment
        with patch.dict(
            'os.environ',
            {
                'HAGENT_EXECUTION_MODE': 'docker',
                'HAGENT_REPO_DIR': str(local_dirs['repo_dir'].resolve()),
                'HAGENT_BUILD_DIR': str(local_dirs['build_dir'].resolve()),
                'HAGENT_CACHE_DIR': str(local_dirs['cache_dir'].resolve()),
            },
        ):
            mock_pm = PathManager()

        with patch.object(ContainerManager, '_initialize_docker_client'):
            manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08', mock_pm)

            with patch('docker.types.Mount') as mock_mount:
                mock_mount_obj = MagicMock()
                mock_mount.return_value = mock_mount_obj

                mounts = manager._setup_mount_points()

                # Should have 3 mounts (cache, repo, build)
                assert len(mounts) == 3
                assert mock_mount.call_count == 3

                # Verify mount calls
                calls = mock_mount.call_args_list
                mount_targets = [call[1]['target'] for call in calls]
                assert '/code/workspace/cache' in mount_targets
                assert '/code/workspace/repo' in mount_targets
                assert '/code/workspace/build' in mount_targets
