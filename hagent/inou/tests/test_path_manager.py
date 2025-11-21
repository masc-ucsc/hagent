"""
Tests for PathManager

Tests path resolution, environment variable validation, and cache directory
structure creation for both local and Docker execution modes.
"""

import os
import tempfile
import pytest
from pathlib import Path
from unittest.mock import patch

from hagent.inou.path_manager import PathManager


class TestPathManager:
    """Test PathManager functionality."""

    @pytest.fixture(autouse=True)
    def reset_path_manager_state(self):
        """Reset PathManager state before and after each test.

        This test class specifically tests PathManager's initialization behavior,
        so we can't use PathManager.configured() - we need to test the singleton
        pattern directly. We reset the class variables directly.
        """
        # Save original state
        old_instance = PathManager._instance
        old_initialized = PathManager._initialized

        # Reset before test
        PathManager._instance = None
        PathManager._initialized = False

        yield

        # Reset after test
        PathManager._instance = old_instance
        PathManager._initialized = old_initialized

    @patch.dict(os.environ, {}, clear=True)
    def test_local_mode_missing_variables_fails_fast(self):
        """Test that local mode (no HAGENT_DOCKER) with missing variables causes fail-fast exit."""
        with patch('sys.exit') as mock_exit:
            PathManager()
            mock_exit.assert_called_once_with(1)

    def test_local_mode_valid_environment(self):
        """Test local mode (no HAGENT_DOCKER) with valid environment variables."""
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            repo_dir = temp_path / 'repo'
            build_dir = temp_path / 'build'
            cache_dir = temp_path / 'cache'

            # Create repo directory (must exist for validation)
            repo_dir.mkdir()

            env_vars = {
                # No HAGENT_DOCKER → local mode
                'HAGENT_REPO_DIR': str(repo_dir),
                'HAGENT_BUILD_DIR': str(build_dir),
                'HAGENT_CACHE_DIR': str(cache_dir),
            }

            with patch.dict(os.environ, env_vars, clear=True):
                pm = PathManager()

                assert pm.is_local_mode()
                assert not pm.is_docker_mode()
                assert pm.repo_dir == repo_dir.resolve()
                assert pm.build_dir == build_dir.resolve()
                assert pm.cache_dir == cache_dir.resolve()

                # Check cache structure was created
                assert (cache_dir / 'inou').exists()
                assert (cache_dir / 'inou' / 'logs').exists()
                assert (cache_dir / 'build').exists()
                assert (cache_dir / 'venv').exists()

    @patch.dict(os.environ, {'HAGENT_DOCKER': 'test-image:latest'}, clear=True)
    def test_docker_mode_minimal_environment(self):
        """Test Docker mode (HAGENT_DOCKER set) with minimal environment."""
        pm = PathManager()
        assert pm.is_docker_mode()
        assert not pm.is_local_mode()
        # In Docker mode without host-mounted variables, use default container paths
        assert pm._repo_dir == Path('/code/workspace/repo')
        assert pm._build_dir == Path('/code/workspace/build')
        assert pm._cache_dir == Path('/code/workspace/cache')

    def test_docker_mode_with_container_variables(self):
        """Test Docker mode (HAGENT_DOCKER set) with host-mounted environment variables."""
        with tempfile.TemporaryDirectory() as temp_dir:
            temp_path = Path(temp_dir)
            repo_dir = temp_path / 'repo'
            build_dir = temp_path / 'build'
            cache_dir = temp_path / 'cache'

            # Create repo directory (must exist for validation)
            repo_dir.mkdir()

            env_vars = {
                'HAGENT_DOCKER': 'test-image:latest',  # Docker mode activated
                'HAGENT_REPO_DIR': str(repo_dir),
                'HAGENT_BUILD_DIR': str(build_dir),
                'HAGENT_CACHE_DIR': str(cache_dir),
            }

            with patch.dict(os.environ, env_vars, clear=True):
                pm = PathManager()

                assert pm.is_docker_mode()
                assert not pm.is_local_mode()
                assert pm.repo_dir == repo_dir.resolve()
                assert pm.build_dir == build_dir.resolve()
                assert pm.cache_dir == cache_dir.resolve()

                # Check cache structure was created (since these are host paths)
                assert (cache_dir / 'inou').exists()
                assert (cache_dir / 'inou' / 'logs').exists()
                assert (cache_dir / 'build').exists()
                assert (cache_dir / 'venv').exists()

    def test_possible_config_paths(self):
        """Test config path generation."""
        paths = PathManager.possible_config_paths()

        # Check basic paths are included
        assert './hagent.yaml' in paths
        assert 'hagent.yaml' in paths
        assert '/code/workspace/repo/hagent.yaml' in paths

        # Test with environment variables
        with tempfile.TemporaryDirectory() as temp_dir:
            env_vars = {
                'HAGENT_REPO_DIR': temp_dir,
                'HAGENT_BUILD_DIR': temp_dir,
            }

            with patch.dict(os.environ, env_vars, clear=True):
                paths = PathManager.possible_config_paths()
                expected_repo_path = str(Path(temp_dir) / 'hagent.yaml')
                assert expected_repo_path in paths

    def test_find_config_existing_file(self):
        """Test finding existing config file."""
        with tempfile.TemporaryDirectory() as temp_dir:
            config_file = Path(temp_dir) / 'hagent.yaml'
            config_file.write_text('test: config')

            with patch('hagent.inou.path_manager.PathManager.possible_config_paths', return_value=[str(config_file)]):
                found_path = PathManager.find_config()
                assert found_path == str(config_file.resolve())

    @patch.dict(os.environ, {}, clear=True)
    def test_find_config_no_file(self):
        """Test find_config when no config file exists."""
        with patch('hagent.inou.path_manager.PathManager.possible_config_paths', return_value=['/nonexistent/path']):
            with pytest.raises(FileNotFoundError, match='No hagent.yaml found'):
                PathManager.find_config()

    def test_find_config_requires_read_permission(self, tmp_path):
        """Ensure unreadable config files are ignored."""
        config_file = tmp_path / 'hagent.yaml'
        config_file.write_text('data: test')
        config_file.chmod(0o000)

        try:
            with patch('hagent.inou.path_manager.PathManager.possible_config_paths', return_value=[str(config_file)]):
                with pytest.raises(FileNotFoundError):
                    PathManager.find_config()
        finally:
            config_file.chmod(0o644)

    def test_find_config_translates_docker_path(self, tmp_path):
        """Docker-style paths should be translated to host paths when possible."""
        config_file = tmp_path / 'hagent.yaml'
        config_file.write_text('test: docker')

        env_vars = {'HAGENT_REPO_DIR': str(tmp_path)}

        with patch.dict(os.environ, env_vars, clear=False):
            with patch(
                'hagent.inou.path_manager.PathManager.possible_config_paths',
                return_value=['/code/workspace/repo/hagent.yaml'],
            ):
                found_path = PathManager.find_config()

        assert found_path == str(config_file.resolve())

    @patch.dict(os.environ, {'HAGENT_DOCKER': 'test-image:latest'}, clear=True)
    def test_find_config_allows_container_path_fallback(self):
        """In Docker mode (HAGENT_DOCKER set), container paths should be returned when host paths aren't available."""
        with patch(
            'hagent.inou.path_manager.PathManager.possible_config_paths',
            return_value=['/code/workspace/repo/hagent.yaml'],
        ):
            found_path = PathManager.find_config()

        assert found_path == '/code/workspace/repo/hagent.yaml'

    def test_get_cache_dir(self):
        """Test get_cache_dir method."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / 'cache'
            # Use mocking to avoid validation
            with patch.object(PathManager, '_validate_and_setup_environment'):
                pm = PathManager()
            pm._cache_dir = cache_dir.resolve()

            result = pm.get_cache_dir()
            expected = str(cache_dir / 'inou')
            assert Path(result).resolve() == Path(expected).resolve()

    def test_get_cache_path_valid(self):
        """Test get_cache_path with valid relative path."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / 'cache'
            # Use mocking to avoid validation
            with patch.object(PathManager, '_validate_and_setup_environment'):
                pm = PathManager()
            pm._cache_dir = cache_dir.resolve()

            result = pm.get_cache_path('test.log')
            expected = str(cache_dir / 'inou' / 'test.log')
            assert Path(result).resolve() == Path(expected).resolve()

    def test_get_cache_path_invalid_absolute(self):
        """Test get_cache_path with invalid absolute path."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / 'cache'
            # Use mocking to avoid validation
            with patch.object(PathManager, '_validate_and_setup_environment'):
                pm = PathManager()
            pm._cache_dir = cache_dir.resolve()

            with patch('sys.exit') as mock_exit:
                pm.get_cache_path('/tmp/absolute.log')
                mock_exit.assert_called_once_with(1)

    def test_get_cache_path_invalid_escape(self):
        """Test get_cache_path with path trying to escape cache directory."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / 'cache'
            # Use mocking to avoid validation
            with patch.object(PathManager, '_validate_and_setup_environment'):
                pm = PathManager()
            pm._cache_dir = cache_dir.resolve()

            with patch('sys.exit') as mock_exit:
                pm.get_cache_path('../escape.log')
                mock_exit.assert_called_once_with(1)

    def test_get_log_dir(self):
        """Test get_log_dir method."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / 'cache'
            # Use mocking to avoid validation
            with patch.object(PathManager, '_validate_and_setup_environment'):
                pm = PathManager()
            pm._cache_dir = cache_dir.resolve()

            result = pm.get_log_dir()
            expected = str(cache_dir / 'inou' / 'logs')
            assert Path(result).resolve() == Path(expected).resolve()

    def test_get_build_cache_dir(self):
        """Test get_build_cache_dir method."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / 'cache'
            # Use mocking to avoid validation
            with patch.object(PathManager, '_validate_and_setup_environment'):
                pm = PathManager()
            pm._cache_dir = cache_dir.resolve()

            result = pm.get_build_cache_dir()
            expected = str(cache_dir / 'build')
            assert Path(result).resolve() == Path(expected).resolve()

    def test_get_venv_dir(self):
        """Test _get_venv_dir method."""
        with tempfile.TemporaryDirectory() as temp_dir:
            cache_dir = Path(temp_dir) / 'cache'
            # Use mocking to avoid validation
            with patch.object(PathManager, '_validate_and_setup_environment'):
                pm = PathManager()
            pm._cache_dir = cache_dir.resolve()

            result = pm._get_venv_dir()
            expected = str(cache_dir / 'venv')
            assert Path(result).resolve() == Path(expected).resolve()

    def test_property_access_without_values_fails_fast(self):
        """Test that accessing properties without values causes fail-fast exit."""
        # Use mocking to avoid validation
        with patch.object(PathManager, '_validate_and_setup_environment'):
            pm = PathManager()

        with patch('sys.exit') as mock_exit:
            _ = pm.repo_dir
            mock_exit.assert_called_once_with(1)

        mock_exit.reset_mock()
        with patch('sys.exit') as mock_exit:
            _ = pm.build_dir
            mock_exit.assert_called_once_with(1)

        mock_exit.reset_mock()
        with patch('sys.exit') as mock_exit:
            _ = pm.cache_dir
            mock_exit.assert_called_once_with(1)

    def test_cache_structure_creation_failure(self):
        """Test handling of cache directory creation failure."""
        with tempfile.TemporaryDirectory() as temp_dir:
            # Create a file where we want to create a directory to cause failure
            cache_path = Path(temp_dir) / 'cache'
            cache_path.write_text('blocking file')

            env_vars = {
                'HAGENT_REPO_DIR': temp_dir,
                'HAGENT_BUILD_DIR': temp_dir,
                'HAGENT_CACHE_DIR': str(cache_path),
            }

            with patch.dict(os.environ, env_vars, clear=True):
                with patch('sys.exit') as mock_exit:
                    PathManager()
                    mock_exit.assert_called_once_with(1)

    @patch.dict(os.environ, {'HAGENT_REPO_DIR': '/nonexistent'}, clear=True)
    def test_nonexistent_repo_dir_fails_fast(self):
        """Test that non-existent repo directory causes fail-fast exit."""
        with patch('sys.exit') as mock_exit:
            PathManager()
            mock_exit.assert_called_once_with(1)
