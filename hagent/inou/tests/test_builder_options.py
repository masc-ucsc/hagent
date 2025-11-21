"""Test Builder optional parameters functionality."""

import shutil
import tempfile
from pathlib import Path

import pytest

from hagent.inou.builder import Builder
from hagent.inou.path_manager import PathManager


@pytest.fixture
def test_config_dir():
    """Create a temporary directory with a copy of the test hagent.yaml."""
    with tempfile.TemporaryDirectory() as tmpdir:
        # Copy the shared test configuration file
        test_config_source = Path(__file__).parent / 'hagent_test.yaml'
        config_path = Path(tmpdir) / 'hagent.yaml'
        shutil.copy(test_config_source, config_path)
        yield tmpdir, str(config_path)


def test_builder_options_with_defaults(test_config_dir):
    """Test that default values are used when options not provided."""
    tmpdir, config_path = test_config_dir

    # Use PathManager.configured() for clean test isolation
    with PathManager.configured(repo_dir=tmpdir, build_dir=tmpdir, cache_dir=tmpdir):
        builder = Builder(config_path=config_path)
        success = builder.setup()
        assert success, f'Builder setup failed: {builder.get_error()}'

        try:
            # Run without providing options - should use defaults
            exit_code, stdout, stderr = builder.run_api(exact_name='echo', command_name='custom_echo', dry_run=True, options=None)

            assert exit_code == 0, f'Command failed with stderr: {stderr}'
            # Should have default prefix "INFO:" (format: "{value}:" with value="INFO") and no suffix
            assert 'echo INFO:HAGENT_TEST' in stdout, f'Expected default prefix in output: {stdout}'
        finally:
            builder.cleanup()


def test_builder_options_with_custom_values(test_config_dir):
    """Test that custom option values override defaults."""
    tmpdir, config_path = test_config_dir

    # Use PathManager.configured() for clean test isolation
    with PathManager.configured(repo_dir=tmpdir, build_dir=tmpdir, cache_dir=tmpdir):
        builder = Builder(config_path=config_path)
        success = builder.setup()
        assert success, f'Builder setup failed: {builder.get_error()}'

        try:
            # Run with custom options
            exit_code, stdout, stderr = builder.run_api(
                exact_name='echo',
                command_name='custom_echo',
                dry_run=True,
                options={'prefix': 'DEBUG', 'suffix': 'test'},
            )

            assert exit_code == 0, f'Command failed with stderr: {stderr}'
            # Should have custom prefix "DEBUG:" and suffix "(test)"
            assert 'DEBUG:HAGENT_TEST(test)' in stdout, f'Expected custom options in output: {stdout}'
        finally:
            builder.cleanup()


def test_builder_options_partial_override(test_config_dir):
    """Test that partial option overrides work correctly."""
    tmpdir, config_path = test_config_dir

    # Use PathManager.configured() for clean test isolation
    with PathManager.configured(repo_dir=tmpdir, build_dir=tmpdir, cache_dir=tmpdir):
        builder = Builder(config_path=config_path)
        success = builder.setup()
        assert success, f'Builder setup failed: {builder.get_error()}'

        try:
            # Override only suffix, keep default prefix
            exit_code, stdout, stderr = builder.run_api(
                exact_name='echo', command_name='custom_echo', dry_run=True, options={'suffix': 'partial'}
            )

            assert exit_code == 0, f'Command failed with stderr: {stderr}'
            # Should have default prefix "INFO:" and custom suffix "(partial)"
            assert 'echo INFO:HAGENT_TEST(partial)' in stdout, f'Expected partial override in output: {stdout}'
        finally:
            builder.cleanup()


def test_builder_options_empty_suffix(test_config_dir):
    """Test that empty default values work correctly."""
    tmpdir, config_path = test_config_dir

    # Use PathManager.configured() for clean test isolation
    with PathManager.configured(repo_dir=tmpdir, build_dir=tmpdir, cache_dir=tmpdir):
        builder = Builder(config_path=config_path)
        success = builder.setup()
        assert success, f'Builder setup failed: {builder.get_error()}'

        try:
            # Override only prefix, suffix should remain empty
            exit_code, stdout, stderr = builder.run_api(
                exact_name='echo', command_name='custom_echo', dry_run=True, options={'prefix': 'WARN'}
            )

            assert exit_code == 0, f'Command failed with stderr: {stderr}'
            # Should have custom prefix "WARN:" and no suffix
            assert 'WARN:HAGENT_TEST' in stdout, f'Expected no suffix in output: {stdout}'
            # Make sure there's no trailing parentheses from empty suffix
            assert 'WARN:HAGENT_TEST()' not in stdout, f'Empty suffix should not add parentheses: {stdout}'
        finally:
            builder.cleanup()


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
