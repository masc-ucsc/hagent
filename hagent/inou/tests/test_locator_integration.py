"""Integration tests for hagent.inou.locator with real Docker environment.

These tests use the mascucsc/hagent-simplechisel:2025.10 Docker image to test
the full Locator workflow with actual Chisel compilation and slang-hier integration.
"""

import os
import subprocess
import tempfile
from pathlib import Path

import pytest

from hagent.inou.builder import Builder
from hagent.inou.locator import Locator, RepresentationType


@pytest.fixture(scope='class')
def docker_env():
    """Setup environment for Docker-based testing.

    Creates a temporary test directory and runs setup_simplechisel_mcp.sh to
    initialize the environment.
    """
    # Check if Docker is available
    try:
        result = subprocess.run(['docker', 'info'], capture_output=True, text=True, timeout=5)
        if result.returncode != 0:
            pytest.skip('Docker not available')
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pytest.skip('Docker not available')

    # Find hagent root directory
    test_file = Path(__file__).resolve()
    hagent_root = test_file.parent.parent.parent.parent
    setup_run_dir = hagent_root / 'setup_run'
    setup_run_dir.mkdir(exist_ok=True)

    # Create unique temporary directory for this test class
    test_dir = Path(tempfile.mkdtemp(prefix='locator_integration_', dir=setup_run_dir))

    try:
        # Run setup_simplechisel_mcp.sh to initialize the test environment
        setup_script = hagent_root / 'scripts' / 'setup_simplechisel_mcp.sh'
        result = subprocess.run(
            [str(setup_script), str(test_dir)],
            capture_output=True,
            text=True,
            timeout=60,
        )

        if result.returncode != 0:
            pytest.skip(f'Failed to setup test environment: {result.stderr}')

        repo_dir = test_dir / 'repo'
        build_dir = test_dir / 'build'
        cache_dir = test_dir / 'cache'

        # Verify directories were created
        if not all([repo_dir.exists(), build_dir.exists(), cache_dir.exists()]):
            pytest.skip('Setup script did not create expected directories')

        # Set environment variables for hagent
        old_env = {}
        env_vars = {
            'HAGENT_EXECUTION_MODE': 'docker',
            'HAGENT_DOCKER': 'mascucsc/hagent-simplechisel:2025.10',
            'HAGENT_REPO_DIR': str(repo_dir),
            'HAGENT_BUILD_DIR': str(build_dir),
            'HAGENT_CACHE_DIR': str(cache_dir),
        }

        for key, value in env_vars.items():
            old_env[key] = os.environ.get(key)
            os.environ[key] = value

        yield {
            'repo_dir': repo_dir,
            'build_dir': build_dir,
            'cache_dir': cache_dir,
        }

        # Restore environment
        for key, value in old_env.items():
            if value is None:
                os.environ.pop(key, None)
            else:
                os.environ[key] = value

    finally:
        # Cleanup: remove temporary test directory
        import shutil

        if test_dir.exists():
            shutil.rmtree(test_dir, ignore_errors=True)


@pytest.mark.integration
class TestLocatorGCDIntegration:
    """Integration tests using GCD module from Docker image.

    These tests require a fully functional build environment.
    Tests will skip if compilation is not available.
    """

    def _compile_gcd(self, docker_env):
        """Helper to compile GCD, skipping test if not available."""
        builder = Builder(config_path=None)
        if not builder.setup():
            pytest.skip(f'Builder setup failed: {builder.get_error()}')

        exit_code, stdout, stderr = builder.run_api(exact_name='gcd', command_name='compile')
        if exit_code != 0:
            pytest.skip(f'Compilation not available in test environment: {stderr}')

        return builder, exit_code, stdout, stderr

    def test_gcd_setup_and_compile(self, docker_env):
        """Test that we can setup Builder and compile GCD module."""
        builder, exit_code, stdout, stderr = self._compile_gcd(docker_env)

        # Check that Verilog files were generated
        build_dir = Path(docker_env['build_dir'])
        verilog_files = list(build_dir.glob('build_gcd/*.sv'))
        assert len(verilog_files) > 0, 'No Verilog files generated'

        # Check that GCD.sv exists
        gcd_file = build_dir / 'build_gcd' / 'GCD.sv'
        assert gcd_file.exists(), 'GCD.sv not found'

        builder.cleanup()

    def test_gcd_locator_setup(self, docker_env):
        """Test Locator setup with GCD profile."""
        locator = Locator(config_path=None, profile_name='gcd')

        # Setup locator (this will also setup Builder)
        assert locator.setup(), f'Locator setup failed: {locator.get_error()}'

        # Check that cache directory was created
        cache_dir = Path(docker_env['cache_dir'])
        locator_cache = cache_dir / 'locator' / 'gcd'
        assert locator_cache.exists(), 'Locator cache directory not created'

        locator.cleanup()

    def test_gcd_verilog_to_chisel_variable_mapping(self, docker_env):
        """Test mapping Verilog variables to Chisel source for GCD module."""
        # First compile the GCD module
        builder, exit_code, stdout, stderr = self._compile_gcd(docker_env)
        builder.cleanup()

        # Now use Locator to map variables
        locator = Locator(config_path=None, profile_name='gcd')
        assert locator.setup(), f'Locator setup failed: {locator.get_error()}'

        # Try to find Verilog variable "x" in Chisel source
        # "x" is a register in the GCD module
        chisel_locs = locator.locate_variable(
            to=RepresentationType.CHISEL,
            from_type=RepresentationType.VERILOG,
            variable='x',
        )

        # We should find the variable "x" in GCD.scala
        assert len(chisel_locs) > 0, 'No Chisel locations found for variable "x"'

        # Check that we found it in GCD.scala
        found_in_gcd = any('GCD.scala' in loc.file_path for loc in chisel_locs)
        assert found_in_gcd, 'Variable "x" not found in GCD.scala'

        # Check the confidence and module name
        for loc in chisel_locs:
            if 'GCD.scala' in loc.file_path:
                assert loc.module_name == 'GCD', f'Wrong module name: {loc.module_name}'
                assert loc.confidence > 0.0, 'Confidence should be > 0'
                assert loc.representation == RepresentationType.CHISEL

        locator.cleanup()

    def test_gcd_find_multiple_variables(self, docker_env):
        """Test finding multiple GCD variables in Chisel."""
        # Compile GCD
        builder, exit_code, _, _ = self._compile_gcd(docker_env)
        builder.cleanup()

        # Setup locator
        locator = Locator(config_path=None, profile_name='gcd')
        assert locator.setup()

        # Test finding different variables from GCD module
        test_variables = ['x', 'y', 'io']

        for var_name in test_variables:
            chisel_locs = locator.locate_variable(
                to=RepresentationType.CHISEL,
                from_type=RepresentationType.VERILOG,
                variable=var_name,
            )

            # Should find at least one location
            assert len(chisel_locs) > 0, f'Variable "{var_name}" not found in Chisel'

            # At least one should be in GCD.scala
            found = any('GCD.scala' in loc.file_path for loc in chisel_locs)
            assert found, f'Variable "{var_name}" not found in GCD.scala'

        locator.cleanup()

    def test_gcd_cache_persistence(self, docker_env):
        """Test that Locator cache persists across instances."""
        # Compile GCD
        builder, exit_code, _, _ = self._compile_gcd(docker_env)
        builder.cleanup()

        # First locator instance - will build cache
        locator1 = Locator(config_path=None, profile_name='gcd')
        assert locator1.setup()

        # Perform a lookup to trigger cache building
        locs1 = locator1.locate_variable(
            to=RepresentationType.CHISEL,
            from_type=RepresentationType.VERILOG,
            variable='x',
        )
        assert len(locs1) > 0

        # Check that cache files exist
        cache_dir = Path(docker_env['cache_dir']) / 'locator' / 'gcd'
        cache_files_before = list(cache_dir.glob('*.cache'))
        assert len(cache_files_before) > 0, 'No cache files created'

        locator1.cleanup()

        # Second locator instance - should use existing cache
        locator2 = Locator(config_path=None, profile_name='gcd')
        assert locator2.setup()

        locs2 = locator2.locate_variable(
            to=RepresentationType.CHISEL,
            from_type=RepresentationType.VERILOG,
            variable='x',
        )

        # Should get same results (cache working)
        assert len(locs2) == len(locs1), 'Cache not working - different results'

        # Cache files should still exist
        cache_files_after = list(cache_dir.glob('*.cache'))
        assert len(cache_files_after) == len(cache_files_before), 'Cache files changed unexpectedly'

        locator2.cleanup()

    def test_gcd_cache_invalidation(self, docker_env):
        """Test cache invalidation for GCD module."""
        # Compile GCD
        builder, exit_code, _, _ = self._compile_gcd(docker_env)
        builder.cleanup()

        # Setup locator and build cache
        locator = Locator(config_path=None, profile_name='gcd')
        assert locator.setup()

        # Trigger cache building
        locator.locate_variable(
            to=RepresentationType.CHISEL,
            from_type=RepresentationType.VERILOG,
            variable='x',
        )

        # Check cache exists
        cache_dir = Path(docker_env['cache_dir']) / 'locator' / 'gcd'
        assert (cache_dir / 'metadata.json').exists(), 'Metadata not created'

        # Invalidate cache (soft)
        locator.invalidate_cache(force=False)

        # Metadata should be gone but cache files remain
        assert not (cache_dir / 'metadata.json').exists(), 'Metadata not deleted'
        cache_files = list(cache_dir.glob('*.cache'))
        assert len(cache_files) > 0, 'Cache files were deleted (should remain)'

        # Invalidate cache (force)
        locator.invalidate_cache(force=True)

        # All cache files should be gone
        cache_files_after = list(cache_dir.glob('*.cache'))
        assert len(cache_files_after) == 0, 'Cache files not deleted with force=True'

        locator.cleanup()

    def test_gcd_verilog_to_chisel_code_mapping(self, docker_env):
        """Test mapping Verilog code changes to Chisel source."""
        # Compile GCD
        builder, exit_code, _, _ = self._compile_gcd(docker_env)
        builder.cleanup()

        # Setup locator
        locator = Locator(config_path=None, profile_name='gcd')
        assert locator.setup()

        # Create a unified diff for GCD module
        diff = """
--- a/GCD.sv
+++ b/GCD.sv
@@ -20,2 +20,3 @@
   reg [15:0] x;
+  reg [15:0] temp;
   reg [15:0] y;
"""

        # Map the diff to Chisel
        chisel_locs = locator.locate_code(to=RepresentationType.CHISEL, from_type=RepresentationType.VERILOG, diff_patch=diff)

        # Should find locations in GCD.scala
        assert len(chisel_locs) > 0, 'No Chisel locations found for diff'

        # Check that results point to GCD.scala
        for loc in chisel_locs:
            assert 'GCD.scala' in loc.file_path
            assert loc.module_name == 'GCD'
            assert loc.representation == RepresentationType.CHISEL

        locator.cleanup()

    def test_gcd_error_handling(self, docker_env):
        """Test error handling for invalid operations."""
        # Compile GCD
        builder, exit_code, _, _ = self._compile_gcd(docker_env)
        builder.cleanup()

        # Setup locator
        locator = Locator(config_path=None, profile_name='gcd')
        assert locator.setup()

        # Test same-representation error
        result = locator.locate_variable(
            to=RepresentationType.VERILOG,
            from_type=RepresentationType.VERILOG,
            variable='x',
        )
        assert result == []
        assert locator.get_error() == 'same representation mapping not supported'

        # Test synalign not integrated error
        result = locator.locate_variable(
            to=RepresentationType.NETLIST,
            from_type=RepresentationType.VERILOG,
            variable='x',
        )
        assert result == []
        assert locator.get_error() == 'synalign not integrated'

        locator.cleanup()


@pytest.mark.integration
class TestLocatorWithSlangHier:
    """Test Locator with slang-hier integration for hierarchy analysis."""

    def _compile_gcd(self, docker_env):
        """Helper to compile GCD, skipping test if not available."""
        builder = Builder(config_path=None)
        if not builder.setup():
            pytest.skip(f'Builder setup failed: {builder.get_error()}')

        exit_code, stdout, stderr = builder.run_api(exact_name='gcd', command_name='compile')
        if exit_code != 0:
            pytest.skip(f'Compilation not available in test environment: {stderr}')

        return builder, exit_code, stdout, stderr

    def test_slang_hier_execution(self, docker_env):
        """Test that slang-hier can be executed through Locator."""
        # Compile GCD first
        builder, exit_code, _, _ = self._compile_gcd(docker_env)
        builder.cleanup()

        # Setup locator
        locator = Locator(config_path=None, profile_name='gcd')
        assert locator.setup()

        # Try to build hierarchy cache (this will run slang-hier)
        # Note: This is an internal method, but we're testing the integration
        _hierarchy = locator._build_hierarchy_cache()

        # Should have some hierarchy data
        # Note: slang-hier might not be in the Docker image, so we check gracefully
        if locator.get_error() and 'slang-hier' in locator.get_error():
            pytest.skip('slang-hier not available in Docker image')

        # If we got here, hierarchy cache was built successfully
        assert isinstance(_hierarchy, dict), 'Hierarchy should be a dict'

        locator.cleanup()


if __name__ == '__main__':
    pytest.main([__file__, '-v', '-m', 'integration'])
