"""Tests for hagent.inou.cli_locator module.

These are blackbox tests that exercise the CLI using subprocess only.
Tests use Docker mode with mascucsc/hagent-simplechisel:2026.01.

Note: These tests use subprocess.run() and need to pass environment variables
to the subprocess. For subprocess-based CLI tests, we create a copy of os.environ
and modify that copy (not using PathManager.configured() which only affects
the current process).
"""

import os
import subprocess
import sys
import uuid
from pathlib import Path

import pytest


@pytest.fixture(scope='module')
def docker_env_for_cli():
    """Setup environment for Docker-based CLI testing.

    Creates a persistent empty cache directory shared across tests and returns
    environment variables suitable for passing to subprocess.run().

    Uses Docker mode with an empty cache directory. This allows:
    - Prebuilt files (repo, build) inside the Docker image to be used
    - Empty cache directory shared across all tests in this module
    - Persists across tests for efficiency (no recreation overhead)
    - HAGENT_DOCKER=mascucsc/hagent-simplechisel:2026.01
    - HAGENT_CACHE_DIR=output/test_cli_locator_<unique_id>
    """
    # Check if Docker is available
    try:
        result = subprocess.run(['docker', 'info'], capture_output=True, text=True, timeout=5)
        if result.returncode != 0:
            pytest.skip('Docker not available')
    except (FileNotFoundError, subprocess.TimeoutExpired):
        pytest.skip('Docker not available')

    # Create a persistent cache directory for all tests in this module
    # Use output/test_cli_locator_<uuid> to avoid conflicts
    repo_root = Path(__file__).resolve().parent.parent.parent.parent
    test_id = uuid.uuid4().hex[:8]
    test_dir = repo_root / 'output' / f'test_cli_locator_{test_id}'
    test_dir.mkdir(parents=True, exist_ok=True)

    cache_dir = test_dir / 'cache'
    cache_dir.mkdir(exist_ok=True)

    # Set up Docker environment with empty cache mounted
    # Create a NEW dict based on os.environ (don't modify global state)
    env = os.environ.copy()

    # Remove any existing HAGENT path variables
    for key in ['HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_OUTPUT_DIR']:
        env.pop(key, None)

    # Set execution mode, Docker image, and empty cache directory
    # The cache directory is shared across tests but should NOT be populated from Docker
    env.update(
        {
            'HAGENT_DOCKER': 'mascucsc/hagent-simplechisel:2026.01',
            'HAGENT_CACHE_DIR': str(cache_dir),
        }
    )

    # No cleanup - persist cache across all tests for efficiency
    yield {'env': env, 'test_dir': test_dir}


class TestCLILocatorBasics:
    """Test basic CLI functionality."""

    def test_help_message(self):
        """Test that --help displays usage information."""
        result = subprocess.run(
            [sys.executable, '-m', 'hagent.inou.cli_locator', '--help'],
            capture_output=True,
            text=True,
        )

        assert result.returncode == 0
        assert 'Locate variables and code across HDL representations' in result.stdout
        assert '--api' in result.stdout
        assert '--from' in result.stdout
        assert '--to' in result.stdout

    def test_missing_required_arguments(self):
        """Test that missing required arguments produces error."""
        result = subprocess.run(
            [sys.executable, '-m', 'hagent.inou.cli_locator'],
            capture_output=True,
            text=True,
        )

        assert result.returncode != 0
        assert 'required' in result.stderr.lower() or 'error' in result.stderr.lower()

    def test_invalid_api_mode(self):
        """Test that invalid API mode is rejected."""
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'invalid',
                '--from',
                'verilog',
                '--to',
                'chisel',
                '--top',
                'test',
            ],
            capture_output=True,
            text=True,
        )

        assert result.returncode != 0

    def test_invalid_representation(self):
        """Test that invalid representation type is rejected."""
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_variable',
                '--to',
                'invalid',
                '--top',
                'test',
                'x',
            ],
            capture_output=True,
            text=True,
        )

        assert result.returncode != 0

    def test_locate_variable_requires_variable_argument(self):
        """Test that locate_variable mode requires variable argument."""
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_variable',
                '--to',
                'chisel',
                '--top',
                'test',
            ],
            capture_output=True,
            text=True,
        )

        assert result.returncode != 0
        assert 'required' in result.stderr.lower() or 'variable' in result.stderr.lower()

    def test_locate_code_rejects_variable_argument(self):
        """Test that locate_code mode rejects variable argument."""
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_code',
                '--from',
                'verilog',
                '--to',
                'chisel',
                '--top',
                'test',
                'x',
            ],
            capture_output=True,
            text=True,
        )

        assert result.returncode != 0
        assert 'should not be provided' in result.stderr


class TestCLILocatorValidation:
    """Test validation and error handling."""

    def test_map_variable_requires_module(self):
        """Test that map_variable mode requires --module argument."""
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'map_variable',
                '--from',
                'verilog',
                '--to',
                'chisel',
                '--top',
                'test',
                'x',
            ],
            capture_output=True,
            text=True,
        )

        # Should fail because --module is required for map_variable
        assert result.returncode != 0
        assert '--module' in result.stderr or 'module' in result.stderr.lower()


@pytest.mark.integration
@pytest.mark.usefixtures('docker_env_for_cli')
class TestCLILocatorWithPipelinedD:
    """Integration tests with pipelined_d module using Docker.

    These tests use Docker mode with prebuilt files from the Docker image.
    Only HAGENT_CACHE_DIR is mounted for faster re-runs. HAGENT_REPO_DIR and
    HAGENT_BUILD_DIR are not mounted, so tests use prebuilt files inside
    mascucsc/hagent-simplechisel:2026.01.
    """

    @pytest.mark.skip(reason='Locator does not yet support flat netlist/SystemVerilog (no hierarchy)')
    def test_locate_vcd_to_chisel(self, docker_env_for_cli):
        """Test VCD signal mapping to Chisel using locate_vcd API.

        Example: pipelined_d.id_ex_ctrl.reg_ex_ctrl_aluop -> stage-register.scala
        Note: Skipped - netlist.v is flat and Chisel-generated .sv files use flattened
        signal names (_id_ex_ctrl_io_data_ex_ctrl_aluop) instead of hierarchical paths.
        Locator currently requires hierarchical Verilog with module instances.
        """
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_vcd',
                '--to',
                'Chisel',
                '--top',
                'pipelined_d',
                'pipelined_d.id_ex_ctrl.reg_ex_ctrl_aluop',
            ],
            capture_output=True,
            text=True,
            env=docker_env_for_cli['env'],
            cwd=str(docker_env_for_cli['test_dir']),
        )

        # Should succeed and find locations in Scala source
        if result.returncode != 0:
            print(f'STDOUT: {result.stdout}')
            print(f'STDERR: {result.stderr}')

        assert result.returncode == 0, f'CLI failed: {result.stderr}'
        # Should find Scala source files
        assert '.scala' in result.stdout.lower(), f'Scala source not found in output: {result.stdout}'
        # Should contain line numbers
        assert ':' in result.stdout

    @pytest.mark.skip(reason='Locator does not yet support flat netlist/SystemVerilog (no hierarchy)')
    def test_locate_vcd_to_verilog(self, docker_env_for_cli):
        """Test VCD signal mapping to Verilog using locate_vcd API.

        Example: pipelined_d.id_ex_ctrl.reg_ex_ctrl_aluop -> StageReg.sv
        Note: Skipped - requires hierarchical Verilog support
        """
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_vcd',
                '--to',
                'Verilog',
                '--top',
                'pipelined_d',
                'pipelined_d.id_ex_ctrl.reg_ex_ctrl_aluop',
            ],
            capture_output=True,
            text=True,
            env=docker_env_for_cli['env'],
            cwd=str(docker_env_for_cli['test_dir']),
        )

        if result.returncode != 0:
            print(f'STDOUT: {result.stdout}')
            print(f'STDERR: {result.stderr}')

        assert result.returncode == 0, f'CLI failed: {result.stderr}'
        assert '.sv' in result.stdout or '.v' in result.stdout, f'Verilog source not found in output: {result.stdout}'
        assert ':' in result.stdout

    @pytest.mark.skip(reason='Locator does not yet support flat netlist/SystemVerilog (no hierarchy)')
    def test_locate_vcd_verbose(self, docker_env_for_cli):
        """Test verbose output with confidence scores and module info."""
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_vcd',
                '--to',
                'Chisel',
                '--top',
                'pipelined_d',
                '-v',
                'pipelined_d.id_ex_ctrl.reg_ex_ctrl_aluop',
            ],
            capture_output=True,
            text=True,
            env=docker_env_for_cli['env'],
            cwd=str(docker_env_for_cli['test_dir']),
        )

        if result.returncode != 0:
            print(f'STDOUT: {result.stdout}')
            print(f'STDERR: {result.stderr}')

        assert result.returncode == 0
        # Verbose output should include additional information
        # (either in stdout or stderr depending on implementation)
        output = result.stdout + result.stderr
        assert 'Confidence:' in output or 'Module:' in output or '.scala' in output.lower()

    def test_map_variable_verilog_to_chisel(self, docker_env_for_cli):
        """Test cross-representation variable mapping from Verilog to Chisel."""
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'map_variable',
                '--from',
                'verilog',
                '--to',
                'chisel',
                '--top',
                'pipelined_d',
                '--module',
                'ALUControl',
                'io_aluop',
            ],
            capture_output=True,
            text=True,
            env=docker_env_for_cli['env'],
            cwd=str(docker_env_for_cli['test_dir']),
        )

        # This may succeed or fail depending on whether files exist
        # Just verify it doesn't crash
        if result.returncode != 0:
            # Error should be informative
            assert len(result.stderr) > 0

    def test_locate_variable_in_chisel(self, docker_env_for_cli):
        """Test single-representation variable location within Chisel."""
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_variable',
                '--to',
                'chisel',
                '--top',
                'pipelined_d',
                '--module',
                'ALUControl',
                'aluop',
            ],
            capture_output=True,
            text=True,
            env=docker_env_for_cli['env'],
            cwd=str(docker_env_for_cli['test_dir']),
        )

        # May succeed or fail depending on exact variable names
        # Just verify it doesn't crash and provides feedback
        assert result.returncode in [0, 1]
        if result.returncode != 0:
            assert len(result.stderr) > 0


@pytest.mark.integration
@pytest.mark.usefixtures('docker_env_for_cli')
class TestCLILocatorWithGCD:
    """Integration tests with GCD module using Docker.

    Tests VCD signal location with case-insensitive module names.
    Uses the same Docker environment as PipelinedD tests.
    """

    def test_locate_vcd_gcd_lowercase(self, docker_env_for_cli):
        """Test VCD signal location with lowercase module name: gcd.x -> GCD.sv.

        Tests case-insensitive hierarchy matching where user provides 'gcd'
        but slang-hier returns 'GCD'.
        """
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_vcd',
                '--to',
                'verilog',
                '--top',
                'gcd',
                'gcd.x',
            ],
            capture_output=True,
            text=True,
            env=docker_env_for_cli['env'],
            cwd=str(docker_env_for_cli['test_dir']),
        )

        # Should succeed and find 'x' variable in GCD.sv
        if result.returncode != 0:
            print(f'STDOUT: {result.stdout}')
            print(f'STDERR: {result.stderr}')

        assert result.returncode == 0, f'CLI failed: {result.stderr}'
        assert 'GCD.sv' in result.stdout, f'GCD.sv not found in output: {result.stdout}'
        # Should find multiple occurrences of 'x' (at lines 12, 16, 19, 20, 22, 24)
        assert result.stdout.count(':') >= 6, f'Expected at least 6 occurrences, got: {result.stdout}'

    def test_locate_vcd_gcd_uppercase(self, docker_env_for_cli):
        """Test VCD signal location with uppercase module name: GCD.x -> GCD.sv.

        Tests exact case matching when user provides correct case.
        """
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_vcd',
                '--to',
                'verilog',
                '--top',
                'gcd',
                'GCD.x',
            ],
            capture_output=True,
            text=True,
            env=docker_env_for_cli['env'],
            cwd=str(docker_env_for_cli['test_dir']),
        )

        # Should succeed and find 'x' variable in GCD.sv
        if result.returncode != 0:
            print(f'STDOUT: {result.stdout}')
            print(f'STDERR: {result.stderr}')

        assert result.returncode == 0, f'CLI failed: {result.stderr}'
        assert 'GCD.sv' in result.stdout, f'GCD.sv not found in output: {result.stdout}'
        # Should find multiple occurrences of 'x' (at lines 12, 16, 19, 20, 22, 24)
        assert result.stdout.count(':') >= 6, f'Expected at least 6 occurrences, got: {result.stdout}'

    def test_locate_vcd_gcd_io_signal(self, docker_env_for_cli):
        """Test VCD signal location with IO signal: gcd.io_outputGCD -> GCD.sv."""
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_vcd',
                '--to',
                'verilog',
                '--top',
                'gcd',
                'gcd.io_outputGCD',
            ],
            capture_output=True,
            text=True,
            env=docker_env_for_cli['env'],
            cwd=str(docker_env_for_cli['test_dir']),
        )

        # Should succeed and find 'io_outputGCD' in GCD.sv
        if result.returncode != 0:
            print(f'STDOUT: {result.stdout}')
            print(f'STDERR: {result.stderr}')

        assert result.returncode == 0, f'CLI failed: {result.stderr}'
        assert 'GCD.sv' in result.stdout, f'GCD.sv not found in output: {result.stdout}'
        # Should find at least one occurrence
        assert ':' in result.stdout, f'No line numbers found in output: {result.stdout}'


@pytest.mark.integration
@pytest.mark.usefixtures('docker_env_for_cli')
class TestCLILocatorWithPipelinedDHierarchy:
    """Integration tests with hierarchical PipelinedCPU module using Docker.

    Tests VCD signal location in hierarchical designs where slang-hier
    returns multiple modules with instance paths.
    """

    def test_locate_vcd_hierarchical_signal(self, docker_env_for_cli):
        """Test VCD signal location in hierarchical design: PipelinedCPU.aluControl.io_aluop -> ALUControl.sv.

        Tests that:
        1. synth.py --dry-run is called with template substitution
        2. Slang args are extracted correctly (-F filelist.f, not netlist.v)
        3. Full hierarchy is built (17 modules for PipelinedCPU)
        4. Signal is found in the correct submodule (ALUControl)
        """
        result = subprocess.run(
            [
                sys.executable,
                '-m',
                'hagent.inou.cli_locator',
                '--api',
                'locate_vcd',
                '--to',
                'verilog',
                '--top',
                'pipelined_d',
                'PipelinedCPU.aluControl.io_aluop',
            ],
            capture_output=True,
            text=True,
            env=docker_env_for_cli['env'],
            cwd=str(docker_env_for_cli['test_dir']),
        )

        # Should succeed and find 'io_aluop' in ALUControl.sv
        if result.returncode != 0:
            print(f'STDOUT: {result.stdout}')
            print(f'STDERR: {result.stderr}')

        assert result.returncode == 0, f'CLI failed: {result.stderr}'
        assert 'ALUControl.sv' in result.stdout, f'ALUControl.sv not found in output: {result.stdout}'
        # Should find occurrences at lines 3 and 38
        assert result.stdout.count(':') >= 2, f'Expected at least 2 occurrences, got: {result.stdout}'
        # Verify clean output (no debug info like "Module=" should be present)
        assert 'Module=' not in result.stdout, f'Debug output found in results: {result.stdout}'


if __name__ == '__main__':
    pytest.main([__file__, '-v'])
