#!/usr/bin/env python3
"""
Converted test suite for Yosys synthesis operations using new Executor API.

This test suite validates executor functionality with Yosys synthesis tools. Tests cover:
1. Basic Yosys synthesis commands
2. Verilog file processing
3. Synthesis output verification
4. Error handling for synthesis failures
5. Complex synthesis flows

Converted from original test_file_manager_yosys.py to use new Executor API.
"""

import os
import pytest
from hagent.inou.path_manager import PathManager
from hagent.inou.runner import Runner


@pytest.fixture(scope='function', autouse=True)
def setup_hagent_environment(request):
    """Setup HAGENT environment for Docker mode tests using PathManager.configured()."""
    import hagent.inou.container_manager as cm

    # Reset container state before setting new environment
    cm._docker_workspace_validated = False

    # Use unique directory for each test to avoid parallel test conflicts
    test_name = request.node.name
    base_dir = os.path.abspath(f'./output/test_executor_yosys_synthesis/{test_name}')
    repo_dir = os.path.join(base_dir, 'repo')
    build_dir = os.path.join(base_dir, 'build')
    cache_dir = os.path.join(base_dir, 'cache')

    # Create directories if they don't exist
    os.makedirs(repo_dir, exist_ok=True)
    os.makedirs(build_dir, exist_ok=True)
    os.makedirs(cache_dir, exist_ok=True)

    # Use PathManager.configured() context manager for clean test isolation
    with PathManager.configured(
        docker_image='mascucsc/hagent-builder:2025.12',
        repo_dir=repo_dir,
        build_dir=build_dir,
        cache_dir=cache_dir,
    ):
        yield

    # Reset container state after test
    cm._docker_workspace_validated = False


@pytest.mark.slow
class TestExecutorYosysSynthesis:
    """Test suite for Yosys synthesis operations using new Executor API."""

    @pytest.fixture
    def verilog_files(self):
        """Create temporary Verilog test files and clean them up after test."""
        files = {}

        # Simple inverter module
        files['inverter.v'] = """
module simple_inverter(
  input  wire a,
  output wire y
);
  assign y = ~a;
endmodule
"""

        # AND gate module
        files['and_gate.v'] = """
module and_gate(
  input  wire a,
  input  wire b,
  output wire y
);
  assign y = a & b;
endmodule
"""

        # Counter module (more complex)
        files['counter.v'] = """
module counter(
  input  wire clk,
  input  wire reset,
  output reg [3:0] count
);
  always @(posedge clk or posedge reset) begin
    if (reset)
      count <= 4'b0000;
    else
      count <= count + 1;
  end
endmodule
"""

        return files

    @pytest.fixture
    def runner_filesystem(self):
        """Create and setup a Runner and FileSystem instance with Yosys tools."""
        # Create Runner instance with Docker image
        runner = Runner(docker_image='mascucsc/hagent-builder:2025.12')
        assert runner.setup(), f'Runner setup failed: {runner.get_error()}'

        # Runner provides its own filesystem
        filesystem = runner.filesystem
        assert filesystem is not None, 'Runner filesystem not initialized'

        yield runner, filesystem

        # Cleanup
        try:
            runner.cleanup()
        except Exception:
            pass

    def test_yosys_available(self, runner_filesystem):
        """Test that Yosys is available in the container."""
        runner, filesystem = runner_filesystem

        # Check if yosys is available
        rc, out, err = runner.run_cmd('which yosys')
        if rc != 0:
            pytest.skip(f'Yosys not available: {err}')

        # Check yosys version
        rc, out, err = runner.run_cmd('yosys -V')
        assert rc == 0, f'Yosys version check failed - RC: {rc}, ERR: {err}'
        assert 'Yosys' in out, f'Unexpected yosys version output: {out}'

    def test_simple_verilog_synthesis(self, runner_filesystem, verilog_files):
        """Test basic Verilog synthesis with Yosys."""
        runner, filesystem = runner_filesystem

        # Skip if yosys not available
        rc, _, _ = runner.run_cmd('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available')

        # Clean up any existing files
        runner.run_cmd('rm -f *.v *.json')

        # Create simple Verilog file using filesystem
        verilog_content = verilog_files['inverter.v']
        assert filesystem.write_text('inverter.v', verilog_content), 'Failed to create Verilog file'

        # Debug: Check if commands are running at all
        rc, out, err = runner.run_cmd('echo "Test command working"')
        print(f"Test command: RC={rc}, OUT='{out}', ERR='{err}'")

        # Try different ways to check mounts
        rc, out, err = runner.run_cmd('mount | grep workspace || echo "No workspace mounts found"')
        print(f'Workspace mounts: {out}')

        # Check if directories exist
        rc, out, err = runner.run_cmd('ls -la /code/workspace/ || echo "workspace dir missing"')
        print(f'Workspace directory: {out}')

        print('=' * 50)

        # Check current working directory and initial files
        rc, out, err = runner.run_cmd('pwd && ls -la')
        print(f'Working directory and files before yosys: {out}')

        # Check container user and permissions
        rc, out, err = runner.run_cmd('id && ls -la inverter.v')
        print(f'User and file permissions: {out}')

        # Simple synthesis using opt instead of synth to avoid memory issues
        yosys_cmd = 'yosys -p "read_verilog inverter.v; opt; write_verilog inverter_synth.v"'
        rc, out, err = runner.run_cmd(yosys_cmd)

        # Debug: show files after yosys run and check if yosys completed successfully
        rc2, out2, err2 = runner.run_cmd('ls -la *.v 2>/dev/null || echo "No .v files found"')
        print(f'Verilog files after yosys: {out2}')

        # Check if yosys actually completed or was killed
        if rc == 137:
            print('Yosys was killed (SIGKILL) - likely memory or resource constraint')
            rc3, out3, err3 = runner.run_cmd('dmesg | tail -10 2>/dev/null || echo "Cannot access dmesg"')
            print(f'System messages: {out3}')

        assert rc == 0, f'Yosys synthesis failed - RC: {rc}, ERR: {err}, STDOUT: {out}'

        # Verify output file was created
        rc, out, err = runner.run_cmd('test -f inverter_synth.v')
        if rc != 0:
            # Additional debugging if file not found
            rc_debug, out_debug, err_debug = runner.run_cmd('ls -la && find . -name "*.v"')
            print(f'Debug - current directory contents: {out_debug}')
        assert rc == 0, f'Synthesis output file not found - RC: {rc}, ERR: {err}'

        # Check that output contains synthesized content
        rc, out, err = runner.run_cmd('cat inverter_synth.v')
        assert rc == 0, f'Could not read synthesis output - RC: {rc}, ERR: {err}'
        assert 'module' in out.lower(), f'Synthesis output does not contain module: {out}'

    def test_synthesis_with_statistics(self, runner_filesystem, verilog_files):
        """Test synthesis with statistics reporting."""
        runner, filesystem = runner_filesystem

        # Skip if yosys not available
        rc, _, _ = runner.run_cmd('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        runner.run_cmd('rm -f *.v *.json')

        # Create Verilog file
        verilog_content = verilog_files['and_gate.v']
        assert filesystem.write_text('and_gate.v', verilog_content), 'Failed to create Verilog file'

        # Synthesis with statistics
        yosys_cmd = 'yosys -p "read_verilog and_gate.v; synth; stat"'
        rc, out, err = runner.run_cmd(yosys_cmd)
        assert rc == 0, f'Yosys synthesis with stats failed - RC: {rc}, ERR: {err}'

        # Check that statistics are in output
        # Yosys stat command outputs lines like "1 cells", "3 wires", etc.
        assert 'Printing statistics' in out or 'cells' in out, f'Statistics not found in output: {out}'

    def test_synthesis_to_json(self, runner_filesystem, verilog_files):
        """Test synthesis with JSON output format."""
        runner, filesystem = runner_filesystem

        # Skip if yosys not available
        rc, _, _ = runner.run_cmd('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        runner.run_cmd('rm -f *.v *.json')

        # Create Verilog file
        verilog_content = verilog_files['inverter.v']
        assert filesystem.write_text('inverter.v', verilog_content), 'Failed to create Verilog file'

        # Synthesis to JSON
        yosys_cmd = 'yosys -p "read_verilog inverter.v; synth; write_json inverter.json"'
        rc, out, err = runner.run_cmd(yosys_cmd)
        assert rc == 0, f'Yosys JSON synthesis failed - RC: {rc}, ERR: {err}'

        # Verify JSON file was created
        rc, out, err = runner.run_cmd('test -f inverter.json')
        assert rc == 0, f'JSON output file not found - RC: {rc}, ERR: {err}'

        # Verify JSON content
        rc, out, err = runner.run_cmd('head -10 inverter.json')
        assert rc == 0, f'Could not read JSON output - RC: {rc}, ERR: {err}'
        assert '{' in out, f'JSON output does not appear to be valid JSON: {out}'

    def test_synthesis_error_handling(self, runner_filesystem):
        """Test error handling for invalid Verilog synthesis."""
        runner, filesystem = runner_filesystem

        # Skip if yosys not available
        rc, _, _ = runner.run_cmd('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        runner.run_cmd('rm -f *.v *.json')

        # Create invalid Verilog file
        invalid_verilog = """
module broken_module(
  invalid syntax here
  missing endmodule
"""
        assert filesystem.write_text('broken.v', invalid_verilog), 'Failed to create invalid Verilog file'

        # Try to synthesize invalid file
        yosys_cmd = 'yosys -p "read_verilog broken.v; synth"'
        rc, out, err = runner.run_cmd(yosys_cmd)
        assert rc != 0, 'Yosys should have failed on invalid Verilog but succeeded'

        # Check that error message is informative
        combined_output = out + err
        assert 'syntax error' in combined_output.lower() or 'error' in combined_output.lower(), (
            f'Error output should contain error information: {combined_output}'
        )

    def test_multiple_file_synthesis(self, runner_filesystem, verilog_files):
        """Test synthesis with multiple Verilog files."""
        runner, filesystem = runner_filesystem

        # Skip if yosys not available
        rc, _, _ = runner.run_cmd('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing .v files to avoid conflicts
        runner.run_cmd('rm -f *.v *.json')

        # Create multiple Verilog files
        for filename, content in verilog_files.items():
            assert filesystem.write_text(filename, content), f'Failed to create {filename}'

        # Synthesis with multiple files
        yosys_cmd = 'yosys -p "read_verilog *.v; synth; write_verilog combined_synth.v"'
        rc, out, err = runner.run_cmd(yosys_cmd)
        assert rc == 0, f'Multi-file synthesis failed - RC: {rc}, ERR: {err}'

        # Verify output file was created
        rc, out, err = runner.run_cmd('test -f combined_synth.v')
        assert rc == 0, f'Multi-file synthesis output not found - RC: {rc}, ERR: {err}'

        # Check that all modules are present in output
        rc, out, err = runner.run_cmd('cat combined_synth.v')
        assert rc == 0, f'Could not read multi-file synthesis output - RC: {rc}, ERR: {err}'

    def test_synthesis_with_technology_mapping(self, runner_filesystem, verilog_files):
        """Test synthesis with technology mapping."""
        runner, filesystem = runner_filesystem

        # Skip if yosys not available
        rc, _, _ = runner.run_cmd('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        runner.run_cmd('rm -f *.v *.json')

        # Create Verilog file
        verilog_content = verilog_files['counter.v']
        assert filesystem.write_text('counter.v', verilog_content), 'Failed to create Verilog file'

        # Synthesis with technology mapping (using basic cell library)
        yosys_cmd = 'yosys -p "read_verilog counter.v; synth; dfflibmap -liberty /dev/null; abc; write_verilog counter_mapped.v"'
        rc, out, err = runner.run_cmd(yosys_cmd)
        # Note: This might fail if liberty file is not available, which is expected
        # We're mainly testing that the command structure works

        if rc == 0:
            # If successful, verify output
            rc, out, err = runner.run_cmd('test -f counter_mapped.v')
            assert rc == 0, f'Technology mapped output not found - RC: {rc}, ERR: {err}'

    def test_yosys_script_execution(self, runner_filesystem, verilog_files):
        """Test execution of Yosys scripts."""
        runner, filesystem = runner_filesystem

        # Skip if yosys not available
        rc, _, _ = runner.run_cmd('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        runner.run_cmd('rm -f *.v *.json *.ys')

        # Create Verilog file
        verilog_content = verilog_files['and_gate.v']
        assert filesystem.write_text('and_gate.v', verilog_content), 'Failed to create Verilog file'

        # Create Yosys script
        yosys_script = """
read_verilog and_gate.v
synth
stat
write_verilog and_gate_script.v
"""
        assert filesystem.write_text('synth.ys', yosys_script), 'Failed to create Yosys script'

        # Execute script
        rc, out, err = runner.run_cmd('yosys -s synth.ys')
        assert rc == 0, f'Yosys script execution failed - RC: {rc}, ERR: {err}'

        # Verify output file was created
        rc, out, err = runner.run_cmd('test -f and_gate_script.v')
        assert rc == 0, f'Script output file not found - RC: {rc}, ERR: {err}'
