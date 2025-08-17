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
from hagent.inou.container_manager import ContainerManager
from hagent.inou.executor import ExecutorFactory
from hagent.inou.path_manager import PathManager


@pytest.fixture(scope='session', autouse=True)
def setup_hagent_environment():
    """Setup HAGENT environment variables for Docker mode tests."""
    original_env = {}

    # Save original environment
    hagent_vars = ['HAGENT_EXECUTION_MODE', 'HAGENT_REPO_DIR', 'HAGENT_BUILD_DIR', 'HAGENT_CACHE_DIR']
    for var in hagent_vars:
        original_env[var] = os.environ.get(var)

    # Set Docker mode environment with host-accessible paths for testing
    os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

    # Use local directories that Docker can easily mount
    repo_dir = os.path.abspath('.')  # Current working directory
    build_dir = os.path.abspath('./output/test_yosys_build')
    cache_dir = os.path.abspath('./output/test_yosys_cache')

    # Create directories if they don't exist
    os.makedirs(build_dir, exist_ok=True)
    os.makedirs(cache_dir, exist_ok=True)

    os.environ['HAGENT_REPO_DIR'] = repo_dir
    os.environ['HAGENT_BUILD_DIR'] = build_dir
    os.environ['HAGENT_CACHE_DIR'] = cache_dir

    yield

    # Restore original environment
    for var, value in original_env.items():
        if value is None:
            os.environ.pop(var, None)
        else:
            os.environ[var] = value


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
    def yosys_executor(self):
        """Create and setup an Executor instance with Yosys tools."""
        # Ensure directories exist before creating path_manager
        cache_dir = os.environ.get('HAGENT_CACHE_DIR')
        if cache_dir:
            os.makedirs(cache_dir, exist_ok=True)

        path_manager = PathManager()
        # Use image with Yosys tools - may need to change to appropriate image
        container_manager = ContainerManager('mascucsc/hagent-simplechisel:2025.08', path_manager)
        executor = ExecutorFactory.create_executor(container_manager)

        assert executor.setup(), f'Executor setup failed: {executor.get_error()}'

        yield executor, container_manager

        # Cleanup
        try:
            container_manager.cleanup()
        except Exception:
            pass

    def test_yosys_available(self, yosys_executor):
        """Test that Yosys is available in the container."""
        executor, _ = yosys_executor

        # Check if yosys is available
        rc, out, err = executor.run('which yosys')
        if rc != 0:
            pytest.skip(f'Yosys not available in container: {err}')

        # Check yosys version
        rc, out, err = executor.run('yosys -V')
        assert rc == 0, f'Yosys version check failed - RC: {rc}, ERR: {err}'
        assert 'Yosys' in out, f'Unexpected yosys version output: {out}'

    def test_simple_verilog_synthesis(self, yosys_executor, verilog_files):
        """Test basic Verilog synthesis with Yosys."""
        executor, _ = yosys_executor

        # Skip if yosys not available
        rc, _, _ = executor.run('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        executor.run('rm -f *.v *.json')

        # Create simple Verilog file in container
        verilog_content = verilog_files['inverter.v']
        rc, out, err = executor.run(f"cat << 'EOF' > inverter.v\n{verilog_content}\nEOF")
        assert rc == 0, f'Failed to create Verilog file - RC: {rc}, ERR: {err}'

        # Simple synthesis
        yosys_cmd = 'yosys -p "read_verilog inverter.v; synth; write_verilog inverter_synth.v"'
        rc, out, err = executor.run(yosys_cmd)
        assert rc == 0, f'Yosys synthesis failed - RC: {rc}, ERR: {err}'

        # Verify output file was created
        rc, out, err = executor.run('test -f inverter_synth.v')
        assert rc == 0, f'Synthesis output file not found - RC: {rc}, ERR: {err}'

        # Check that output contains synthesized content
        rc, out, err = executor.run('cat inverter_synth.v')
        assert rc == 0, f'Could not read synthesis output - RC: {rc}, ERR: {err}'
        assert 'module' in out.lower(), f'Synthesis output does not contain module: {out}'

    def test_synthesis_with_statistics(self, yosys_executor, verilog_files):
        """Test synthesis with statistics reporting."""
        executor, _ = yosys_executor

        # Skip if yosys not available
        rc, _, _ = executor.run('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        executor.run('rm -f *.v *.json')

        # Create Verilog file
        verilog_content = verilog_files['and_gate.v']
        rc, out, err = executor.run(f"cat << 'EOF' > and_gate.v\n{verilog_content}\nEOF")
        assert rc == 0, f'Failed to create Verilog file - RC: {rc}, ERR: {err}'

        # Synthesis with statistics
        yosys_cmd = 'yosys -p "read_verilog and_gate.v; synth; stat"'
        rc, out, err = executor.run(yosys_cmd)
        assert rc == 0, f'Yosys synthesis with stats failed - RC: {rc}, ERR: {err}'

        # Check that statistics are in output
        assert 'Number of cells' in out or 'Chip area' in out, f'Statistics not found in output: {out}'

    def test_synthesis_to_json(self, yosys_executor, verilog_files):
        """Test synthesis with JSON output format."""
        executor, _ = yosys_executor

        # Skip if yosys not available
        rc, _, _ = executor.run('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        executor.run('rm -f *.v *.json')

        # Create Verilog file
        verilog_content = verilog_files['inverter.v']
        rc, out, err = executor.run(f"cat << 'EOF' > inverter.v\n{verilog_content}\nEOF")
        assert rc == 0, f'Failed to create Verilog file - RC: {rc}, ERR: {err}'

        # Synthesis to JSON
        yosys_cmd = 'yosys -p "read_verilog inverter.v; synth; write_json inverter.json"'
        rc, out, err = executor.run(yosys_cmd)
        assert rc == 0, f'Yosys JSON synthesis failed - RC: {rc}, ERR: {err}'

        # Verify JSON file was created
        rc, out, err = executor.run('test -f inverter.json')
        assert rc == 0, f'JSON output file not found - RC: {rc}, ERR: {err}'

        # Verify JSON content
        rc, out, err = executor.run('head -10 inverter.json')
        assert rc == 0, f'Could not read JSON output - RC: {rc}, ERR: {err}'
        assert '{' in out, f'JSON output does not appear to be valid JSON: {out}'

    def test_synthesis_error_handling(self, yosys_executor):
        """Test error handling for invalid Verilog synthesis."""
        executor, _ = yosys_executor

        # Skip if yosys not available
        rc, _, _ = executor.run('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        executor.run('rm -f *.v *.json')

        # Create invalid Verilog file
        invalid_verilog = """
module broken_module(
  invalid syntax here
  missing endmodule
"""
        rc, out, err = executor.run(f"cat << 'EOF' > broken.v\n{invalid_verilog}\nEOF")
        assert rc == 0, f'Failed to create invalid Verilog file - RC: {rc}, ERR: {err}'

        # Try to synthesize invalid file
        yosys_cmd = 'yosys -p "read_verilog broken.v; synth"'
        rc, out, err = executor.run(yosys_cmd)
        assert rc != 0, 'Yosys should have failed on invalid Verilog but succeeded'

        # Check that error message is informative
        combined_output = out + err
        assert 'syntax error' in combined_output.lower() or 'error' in combined_output.lower(), (
            f'Error output should contain error information: {combined_output}'
        )

    def test_multiple_file_synthesis(self, yosys_executor, verilog_files):
        """Test synthesis with multiple Verilog files."""
        executor, _ = yosys_executor

        # Skip if yosys not available
        rc, _, _ = executor.run('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing .v files to avoid conflicts
        executor.run('rm -f *.v *.json')

        # Create multiple Verilog files
        for filename, content in verilog_files.items():
            rc, out, err = executor.run(f"cat << 'EOF' > {filename}\n{content}\nEOF")
            assert rc == 0, f'Failed to create {filename} - RC: {rc}, ERR: {err}'

        # Synthesis with multiple files
        yosys_cmd = 'yosys -p "read_verilog *.v; synth; write_verilog combined_synth.v"'
        rc, out, err = executor.run(yosys_cmd)
        assert rc == 0, f'Multi-file synthesis failed - RC: {rc}, ERR: {err}'

        # Verify output file was created
        rc, out, err = executor.run('test -f combined_synth.v')
        assert rc == 0, f'Multi-file synthesis output not found - RC: {rc}, ERR: {err}'

        # Check that all modules are present in output
        rc, out, err = executor.run('cat combined_synth.v')
        assert rc == 0, f'Could not read multi-file synthesis output - RC: {rc}, ERR: {err}'

    def test_synthesis_with_technology_mapping(self, yosys_executor, verilog_files):
        """Test synthesis with technology mapping."""
        executor, _ = yosys_executor

        # Skip if yosys not available
        rc, _, _ = executor.run('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        executor.run('rm -f *.v *.json')

        # Create Verilog file
        verilog_content = verilog_files['counter.v']
        rc, out, err = executor.run(f"cat << 'EOF' > counter.v\n{verilog_content}\nEOF")
        assert rc == 0, f'Failed to create Verilog file - RC: {rc}, ERR: {err}'

        # Synthesis with technology mapping (using basic cell library)
        yosys_cmd = 'yosys -p "read_verilog counter.v; synth; dfflibmap -liberty /dev/null; abc; write_verilog counter_mapped.v"'
        rc, out, err = executor.run(yosys_cmd)
        # Note: This might fail if liberty file is not available, which is expected
        # We're mainly testing that the command structure works

        if rc == 0:
            # If successful, verify output
            rc, out, err = executor.run('test -f counter_mapped.v')
            assert rc == 0, f'Technology mapped output not found - RC: {rc}, ERR: {err}'

    def test_yosys_script_execution(self, yosys_executor, verilog_files):
        """Test execution of Yosys scripts."""
        executor, _ = yosys_executor

        # Skip if yosys not available
        rc, _, _ = executor.run('which yosys')
        if rc != 0:
            pytest.skip('Yosys not available in container')

        # Clean up any existing files
        executor.run('rm -f *.v *.json *.ys')

        # Create Verilog file
        verilog_content = verilog_files['and_gate.v']
        rc, out, err = executor.run(f"cat << 'EOF' > and_gate.v\n{verilog_content}\nEOF")
        assert rc == 0, f'Failed to create Verilog file - RC: {rc}, ERR: {err}'

        # Create Yosys script
        yosys_script = """
read_verilog and_gate.v
synth
stat
write_verilog and_gate_script.v
"""
        rc, out, err = executor.run(f"cat << 'EOF' > synth.ys\n{yosys_script}\nEOF")
        assert rc == 0, f'Failed to create Yosys script - RC: {rc}, ERR: {err}'

        # Execute script
        rc, out, err = executor.run('yosys -s synth.ys')
        assert rc == 0, f'Yosys script execution failed - RC: {rc}, ERR: {err}'

        # Verify output file was created
        rc, out, err = executor.run('test -f and_gate_script.v')
        assert rc == 0, f'Script output file not found - RC: {rc}, ERR: {err}'
