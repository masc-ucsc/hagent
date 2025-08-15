#!/usr/bin/env python3
"""
Pytest test suite for File_manager with Yosys synthesis tools.

This test suite validates File_manager functionality with the mascucsc/hagent-builder
Docker image which includes Yosys synthesis tools. Tests cover:
1. Basic Yosys synthesis commands
2. Verilog file processing
3. Synthesis output verification
4. Error handling for synthesis failures
5. Complex synthesis flows
"""

import tempfile
import os
import uuid
import pytest
from hagent.tool.file_manager import File_manager


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

    # Use local directories that tests can actually create and access
    repo_dir = os.path.abspath('.')  # Current working directory
    build_dir = os.path.join(tempfile.gettempdir(), 'hagent_test_build')
    cache_dir = os.path.join(tempfile.gettempdir(), 'hagent_test_cache')

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


class TestFileManagerYosys:
    """Test suite for File_manager with Yosys synthesis tools."""

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

        # Syntax error module (for error testing)
        files['syntax_error.v'] = """
module syntax_error(
  input  wire a,
  output wire y
);
  assign y = ~a  // Missing semicolon
endmodule
"""

        # Create temporary files
        temp_paths = {}
        for filename, content in files.items():
            temp_path = os.path.join(tempfile.gettempdir(), f'test_{uuid.uuid4().hex}_{filename}')
            with open(temp_path, 'w') as f:
                f.write(content)
            temp_paths[filename] = temp_path

        yield temp_paths

        # Cleanup
        for temp_path in temp_paths.values():
            if os.path.exists(temp_path):
                os.remove(temp_path)

    @pytest.fixture
    def yosys_manager(self):
        """Create and setup a File_manager instance with Yosys image."""
        fm = File_manager(image='mascucsc/hagent-builder:latest')
        assert fm.setup(), f'Setup failed: {fm.get_error()}'
        return fm

    def test_yosys_available(self, yosys_manager):
        """Test that Yosys is available in the container."""
        fm = yosys_manager

        # Check Yosys version
        rc, out, err = fm.run('yosys --version')
        assert rc == 0, f'Yosys not available - RC: {rc}, ERR: {err}'
        assert 'Yosys' in out, "Yosys version output should contain 'Yosys'"

        # Check help command works
        rc, out, err = fm.run('yosys --help')
        assert rc == 0, f'Yosys help failed - RC: {rc}, ERR: {err}'
        assert 'Usage:' in out or 'usage:' in out.lower()

    def test_simple_verilog_synthesis(self, yosys_manager, verilog_files):
        """Test basic Verilog synthesis with simple inverter."""
        fm = yosys_manager

        # Copy inverter file
        verilog_file = 'inverter.v'
        assert fm.copy_file(verilog_files[verilog_file], verilog_file), f'Copy failed: {fm.get_error()}'

        # Run basic synthesis check
        output_log = 'synthesis.log'
        yosys_command = f'yosys -p "read_verilog {verilog_file}; hierarchy -check" > {output_log} 2>&1'

        rc, stdout, stderr = fm.run(yosys_command)
        assert rc == 0, f'Yosys synthesis failed - RC: {rc}\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}'

        # Verify log file was created
        log_content = fm.get_file_content(output_log)
        assert log_content, f"Could not retrieve content of '{output_log}'"

        # Verify expected content in log
        assert 'simple_inverter' in log_content, 'Module name should appear in synthesis log'
        assert 'End of script.' in log_content, 'Synthesis should complete successfully'

        print(f'✓ Basic synthesis completed for {verilog_file}')

    def test_synthesis_with_statistics(self, yosys_manager, verilog_files):
        """Test synthesis with statistics generation."""
        fm = yosys_manager

        # Copy AND gate file
        verilog_file = 'and_gate.v'
        assert fm.copy_file(verilog_files[verilog_file], verilog_file)

        # Run synthesis with statistics
        yosys_command = f'yosys -p "read_verilog {verilog_file}; hierarchy -check; stat"'

        rc, stdout, stderr = fm.run(yosys_command)
        assert rc == 0, f'Yosys synthesis with stats failed - RC: {rc}\nSTDERR:\n{stderr}'

        # Verify statistics are in output
        assert 'and_gate' in stdout, 'Module name should appear in output'
        assert 'Number of cells:' in stdout or 'Printing statistics' in stdout, 'Should contain statistics'

        print(f'✓ Synthesis with statistics completed for {verilog_file}')

    def test_synthesis_to_json(self, yosys_manager, verilog_files):
        """Test synthesis with JSON netlist output."""
        fm = yosys_manager

        # Copy counter file (more complex design)
        verilog_file = 'counter.v'
        assert fm.copy_file(verilog_files[verilog_file], verilog_file)

        # Run synthesis to generate JSON
        json_output = 'counter_netlist.json'
        yosys_command = f'yosys -p "read_verilog {verilog_file}; hierarchy -check; proc; write_json {json_output}"'

        rc, stdout, stderr = fm.run(yosys_command)
        assert rc == 0, f'JSON synthesis failed - RC: {rc}\nSTDERR:\n{stderr}'

        # Verify JSON file was created and contains expected content
        json_content = fm.get_file_content(json_output)
        assert json_content, 'Could not retrieve JSON content'

        # Basic JSON structure validation
        assert '"modules"' in json_content, 'JSON should contain modules section'
        assert '"counter"' in json_content, 'JSON should contain counter module'

        # Verify it's valid JSON structure
        import json

        try:
            parsed_json = json.loads(json_content)
            assert 'modules' in parsed_json
            assert 'counter' in parsed_json['modules']
        except json.JSONDecodeError as e:
            pytest.fail(f'Generated JSON is not valid: {e}')

        print(f'✓ JSON synthesis completed for {verilog_file}')

    def test_synthesis_error_handling(self, yosys_manager, verilog_files):
        """Test error handling for Verilog files with syntax errors."""
        fm = yosys_manager

        # Copy file with syntax error
        verilog_file = 'syntax_error.v'
        assert fm.copy_file(verilog_files[verilog_file], verilog_file)

        # Try to synthesize file with syntax error
        yosys_command = f'yosys -p "read_verilog {verilog_file}; hierarchy -check"'

        rc, stdout, stderr = fm.run(yosys_command)
        # Should fail due to syntax error
        assert rc != 0, 'Synthesis should fail for file with syntax errors'

        # Error message should indicate the problem
        error_output = stdout + stderr
        assert 'syntax error' in error_output.lower() or 'error' in error_output.lower()

        print(f'✓ Error handling works correctly for {verilog_file}')

    def test_multiple_file_synthesis(self, yosys_manager, verilog_files):
        """Test synthesis with multiple Verilog files."""
        fm = yosys_manager

        # Copy multiple files
        files_to_copy = ['inverter.v', 'and_gate.v']
        for verilog_file in files_to_copy:
            assert fm.copy_file(verilog_files[verilog_file], verilog_file)

        # Synthesize multiple files
        file_list = ' '.join(files_to_copy)
        yosys_command = f'yosys -p "read_verilog {file_list}; hierarchy -check; stat"'

        rc, stdout, stderr = fm.run(yosys_command)
        assert rc == 0, f'Multi-file synthesis failed - RC: {rc}\nSTDERR:\n{stderr}'

        # Verify both modules are processed
        assert 'simple_inverter' in stdout, 'First module should be processed'
        assert 'and_gate' in stdout, 'Second module should be processed'

        print('✓ Multi-file synthesis completed')

    def test_synthesis_with_technology_mapping(self, yosys_manager, verilog_files):
        """Test synthesis with technology mapping."""
        fm = yosys_manager

        # Copy inverter file
        verilog_file = 'inverter.v'
        assert fm.copy_file(verilog_files[verilog_file], verilog_file)

        # Run synthesis with technology mapping
        verilog_output = 'mapped_inverter.v'
        yosys_command = f'yosys -p "read_verilog {verilog_file}; hierarchy -check; techmap; write_verilog {verilog_output}"'

        rc, stdout, stderr = fm.run(yosys_command)
        assert rc == 0, f'Technology mapping failed - RC: {rc}\nSTDERR:\n{stderr}'

        # Verify mapped Verilog was generated
        mapped_content = fm.get_file_content(verilog_output)
        assert mapped_content, 'Could not retrieve mapped Verilog content'
        assert 'module' in mapped_content, 'Mapped output should contain module definition'

        print(f'✓ Technology mapping completed for {verilog_file}')

    def test_patch_tracking_with_synthesis(self, yosys_manager, verilog_files):
        """Test that synthesis outputs are properly tracked in patches."""
        fm = yosys_manager

        # Copy original file
        verilog_file = 'inverter.v'
        assert fm.copy_file(verilog_files[verilog_file], verilog_file)

        fm.track_dir('.')

        # Run synthesis to create output files
        log_file = 'synthesis.log'
        json_file = 'netlist.json'
        yosys_command = f'yosys -p "read_verilog {verilog_file}; hierarchy -check; write_json {json_file}" > {log_file} 2>&1'

        rc, _, _ = fm.run(yosys_command)
        assert rc == 0

        # Check patch dictionary
        patches = fm.get_patch_dict()
        assert 'full' in patches and 'patch' in patches

        # New files should appear in 'full' section
        full_files = [item['filename'] for item in patches['full']]
        assert any(f.endswith(log_file) for f in full_files), f'Log file should be tracked in patches ({full_files})'
        assert any(f.endswith(json_file) for f in full_files), f'json file should be tracked in patches ({full_files})'

        print('✓ Synthesis outputs properly tracked in patches')

    def test_yosys_script_execution(self, yosys_manager, verilog_files):
        """Test execution of Yosys script files."""
        fm = yosys_manager

        # Copy Verilog file
        verilog_file = 'counter.v'
        assert fm.copy_file(verilog_files[verilog_file], verilog_file)

        # Create a Yosys script
        script_content = f"""
# Yosys synthesis script
read_verilog {verilog_file}
hierarchy -check
proc
stat
write_json counter_output.json
"""

        script_file = 'synthesis_script.ys'
        # Write script to container
        rc, _, _ = fm.run(f"cat > {script_file} << 'EOF'\n{script_content}\nEOF")
        assert rc == 0, 'Failed to create script file'

        # Execute the script
        rc, stdout, stderr = fm.run(f'yosys -s {script_file}')
        assert rc == 0, f'Script execution failed - RC: {rc}\nSTDERR:\n{stderr}'

        # Verify script outputs
        json_content = fm.get_file_content('counter_output.json')
        assert json_content, 'Script should generate JSON output'
        assert '"counter"' in json_content, 'JSON should contain counter module'

        print('✓ Yosys script execution completed')

    def test_synthesis_workflow_integration(self, yosys_manager, verilog_files):
        """Integration test for complete synthesis workflow."""
        fm = yosys_manager

        # Add extension tracking for Verilog files
        # Track working directory for different file types separately
        # Since track_dir only accepts one extension, we'll need to track all files
        fm.track_dir('.')

        # Copy original Verilog file
        verilog_file = 'and_gate.v'
        assert fm.copy_file(verilog_files[verilog_file], verilog_file)

        # Run complete synthesis flow
        commands = [
            f'yosys -p "read_verilog {verilog_file}; hierarchy -check" > read_check.log 2>&1',
            f'yosys -p "read_verilog {verilog_file}; hierarchy -check; stat" > synthesis_stats.log 2>&1',
            f'yosys -p "read_verilog {verilog_file}; hierarchy -check; write_json netlist.json"',
        ]

        for cmd in commands:
            rc, _, stderr = fm.run(cmd)
            assert rc == 0, f'Command failed: {cmd}\nError: {stderr}'

        # Verify all outputs exist
        expected_files = ['read_check.log', 'synthesis_stats.log', 'netlist.json']
        for expected_file in expected_files:
            content = fm.get_file_content(expected_file)
            assert content, f'File {expected_file} should exist and have content'

        # Export complete workflow as patches
        yaml_path = os.path.join(tempfile.gettempdir(), f'yosys_workflow_{uuid.uuid4().hex}.yaml')
        try:
            assert fm.save_patches(yaml_path, 'yosys_synthesis_workflow')
            assert os.path.exists(yaml_path)

            # Verify YAML structure
            import yaml

            with open(yaml_path, 'r') as f:
                data = yaml.safe_load(f)

            assert 'yosys_synthesis_workflow' in data
            workflow = data['yosys_synthesis_workflow']
            assert 'metadata' in workflow
            assert workflow['metadata']['image'] == 'mascucsc/hagent-builder:latest'

            print('✓ Complete workflow integration test passed')

        finally:
            if os.path.exists(yaml_path):
                os.remove(yaml_path)


# Standalone test function for direct execution
def test_yosys_integration():
    """Standalone integration test for Yosys functionality."""
    print('Running Yosys integration test...')

    # Create temporary Verilog file
    verilog_content = """
module simple_inverter(
  input  wire a,
  output wire y
);
  assign y = ~a;
endmodule
"""

    verilog_filename = 'inverter.v'
    verilog_host_path = os.path.join(tempfile.gettempdir(), f'test_{uuid.uuid4().hex}_{verilog_filename}')

    with open(verilog_host_path, 'w') as f:
        f.write(verilog_content)

    try:
        # Initialize File_manager with Yosys image
        fm = File_manager(image='mascucsc/hagent-builder:latest')
        assert fm.setup(), f'Setup failed: {fm.get_error()}'
        print(f"✓ Successfully set up environment with image '{fm.image}'")

        fm.track_dir('.')

        # Copy Verilog file
        assert fm.copy_file(host_path=verilog_host_path, container_path=verilog_filename), fm.get_error()
        print(f"✓ Copied '{verilog_filename}' into the container")

        # Run Yosys synthesis
        output_log = 'synthesis.log'
        yosys_command = f'yosys -p "read_verilog {verilog_filename}; hierarchy -check" > {output_log} 2>&1'
        print(f'Running command: {yosys_command}')

        rc, stdout, stderr = fm.run(yosys_command)
        assert rc == 0, f'Yosys run failed with exit code {rc}:\nSTDOUT:\n{stdout}\nSTDERR:\n{stderr}'
        print('✓ Yosys command executed successfully')

        # Retrieve and verify log content
        log_content = fm.get_file_content(output_log)
        assert log_content, f"Could not retrieve content of '{output_log}'"

        # Verify expected content
        assert 'simple_inverter' in log_content
        assert 'End of script.' in log_content
        print('✓ Verification successful: Log content contains expected synthesis information')

        # Verify patch tracking
        patches = fm.get_patch_dict()

        # Look for the synthesis.log file in patches (it might have full path)
        found_log_in_patch = any(output_log in item['filename'] for item in patches.get('full', []) + patches.get('patch', []))
        assert found_log_in_patch
        print(f"✓ Verification successful: Found '{output_log}' in patch dictionary")

        print('🎉 All Yosys integration tests passed!')

    finally:
        # Cleanup
        if os.path.exists(verilog_host_path):
            os.remove(verilog_host_path)


if __name__ == '__main__':
    test_yosys_integration()
