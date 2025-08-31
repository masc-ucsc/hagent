#!/usr/bin/env python3
"""
Pytest test suite for Equiv_check with Docker fallback functionality.

This test suite validates Equiv_check functionality with the mascucsc/hagent-builder
Docker image which includes Yosys synthesis tools. Tests cover:
1. Docker fallback when local Yosys is not available
2. Equivalence checking with Docker backend
3. Error handling in Docker mode
4. File management and result copying from Docker
5. Integration with File_manager for Docker operations
"""

import os
import pytest
from hagent.tool.equiv_check import Equiv_check


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
    # Use home directory subfolders which Docker Desktop has access to by default
    home_dir = os.path.expanduser('~')
    # IMPORTANT: Don't use repository root directory - use home subdirectory instead
    repo_dir = os.path.join(home_dir, 'hagent_test_repo')  # Use subdirectory instead of '.'
    build_dir = os.path.join(home_dir, 'hagent_test_build')
    cache_dir = os.path.join(home_dir, 'hagent_test_cache')

    # Create directories if they don't exist
    os.makedirs(repo_dir, exist_ok=True)
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


class TestEquivCheckDocker:
    """Test suite for Equiv_check with Docker fallback functionality."""

    @pytest.fixture
    def verilog_modules(self):
        """Create test Verilog modules for equivalence testing."""
        modules = {}

        # Simple inverter - two equivalent implementations
        modules['inverter_gold'] = """
module simple_inverter(
  input  wire a,
  output wire y
);
  assign y = ~a;
endmodule
"""

        modules['inverter_gate'] = """
module simple_inverter(
  input  wire a,
  output wire y
);
  assign y = !a;  // Different syntax but logically equivalent
endmodule
"""

        # AND gate - two equivalent implementations
        modules['and_gold'] = """
module simple_and(
  input  wire a,
  input  wire b,
  output wire y
);
  assign y = a & b;
endmodule
"""

        modules['and_gate'] = """
module simple_and(
  input  wire a,
  input  wire b,
  output wire y
);
  assign y = a && b;  // Different syntax but equivalent for single bits
endmodule
"""

        # Non-equivalent designs
        modules['inverter_non_equiv'] = """
module simple_inverter(
  input  wire a,
  output wire y
);
  assign y = a;  // Buffer instead of inverter - not equivalent
endmodule
"""

        # Syntax error module - use same module name as gold for testing
        modules['syntax_error'] = """
module simple_inverter(
  input  wire a,
  output wire y
);
  assign y = ~a  // Missing semicolon
endmodule
"""

        return modules

    def test_docker_fallback_setup(self):
        """Test that Docker fallback setup works correctly."""
        equiv_checker = Equiv_check()

        # Force Docker fallback by directly calling the Docker setup method
        docker_success = equiv_checker._setup_docker_fallback()

        print('HELLO')

        if not docker_success:
            print(f'Docker setup failed: {equiv_checker.get_error()}')
            pytest.skip(f'Docker setup failed: {equiv_checker.get_error()}')

        assert equiv_checker.use_docker is True
        assert equiv_checker.yosys_installed is True
        assert equiv_checker.file_tracker is not None
        print('✓ Docker fallback setup successful')

    def test_docker_equivalent_designs(self, verilog_modules):
        """Test equivalence checking with equivalent designs using Docker."""
        equiv_checker = Equiv_check()

        # Force Docker usage
        docker_success = equiv_checker._setup_docker_fallback()
        if not docker_success:
            pytest.skip(f'Docker setup failed: {equiv_checker.get_error()}')

        # Test inverter equivalence
        result = equiv_checker.check_equivalence(
            gold_code=verilog_modules['inverter_gold'], gate_code=verilog_modules['inverter_gate'], desired_top='simple_inverter'
        )

        assert result is True, 'Equivalent inverter designs should be detected as equivalent'
        assert equiv_checker.get_counterexample() is None
        print('✓ Docker equivalence check passed for equivalent inverter designs')

    def test_docker_and_gate_equivalence(self, verilog_modules):
        """Test equivalence checking with AND gate designs using Docker."""
        equiv_checker = Equiv_check()

        # Force Docker usage
        docker_success = equiv_checker.setup()
        if not docker_success:
            pytest.skip(f'Docker setup failed: {equiv_checker.get_error()}')

        # Test AND gate equivalence
        result = equiv_checker.check_equivalence(
            gold_code=verilog_modules['and_gold'], gate_code=verilog_modules['and_gate'], desired_top='simple_and'
        )

        assert result is True, 'Equivalent AND gate designs should be detected as equivalent'
        print('✓ Docker equivalence check passed for equivalent AND gate designs')

    def test_docker_non_equivalent_designs(self, verilog_modules):
        """Test equivalence checking with non-equivalent designs using Docker."""
        equiv_checker = Equiv_check()

        # Force Docker usage
        docker_success = equiv_checker._setup_docker_fallback()
        if not docker_success:
            pytest.skip(f'Docker setup failed: {equiv_checker.get_error()}')

        # Test non-equivalent designs
        result = equiv_checker.check_equivalence(
            gold_code=verilog_modules['inverter_gold'],
            gate_code=verilog_modules['inverter_non_equiv'],
            desired_top='simple_inverter',
        )

        assert result is False, 'Non-equivalent designs should be detected as different'

        # Check for counterexample information
        counterexample = equiv_checker.get_counterexample()
        if counterexample:
            print(f'✓ Counterexample detected: {counterexample}')
        else:
            print('✓ Non-equivalence correctly detected')

    def test_docker_syntax_error_handling(self, verilog_modules):
        """Test error handling with syntax errors in Docker mode."""
        equiv_checker = Equiv_check()

        # Force Docker usage
        docker_success = equiv_checker._setup_docker_fallback()
        if not docker_success:
            pytest.skip(f'Docker setup failed: {equiv_checker.get_error()}')

        # Test with syntax error - should return False
        result = equiv_checker.check_equivalence(
            gold_code=verilog_modules['inverter_gold'], gate_code=verilog_modules['syntax_error'], desired_top='simple_inverter'
        )

        # Syntax errors typically result in False (failed equivalence check)
        assert result is False, 'Syntax errors should result in failed equivalence check'
        print('✓ Docker syntax error handling works correctly')

    def test_docker_file_management(self, verilog_modules):
        """Test that files are properly managed between Docker container and host."""
        equiv_checker = Equiv_check()

        # Force Docker usage
        docker_success = equiv_checker._setup_docker_fallback()
        if not docker_success:
            pytest.skip(f'Docker setup failed: {equiv_checker.get_error()}')

        # Perform equivalence check
        equiv_checker.check_equivalence(
            gold_code=verilog_modules['inverter_gold'], gate_code=verilog_modules['inverter_gate'], desired_top='simple_inverter'
        )

        # Verify that file_tracker was used
        assert equiv_checker.file_tracker is not None
        assert equiv_checker.use_docker is True

        # Check that patches were tracked (indicates files were managed)
        patches = equiv_checker.file_tracker.get_patch_dict()
        assert 'full' in patches or 'patch' in patches

        print('✓ Docker file management working correctly')

    def test_setup_docker_fallback_integration(self):
        """Test integration of setup method with Docker fallback."""
        equiv_checker = Equiv_check()

        # Call regular setup - it should try local first, then Docker if needed
        setup_success = equiv_checker.setup()

        assert setup_success is True, f'Setup should succeed with local or Docker: {equiv_checker.get_error()}'
        assert equiv_checker.yosys_installed is True

        # Check which mode it's using
        if equiv_checker.use_docker:
            print('✓ Setup using Docker fallback')
            assert equiv_checker.file_tracker is not None
        else:
            print('✓ Setup using local Yosys installation')

        print(f'✓ Setup successful - Docker mode: {equiv_checker.use_docker}')

    def test_docker_multiple_checks(self, verilog_modules):
        """Test multiple equivalence checks with same Docker instance."""
        equiv_checker = Equiv_check()

        # Force Docker usage
        docker_success = equiv_checker._setup_docker_fallback()
        if not docker_success:
            pytest.skip(f'Docker setup failed: {equiv_checker.get_error()}')

        # First check - equivalent designs
        result1 = equiv_checker.check_equivalence(
            gold_code=verilog_modules['inverter_gold'], gate_code=verilog_modules['inverter_gate'], desired_top='simple_inverter'
        )

        # Second check - non-equivalent designs
        result2 = equiv_checker.check_equivalence(
            gold_code=verilog_modules['inverter_gold'],
            gate_code=verilog_modules['inverter_non_equiv'],
            desired_top='simple_inverter',
        )

        # Third check - different module type
        result3 = equiv_checker.check_equivalence(
            gold_code=verilog_modules['and_gold'], gate_code=verilog_modules['and_gate'], desired_top='simple_and'
        )

        assert result1 is True, 'First check should detect equivalence'
        assert result2 is False, 'Second check should detect non-equivalence'
        assert result3 is True, 'Third check should detect equivalence'

        print('✓ Multiple Docker checks completed successfully')

    def test_docker_error_cases(self):
        """Test various error cases in Docker mode."""
        equiv_checker = Equiv_check()

        # Force Docker usage
        docker_success = equiv_checker._setup_docker_fallback()
        if not docker_success:
            pytest.skip(f'Docker setup failed: {equiv_checker.get_error()}')

        # Test with invalid module names - specified top module not found
        with pytest.raises(ValueError, match='Specified top module .* not found'):
            equiv_checker.check_equivalence(
                gold_code='// No module here', gate_code='module test(); endmodule', desired_top='nonexistent'
            )

        print('✓ Docker error case handling works correctly')


# Standalone test functions for direct execution
def test_docker_integration_standalone():
    """Standalone integration test for Docker functionality."""
    print('Running Docker integration test...')

    # Simple test modules
    gold_code = """
module simple_test(
  input  wire a,
  output wire y
);
  assign y = ~a;
endmodule
"""

    gate_code = """
module simple_test(
  input  wire a,
  output wire y
);
  assign y = !a;
endmodule
"""

    # Setup temporary environment for standalone run
    repo_dir = os.environ.get('HAGENT_REPO_DIR')
    build_dir = os.environ.get('HAGENT_BUILD_DIR')
    cache_dir = os.environ.get('HAGENT_CACHE_DIR')

    home_dir = os.path.expanduser('~')
    if not repo_dir:
        repo_dir = os.path.join(home_dir, 'hagent_test_repo')
        os.makedirs(repo_dir, exist_ok=True)
        os.environ['HAGENT_REPO_DIR'] = repo_dir
    if not build_dir:
        build_dir = os.path.join(home_dir, 'hagent_test_build')
        os.makedirs(build_dir, exist_ok=True)
        os.environ['HAGENT_BUILD_DIR'] = build_dir
    if not cache_dir:
        cache_dir = os.path.join(home_dir, 'hagent_test_cache')
        os.makedirs(cache_dir, exist_ok=True)
        os.environ['HAGENT_CACHE_DIR'] = cache_dir

    os.environ['HAGENT_EXECUTION_MODE'] = 'docker'

    try:
        # Test Docker fallback setup
        equiv_checker = Equiv_check()
        docker_success = equiv_checker._setup_docker_fallback()

        if not docker_success:
            print(f'Docker setup failed: {equiv_checker.get_error()}')
            return False

        print(f'✓ Docker setup successful - using Docker: {equiv_checker.use_docker}')

        # Run equivalence check
        result = equiv_checker.check_equivalence(gold_code=gold_code, gate_code=gate_code, desired_top='simple_test')

        print(f'gold_code:{gold_code}')
        print(f'gate_code:{gate_code}')
        print(f'✓ Equivalence check result: {result}')

        if result is True:
            print('✓ Docker integration test passed')
            return True
        else:
            print('✗ Docker integration test failed')
            return False

    except Exception as e:
        print(f'✗ Docker integration test exception: {e}')
        return False


if __name__ == '__main__':
    # Run standalone test
    success = test_docker_integration_standalone()

    if success:
        print(' 🎉 Docker integration test passed!')
    else:
        print(' ❌ Docker integration test failed')
        exit(1)
