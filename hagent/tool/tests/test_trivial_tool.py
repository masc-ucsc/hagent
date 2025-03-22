# See LICENSE file for details

import os
import pytest
import subprocess
import tempfile
from unittest.mock import patch, MagicMock
from hagent.tool.trivial import Trivial
from hagent.tool.tool import Tool


def test_used_dot():
    dut = Trivial()

    assert dut._some_path == '/'
    assert dut.error_message == ''
    t = dut.some_method_related_to_the_tool('xx')
    assert t == 'xx/'
    assert dut.some_method_related_to_the_tool('xx') == 'xx/'

    x1 = dut.setup('potato')
    assert not x1
    assert dut.some_method_related_to_the_tool('xx') == 'xx/'
    assert dut.error_message != ''

    x2 = dut.setup('.')
    assert x2
    assert dut.some_method_related_to_the_tool('xx') == 'xx.'
    assert dut.error_message == ''


def test_is_ready_and_get_error():
    """Test is_ready() and get_error() methods."""
    dut = Trivial()
    
    # Initial state
    assert not dut.is_ready()
    assert dut.get_error() == ''
    
    # After setup failure
    dut.setup('invalid')
    assert not dut.is_ready()
    assert dut.get_error() != ''
    assert 'invalid setup option' in dut.get_error().lower()
    
    # After successful setup
    dut.setup('.')
    assert dut.is_ready()
    assert dut.get_error() == ''


def test_check_executable_with_path():
    """Test check_executable() with a specific path."""
    dut = Trivial()
    
    # Test with non-existent executable in specific path
    result = dut.check_executable('non_existent_exe', '/tmp')
    assert not result
    assert 'not found or not executable' in dut.error_message
    
    # Test with a file that exists but isn't executable
    with tempfile.NamedTemporaryFile(delete=False) as tmp:
        tmp_path = os.path.dirname(tmp.name)
        tmp_name = os.path.basename(tmp.name)
        try:
            # File exists but is not executable
            result = dut.check_executable(tmp_name, tmp_path)
            assert not result
            assert 'not executable' in dut.error_message.lower()
            
            # Make it executable and test again
            os.chmod(tmp.name, 0o755)
            # Reset error message before testing
            dut.error_message = ''
            result = dut.check_executable(tmp_name, tmp_path)
            assert result
            assert dut.error_message == ''
        finally:
            os.unlink(tmp.name)


def test_check_executable_path_env():
    """Test check_executable() using PATH environment."""
    dut = Trivial()
    
    # Test with executable that should exist in PATH (like python)
    result = dut.check_executable('python')
    assert result
    
    # Test with non-existent executable
    result = dut.check_executable('non_existent_executable_12345')
    assert not result
    assert 'not found in PATH' in dut.error_message


def test_run_command_success():
    """Test successful command execution."""
    dut = Trivial()
    
    # Run a simple command that should succeed
    result = dut.run_command(['echo', 'test'])
    assert result is not None
    assert result.returncode == 0
    assert 'test' in result.stdout


@patch('subprocess.run')
def test_run_command_timeout(mock_run):
    """Test command timeout handling."""
    dut = Trivial()
    
    # Set up the mock to raise a TimeoutExpired exception
    mock_run.side_effect = subprocess.TimeoutExpired(cmd=['test'], timeout=60)
    
    # Run the command and verify error handling
    result = dut.run_command(['test'])
    assert result is None
    assert 'timed out' in dut.error_message.lower()
    assert not dut.is_ready()


@patch('subprocess.run')
def test_run_command_error(mock_run):
    """Test command error handling."""
    dut = Trivial()
    
    # Set up the mock to raise a CalledProcessError
    mock_error = subprocess.CalledProcessError(1, ['test'])
    mock_error.returncode = 1
    mock_run.side_effect = mock_error
    
    # Run the command and verify error handling
    result = dut.run_command(['test'])
    assert result is None
    assert 'return code 1' in dut.error_message
    assert not dut.is_ready()


@patch('subprocess.run')
def test_run_command_generic_exception(mock_run):
    """Test generic exception handling in run_command."""
    dut = Trivial()
    
    # Set up the mock to raise a generic exception
    mock_run.side_effect = Exception('Generic error')
    
    # Run the command and verify error handling
    result = dut.run_command(['test'])
    assert result is None
    assert 'Error running command' in dut.error_message
    assert 'Generic error' in dut.error_message
    assert not dut.is_ready()


def test_abstract_setup_method():
    """Test the abstract setup method in the Tool class."""
    # Create a minimal subclass that implements setup but still calls the parent's setup
    class MinimalTool(Tool):
        def setup(self, *args, **kwargs):
            # Call the parent's setup method first to cover that line
            parent_result = super().setup(*args, **kwargs)
            # Then return a value
            return True
    
    # Instantiate the minimal tool
    tool = MinimalTool()
    
    # Call the setup method which will call the parent's setup
    result = tool.setup()
    
    # The method should return True as we implemented it
    assert result is True


if __name__ == '__main__':  # pragma: no cover
    test_used_dot()
