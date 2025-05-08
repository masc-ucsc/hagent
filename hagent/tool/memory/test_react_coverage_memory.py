# hagent/tool/memory/test_react_coverage_memory.py

"""
Test file specifically designed to increase coverage of the ReactMemory class.
This file targets uncovered lines in react_memory.py.
"""

import os
import tempfile
import unittest
from unittest.mock import patch, mock_open, MagicMock
from typing import List, Dict
from pathlib import Path

from hagent.tool.memory.react_memory import ReactMemory, insert_comment
from hagent.tool.compile import Diagnostic
from hagent.tool.memory.few_shot_memory_layer import FewShotMemory


class MockDiagnostic(Diagnostic):
    """Mock diagnostic for testing."""
    
    def __init__(self, msg: str, loc: int = 1, hint: str = ""):
        self.msg = msg
        self.loc = loc
        self.hint = hint
        self.error = msg  # For testing error type comparison
    
    def to_str(self) -> str:
        return f"Error at line {self.loc}: {self.msg}\nHint: {self.hint}"
    
    def insert_comment(self, code: str, prefix: str) -> str:
        """Insert a comment with diagnostic info into the code."""
        return insert_comment(code, self.to_str(), prefix, self.loc)


class MockDiagnosticWithError(Diagnostic):
    """Mock diagnostic that raises errors when methods are called."""
    
    def __init__(self, msg: str, loc: int = 1, hint: str = "", raise_on_insert: bool = False):
        self.msg = msg
        self.loc = loc
        self.hint = hint
        self.error = msg  # For testing error type comparison
        self.raise_on_insert = raise_on_insert
    
    def to_str(self) -> str:
        return f"Error at line {self.loc}: {self.msg}\nHint: {self.hint}"
    
    def insert_comment(self, code: str, prefix: str) -> str:
        """Insert a comment with diagnostic info into the code."""
        if self.raise_on_insert:
            raise ValueError("Simulated error in insert_comment")
        return code  # Just return the code unchanged for simplicity


class TestReactMemoryCoverage(unittest.TestCase):
    """Test class to increase coverage of ReactMemory."""
    
    def setUp(self):
        """Set up for tests."""
        self.react = ReactMemory()
        # Create a temporary DB file for testing
        self.temp_db = tempfile.NamedTemporaryFile(delete=False, suffix='.yaml')
        self.temp_db.close()
        
        # Create a data directory if it doesn't exist
        self.data_dir = Path("data")
        self.data_dir.mkdir(exist_ok=True)
    
    def tearDown(self):
        """Clean up after tests."""
        if os.path.exists(self.temp_db.name):
            os.remove(self.temp_db.name)
    
    def test_insert_comment(self):
        """Test the insert_comment function."""
        code = "line1\nline2\nline3\nline4\n"
        comment = "This is a comment\nwith multiple lines"
        
        # Insert at the beginning
        result = insert_comment(code, comment, "#", 1)
        self.assertIn("# This is a comment", result)
        
        # Insert in the middle
        result = insert_comment(code, comment, "//", 3)
        self.assertIn("// This is a comment", result)
        
        # Test with invalid location
        with self.assertRaises(ValueError):
            insert_comment(code, comment, "#", 10)
    
    def test_setup(self):
        """Test the setup method."""
        # Test with non-existent DB file and learn mode disabled
        result = self.react.setup(db_path="nonexistent.yaml", learn=False)
        self.assertFalse(result)
        self.assertIn("Database file not found or empty", self.react.error_message)
        
        # Test with non-existent DB file and learn mode enabled
        result = self.react.setup(db_path=self.temp_db.name, learn=True)
        self.assertTrue(result)
        self.assertIsNotNone(self.react._memory_system)
        
        # Test with no DB path (uses default path)
        result = self.react.setup(learn=True, max_iterations=10, comment_prefix="//")
        self.assertTrue(result)
        self.assertEqual(self.react._max_iterations, 10)
        self.assertEqual(self.react._lang_prefix, "//")
        self.assertIsNotNone(self.react._memory_system)
        
        # Test with exception during FewShotMemory initialization
        self.react = ReactMemory()  # Reset to a fresh state
        with patch('hagent.tool.memory.react_memory.FewShotMemory') as mock_memory:
            # Configure the mock to raise an exception when instantiated
            mock_memory.side_effect = Exception("Test exception")
            result = self.react.setup(db_path="test.yaml", learn=True)
            self.assertFalse(result)
            self.assertIn("Failed to initialize memory system", self.react.error_message)
    
    def test_find_error_example(self):
        """Test the _find_error_example method."""
        # Test with no memory system
        self.react._memory_system = None
        result = self.react._find_error_example("error_type1")
        self.assertEqual(result, {'fix_question': '', 'fix_answer': ''})
        
        # Setup with memory system but use a fresh instance to avoid test interference
        self.react = ReactMemory()
        self.react.setup(db_path=self.temp_db.name, learn=True)
        
        # Test with no matching memories
        result = self.react._find_error_example("error_type1")
        self.assertEqual(result, {'fix_question': '', 'fix_answer': ''})
        
        # Add a memory example and test again - but directly to memories dictionary, not using find
        memory_mock = MagicMock()
        memory_mock.error_type = "error_type1"
        memory_mock.faulty_code = "faulty code"
        memory_mock.fixed_code = "fixed code"
        
        # Don't attempt to use FewShotMemory.find in tests
        self.react._memory_system.find = MagicMock(return_value=[])
        self.react._memory_system.memories = {'id1': memory_mock}
        
        result = self.react._find_error_example("error_type1")
        self.assertEqual(result, {'fix_question': 'faulty code', 'fix_answer': 'fixed code'})
    
    def test_add_error_example(self):
        """Test the _add_error_example method."""
        # Test with no memory system
        self.react._memory_system = None
        # Should not raise error
        self.react._add_error_example("error_type1", "question1", "answer1")
        
        # Setup with memory system but use a fresh instance to avoid test interference
        self.react = ReactMemory()
        self.react.setup(db_path=self.temp_db.name, learn=True)
        
        # Mock the find method to avoid semantic search issues
        self.react._memory_system.find = MagicMock(return_value=[])
        
        # Mock the add method
        with patch.object(self.react._memory_system, 'add') as mock_add:
            # Return a mock ID
            mock_add.return_value = "test-memory-id"
            
            # Test with learn mode disabled
            self.react._learn_mode = False
            self.react._add_error_example("error_type1", "question1", "answer1")
            mock_add.assert_not_called()
            
            # Test with learn mode enabled
            self.react._learn_mode = True
            self.react._add_error_example("error_type1", "question1", "answer1")
            mock_add.assert_called_once()
            
            # Check call arguments
            args, kwargs = mock_add.call_args
            self.assertEqual(kwargs['original_code'], "question1")
            self.assertEqual(kwargs['fixed_code'], "answer1")
            self.assertIn("error_type1", kwargs['errors'][0])
            
            # Reset mock and test duplicate detection
            mock_add.reset_mock()
            
            # Create a memory example that matches
            memory_mock = MagicMock()
            memory_mock.error_type = "error_type1"
            memory_mock.faulty_code = "question1"  # Same as what we're trying to add
            
            self.react._memory_system.memories = {'id1': memory_mock}
            
            # Try to add again - should not call add because it's a duplicate
            self.react._add_error_example("error_type1", "question1", "answer1")
            mock_add.assert_not_called()
    
    def test_get_delta(self):
        """Test the _get_delta method."""
        code = "\n".join([f"line{i}" for i in range(1, 21)])
        
        # Test getting delta from the middle
        delta, start, end = self.react._get_delta(code, 10, window=3)
        self.assertEqual(start, 7)
        self.assertEqual(end, 13)
        self.assertIn("line7", delta)
        self.assertIn("line13", delta)
        
        # Test getting delta from the beginning
        delta, start, end = self.react._get_delta(code, 1, window=3)
        self.assertEqual(start, 1)
        self.assertEqual(end, 4)
        
        # Test getting delta from the end
        delta, start, end = self.react._get_delta(code, 20, window=3)
        self.assertEqual(start, 17)
        self.assertEqual(end, 20)
    
    def test_apply_patch(self):
        """Test the _apply_patch method."""
        full_code = "\n".join([f"line{i}" for i in range(1, 11)])
        patch = "patched_line1\npatched_line2\n"
        
        # Apply patch in the middle
        result = self.react._apply_patch(full_code, patch, 4, 6)
        self.assertIn("line3", result)
        self.assertIn("patched_line1", result)
        self.assertIn("patched_line2", result)
        self.assertIn("line7", result)
        self.assertNotIn("line4", result)
        self.assertNotIn("line5", result)
        self.assertNotIn("line6", result)
        
        # Apply patch at the beginning
        result = self.react._apply_patch(full_code, patch, 1, 2)
        self.assertIn("patched_line1", result)
        self.assertIn("line3", result)
        self.assertTrue(result.startswith("patched_line1"))
        self.assertFalse(result.startswith("line1"))
        
        # Apply patch at the end
        result = self.react._apply_patch(full_code, patch, 9, 10)
        self.assertIn("line8", result)
        self.assertIn("patched_line1", result)
        self.assertFalse("line9\n" in result)
        self.assertFalse("line10" in result)
    
    def test_get_log(self):
        """Test the get_log method."""
        self.react.setup()
        self.assertEqual(self.react.get_log(), [])
        
        # Add some log entries
        self.react._log.append({"iteration": 1, "check": None, "fix": None})
        logs = self.react.get_log()
        self.assertEqual(len(logs), 1)
        self.assertEqual(logs[0]["iteration"], 1)
    
    def test_react_cycle_success(self):
        """Test the react_cycle method with successful fix."""
        # Setup with memory
        db_path = str(self.data_dir / "test_react_memory_success.yaml")
        self.react.setup(db_path=db_path, max_iterations=3, learn=True)
        
        # Mock callbacks
        def check_callback(code: str) -> List[Diagnostic]:
            if "error" in code:
                return [MockDiagnostic("Test error", 1)]
            return []
        
        # Track if fix_callback was called
        fix_called = [False]
        
        def fix_callback(code: str, diag: Diagnostic, fix_example: Dict[str, str], delta: bool, iteration: int) -> str:
            fix_called[0] = True
            # For debugging
            print(f"Fix callback called with code: {code}")
            return "This code has a fixed"
        
        # Test with code that has an error
        result = self.react.react_cycle("This code has an error", check_callback, fix_callback)
        
        # Verify fix_callback was called
        self.assertTrue(fix_called[0], "Fix callback was not called")

        self.assertIn("This code has a fixed", result)
        self.assertIn("This code has a fixed", self.react.last_code)
        
        # Check log
        logs = self.react.get_log()
        self.assertEqual(len(logs), 1)
        self.assertEqual(logs[0]["iteration"], 1)
    
    def test_react_cycle_failure(self):
        """Test the react_cycle method with unsuccessful fix."""
        # Setup with memory
        db_path = str(self.data_dir / "test_react_memory_failure.yaml")
        self.react.setup(db_path=db_path, max_iterations=3, learn=True)
        
        # Mock callbacks
        def check_callback(code: str) -> List[Diagnostic]:
            return [MockDiagnostic("Test error", 1)]
        
        def fix_callback(code: str, diag: Diagnostic, fix_example: Dict[str, str], delta: bool, iteration: int) -> str:
            return code  # Return the same code (no fix)
        
        # Test with code that has an error that can't be fixed
        result = self.react.react_cycle("This code has an error", check_callback, fix_callback)
        self.assertEqual(result, "")  # Should return empty string if can't fix
        self.assertIn("This code has an error", self.react.last_code)
        
        # Check log
        logs = self.react.get_log()
        self.assertEqual(len(logs), 3)  # Should have 3 iterations
    
    def test_react_cycle_learning(self):
        """Test the react_cycle method with learning enabled."""
        # Setup with memory
        db_path = str(self.data_dir / "test_react_memory_learning.yaml")
        self.react.setup(db_path=db_path, max_iterations=3, learn=True)
        
        # Mock the _add_error_example method to monitor calls
        with patch.object(self.react, '_add_error_example') as mock_add:
            # Mock callbacks
            def check_callback(code: str) -> List[Diagnostic]:
                if "error1" in code:
                    return [MockDiagnostic("Error type 1", 1)]
                elif "error2" in code:
                    return [MockDiagnostic("Error type 2", 2)]
                return []
            
            def fix_callback(code: str, diag: Diagnostic, fix_example: Dict[str, str], delta: bool, iteration: int) -> str:
                if "error1" in code:
                    return code.replace("an error1", "a fixed1")
                return code
            
            # Test with code that has an error that can be fixed
            result = self.react.react_cycle("This code has an error1", check_callback, fix_callback)
            self.assertIn("This code has a fixed1", result)
            
            # Check if the error example was added
            mock_add.assert_called_once()
            
            # Reset mock and test with code that has a different error that can't be fixed
            mock_add.reset_mock()
            result = self.react.react_cycle("This code has an error2", check_callback, fix_callback)
            self.assertEqual(result, "")  # Should return empty string if can't fix
            
            # Should not be called for unsuccessful fix
            mock_add.assert_not_called()
    
    def test_react_cycle_not_ready(self):
        """Test the react_cycle method when ReactMemory is not ready."""
        # Don't call setup, so _is_ready is False
        result = self.react.react_cycle("code", lambda x: [], lambda x, y, z, d, i: x)
        self.assertEqual(result, "")
        self.assertIn("not ready", self.react.error_message)
    
    def test_react_cycle_insert_comment_exception_in_delta(self):
        """Test react_cycle when insert_comment raises an exception in delta mode."""
        # Setup with memory
        db_path = str(self.data_dir / "test_react_memory_exception.yaml")
        self.react.setup(db_path=db_path, max_iterations=3, learn=True)
        
        # Mock callbacks
        def check_callback(code: str) -> List[Diagnostic]:
            return [MockDiagnosticWithError("Test error", 1, raise_on_insert=True)]
        
        def fix_callback(code: str, diag: Diagnostic, fix_example: Dict[str, str], delta: bool, iteration: int) -> str:
            return code.replace("error", "fixed")
        
        # Test with code that will cause an exception in insert_comment
        result = self.react.react_cycle("This code has an error", check_callback, fix_callback)
        self.assertEqual(result, "")  # Should return empty string on error
        self.assertIn("Failed to insert diagnostic comment in delta", self.react.error_message)
        
        # Check log
        logs = self.react.get_log()
        self.assertEqual(len(logs), 1)
    
    def test_react_cycle_insert_comment_exception_in_full(self):
        """Test react_cycle when insert_comment raises an exception in full code mode."""
        # Setup with memory
        db_path = str(self.data_dir / "test_react_memory_exception2.yaml")
        self.react.setup(db_path=db_path, max_iterations=3, learn=True)
        
        # Mock callbacks with a counter to control when to raise the exception
        iteration_counter = [0]
        
        def check_callback(code: str) -> List[Diagnostic]:
            iteration_counter[0] += 1
            if iteration_counter[0] == 1:
                # First iteration - return a normal diagnostic
                return [MockDiagnosticWithError("Test error", 1)]
            else:
                # Second iteration - return a diagnostic that raises on insert
                return [MockDiagnosticWithError("Test error", 1, raise_on_insert=True)]
        
        def fix_callback(code: str, diag: Diagnostic, fix_example: Dict[str, str], delta: bool, iteration: int) -> str:
            # Return a modified code that still has an error
            return code + " modified"
        
        # Test with code that will cause an exception in insert_comment on the second iteration
        result = self.react.react_cycle("This code has an error", check_callback, fix_callback)
        self.assertEqual(result, "")  # Should return empty string on error
        self.assertIn("Failed to insert diagnostic comment", self.react.error_message)
        
        # Check log
        logs = self.react.get_log()
        self.assertEqual(len(logs), 2)  # Should have 2 iterations


if __name__ == "__main__":
    unittest.main()