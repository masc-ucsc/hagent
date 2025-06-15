#!/usr/bin/env python3
"""
Test file specifically designed to increase coverage of the React class.
This file targets uncovered lines in react.py.
"""

import os
import tempfile
import unittest
from unittest.mock import patch, mock_open, MagicMock
from typing import List, Dict

from hagent.tool.react import React, process_multiline_strings, insert_comment
from hagent.tool.compile import Diagnostic


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


class TestReactCoverage(unittest.TestCase):
    """Test class to increase coverage of React."""
    
    def setUp(self):
        """Set up for tests."""
        self.react = React()
        # Create a temporary DB file for testing
        self.temp_db = tempfile.NamedTemporaryFile(delete=False, suffix='.yaml')
        self.temp_db.close()
    
    def tearDown(self):
        """Clean up after tests."""
        if os.path.exists(self.temp_db.name):
            os.remove(self.temp_db.name)
    
    def test_process_multiline_strings(self):
        """Test the process_multiline_strings function."""
        # Test with a dictionary
        test_dict = {"key1": "value1", "key2": "value2\nwith\nnewlines"}
        result = process_multiline_strings(test_dict)
        self.assertEqual(result["key1"], "value1")
        # Check the type instead of comparing values
        from ruamel.yaml.scalarstring import LiteralScalarString
        self.assertIsInstance(result["key2"], LiteralScalarString)
        
        # Test with a list
        test_list = ["item1", "item2\nwith\nnewlines"]
        result = process_multiline_strings(test_list)
        self.assertEqual(result[0], "item1")
        self.assertIsInstance(result[1], LiteralScalarString)
        
        # Test with a simple string without newlines
        test_str = "simple string"
        result = process_multiline_strings(test_str)
        self.assertEqual(result, "simple string")
    
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
        """Test the setup method with FewShotMemory."""
        # Fails when the DB file does not exist and learning is disabled
        result = self.react.setup(db_path="nonexistent.yaml", learn=False)
        self.assertFalse(result)
        self.assertIn("Database file not found", self.react.error_message)

        # Creates a new cache when learning is enabled
        result = self.react.setup(db_path=self.temp_db.name, learn=True)
        self.assertTrue(result)

        # Prepare an existing memory cache with one entry
        import pickle

        data = {
            "1": {
                "id": "1",
                "error_type": "error_type1",
                "faulty_code": "question",
                "fix_answer": "answer",
            }
        }
        with open(self.temp_db.name, "wb") as f:
            pickle.dump(data, f)

        # Loading the cache should populate the backward compatible _db
        result = self.react.setup(db_path=self.temp_db.name, learn=False)
        self.assertTrue(result)
        found_mem = None
        for mem_id, mem_obj in self.react._memory.memories.items():
            if hasattr(mem_obj, 'error_type') and mem_obj.error_type == "error_type1":
                found_mem = mem_obj
                break
        self.assertIsNotNone(found_mem, "Memory with error_type 'error_type1' not found")
        self.assertEqual(found_mem.faulty_code, "question")

        # Corrupt file should be ignored but still succeed
        with open(self.temp_db.name, "w") as f:
            f.write("corrupt data")

        result = self.react.setup(db_path=self.temp_db.name, learn=False)
        self.assertTrue(result)

        # Setup without a DB path uses an in-memory cache
        result = self.react.setup(learn=True, max_iterations=10, comment_prefix="//")
        self.assertTrue(result)
        self.assertEqual(self.react._max_iterations, 10)
        self.assertEqual(self.react._lang_prefix, "//")
    
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
    
    def test_add_error_example(self):
        """Test the _add_error_example method."""
        self.react.setup(db_path=self.temp_db.name, learn=True)
        
        # Add a new error example
        self.react._add_error_example("error_type1", "question1", "answer1")
        # Verify 'error_type1' in memory
        found_mem1 = None
        for mem_id, mem_obj in self.react._memory.memories.items():
            if hasattr(mem_obj, 'error_type') and mem_obj.error_type == "error_type1":
                found_mem1 = mem_obj
                break
        self.assertIsNotNone(found_mem1, "Memory with error_type 'error_type1' not found after add")
        self.assertEqual(found_mem1.faulty_code, "question1")
        self.assertEqual(found_mem1.fix_answer, "answer1")
        
        # Add another error example
        self.react._add_error_example("error_type2", "question2", "answer2")
        # Verify 'error_type2' in memory
        found_mem2 = None
        for mem_id, mem_obj in self.react._memory.memories.items():
            if hasattr(mem_obj, 'error_type') and mem_obj.error_type == "error_type2":
                found_mem2 = mem_obj
                break
        self.assertIsNotNone(found_mem2, "Memory with error_type 'error_type2' not found after add")
        # Add assertions for faulty_code and fix_answer if needed, similar to error_type1
        
        # Verify DB was saved regardless of learn mode
        self.react._learn_mode = False
        self.react._add_error_example("error_type3", "question3", "answer3")
        # Reload and ensure all entries persisted
        self.react.setup(db_path=self.temp_db.name, learn=False)
        # Verify all entries persisted in memory after reload
        error_types_to_check = ["error_type1", "error_type2", "error_type3"]
        found_in_memory = {et: False for et in error_types_to_check}
        for mem_id, mem_obj in self.react._memory.memories.items():
            if hasattr(mem_obj, 'error_type') and mem_obj.error_type in found_in_memory:
                found_in_memory[mem_obj.error_type] = True
        for et in error_types_to_check:
            self.assertTrue(found_in_memory[et], f"Memory for '{et}' not found after reload")
    
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
        self.react.setup(max_iterations=3)
        
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
        self.react.setup(max_iterations=3)
        
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
        self.react.setup(db_path=self.temp_db.name, learn=True, max_iterations=3)
        
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

        # Check if the error example was added to memory
        found = any(m.error_type == "Error type 1" for m in self.react._memory.memories.values())
        self.assertTrue(found)

        # Test with code that has a different error that can't be fixed
        result = self.react.react_cycle("This code has an error2", check_callback, fix_callback)
        self.assertEqual(result, "")  # Should return empty string if can't fix

        # The second error type should not be added since the fix wasn't successful
        found = any(m.error_type == "Error type 2" for m in self.react._memory.memories.values())
        self.assertFalse(found)
    
    def test_react_cycle_not_ready(self):
        """Test the react_cycle method when React is not ready."""
        # Don't call setup, so _is_ready is False
        result = self.react.react_cycle("code", lambda x: [], lambda x, y, z, d, i: x)
        self.assertEqual(result, "")
        self.assertIn("not ready", self.react.error_message)
    
    # Edge case tests from test_react_edge_cases.py
    
    @patch('hagent.tool.react.FewShotMemory')
    def test_load_db_exception(self, mock_memory):
        """Test exception handling during memory initialization."""
        mock_memory.side_effect = Exception("Test exception")

        result = self.react.setup(db_path=self.temp_db.name, learn=False)

        self.assertFalse(result)
        self.assertIn("Failed to initialize memory system", self.react.error_message)
        self.assertIn("Test exception", self.react.error_message)
    
    @patch('hagent.tool.react.FewShotMemory.add')
    def test_save_db_exception(self, mock_add):
        """Test exception handling when adding to memory fails."""
        mock_add.side_effect = Exception("Test exception")

        self.react.setup(db_path=self.temp_db.name, learn=True)

        with self.assertRaises(Exception):
            self.react._add_error_example("test_error2", "test_question2", "test_answer2")

        # The in-memory DB should not include the failed entry
        # Verify 'test_error2' is not in memory
        found_mem_error2 = False
        for mem_id, mem_obj in self.react._memory.memories.items():
            if hasattr(mem_obj, 'error_type') and mem_obj.error_type == "test_error2":
                found_mem_error2 = True
                break
        self.assertFalse(found_mem_error2, "Memory with error_type 'test_error2' should not be found")
    
    def test_load_db_nonexistent_file(self):
        """Setup should fail when the cache file is missing and learning is disabled."""
        if os.path.exists(self.temp_db.name):
            os.remove(self.temp_db.name)

        result = self.react.setup(db_path=self.temp_db.name, learn=False)
        self.assertFalse(result)
        self.assertIn("Database file not found", self.react.error_message)
    
    def test_react_cycle_no_diagnostics(self):
        """Test react_cycle when check_callback returns no diagnostics."""
        self.react.setup()
        
        # Mock callbacks
        def check_callback(code: str) -> List[Diagnostic]:
            return []  # No diagnostics
        
        def fix_callback(code: str, diag: Diagnostic, fix_example: Dict[str, str], delta: bool, iteration: int) -> str:
            return code  # No changes
        
        # Test with code that has no errors
        result = self.react.react_cycle("This code has no errors", check_callback, fix_callback)
        self.assertEqual(result, "This code has no errors")
        self.assertEqual(self.react.last_code, "This code has no errors")
        
        # Check log
        logs = self.react.get_log()
        self.assertEqual(len(logs), 1)
        self.assertEqual(logs[0]["iteration"], 1)
    
    def test_react_cycle_insert_comment_exception_in_delta(self):
        """Test react_cycle when insert_comment raises an exception in delta mode."""
        self.react.setup(max_iterations=3)
        
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
        self.react.setup(max_iterations=3)
        
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
    
    def test_react_cycle_learning_with_new_error(self):
        """Test react_cycle with learning enabled and a new error type."""
        self.react.setup(db_path=self.temp_db.name, learn=True, max_iterations=3)
        
        # Mock callbacks with a counter to control behavior
        check_call_count = [0] # Use a new name to avoid confusion
        
        def check_callback(code: str) -> List[Diagnostic]:
            check_call_count[0] += 1
            if check_call_count[0] == 1: # React Iteration 1, initial check
                return [MockDiagnosticWithError("Error type 1", 1)]
            elif check_call_count[0] == 2: # React Iteration 1, post-fix check
                # Code is "Code that now has Error type 2"
                return [MockDiagnosticWithError("Error type 2", 2)]
            elif check_call_count[0] == 3: # React Iteration 2, initial check
                # Code is "Code that now has Error type 2"
                return [MockDiagnosticWithError("Error type 2", 2)]
            elif check_call_count[0] == 4: # React Iteration 2, post-fix check
                # Code is "Fixed code"
                return []
            return [] # Default safety
        
        def fix_callback(code: str, diag: Diagnostic, fix_example: Dict[str, str], delta: bool, iteration: int) -> str:
            if diag.msg == "Error type 1":
                return "Code that now has Error type 2"
            elif diag.msg == "Error type 2":
                return "Fixed code"
            # Adding a fallback for safety, though it shouldn't be hit in this specific test's flow
            self.fail(f"fix_callback called with unexpected error: {diag.msg}")
        
        # Test with code that will have different error types
        result = self.react.react_cycle("This code has errors", check_callback, fix_callback)
        self.assertIn("Fixed code", result)
        
        # Check if 'Error type 1' was added to memory
        found_et1 = any(hasattr(m, 'error_type') and m.error_type == "Error type 1" for m in self.react._memory.memories.values())
        self.assertTrue(found_et1, "Memory for 'Error type 1' not found after learning cycle")

        # Check if 'Error type 2' was added to memory
        found_et2 = any(hasattr(m, 'error_type') and m.error_type == "Error type 2" for m in self.react._memory.memories.values())
        self.assertTrue(found_et2, "Memory for 'Error type 2' not found after learning cycle")
        
        # Check log
        logs = self.react.get_log()
        self.assertEqual(len(logs), 2)

    @patch('hagent.tool.react.FewShotMemory')
    def test_save_db_exception_during_setup(self, mock_memory):
        """Test exception handling in memory creation during setup."""
        mock_memory.side_effect = Exception("Test exception")

        result = self.react.setup(db_path="nonexistent_db.yaml", learn=True)

        self.assertFalse(result)
        self.assertIn("Failed to initialize memory system", self.react.error_message)
        self.assertIn("Test exception", self.react.error_message)


if __name__ == "__main__":
    unittest.main() 
