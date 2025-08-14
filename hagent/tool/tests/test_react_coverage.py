#!/usr/bin/env python3
"""
Test file specifically designed to increase coverage of the React class.
This file targets uncovered lines in react.py.
"""

import tempfile
import unittest
from unittest.mock import patch
from typing import List, Dict
from hagent.tool.memory import Memory_shot

from hagent.tool.react import React, process_multiline_strings, insert_comment
from hagent.tool.compile import Diagnostic


class MockDiagnostic(Diagnostic):
    """Mock diagnostic for testing."""

    def __init__(self, msg: str, loc: int = 1, hint: str = ''):
        self.msg = msg
        self.loc = loc
        self.hint = hint
        self.error = msg  # For testing error type comparison

    def to_str(self) -> str:
        return f'Error at line {self.loc}: {self.msg}\nHint: {self.hint}'

    def insert_comment(self, code: str, prefix: str) -> str:
        """Insert a comment with diagnostic info into the code."""
        return insert_comment(code, self.to_str(), prefix, self.loc)


class MockDiagnosticWithError(Diagnostic):
    """Mock diagnostic that raises errors when methods are called."""

    def __init__(self, msg: str, loc: int = 1, hint: str = '', raise_on_insert: bool = False):
        self.msg = msg
        self.loc = loc
        self.hint = hint
        self.error = msg  # For testing error type comparison
        self.raise_on_insert = raise_on_insert

    def to_str(self) -> str:
        return f'Error at line {self.loc}: {self.msg}\nHint: {self.hint}'

    def insert_comment(self, code: str, prefix: str) -> str:
        """Insert a comment with diagnostic info into the code."""
        if self.raise_on_insert:
            raise ValueError('Simulated error in insert_comment')
        return code  # Just return the code unchanged for simplicity


class TestReactCoverage(unittest.TestCase):
    """Test class to increase coverage of React."""

    def setUp(self):
        """Set up for tests."""
        self.react = React()
        # Create a temporary DB file for testing
        self.temp_db = tempfile.mkdtemp()  # NamedTemporaryFile(delete=False, suffix='.yaml')

    def tearDown(self):
        """Clean up after tests."""

    def test_process_multiline_strings(self):
        """Test the process_multiline_strings function."""
        # Test with a dictionary
        test_dict = {'key1': 'value1', 'key2': 'value2\nwith\nnewlines'}
        result = process_multiline_strings(test_dict)
        self.assertEqual(result['key1'], 'value1')
        # Check the type instead of comparing values
        from ruamel.yaml.scalarstring import LiteralScalarString

        self.assertIsInstance(result['key2'], LiteralScalarString)

        # Test with a list
        test_list = ['item1', 'item2\nwith\nnewlines']
        result = process_multiline_strings(test_list)
        self.assertEqual(result[0], 'item1')
        self.assertIsInstance(result[1], LiteralScalarString)

        # Test with a simple string without newlines
        test_str = 'simple string'
        result = process_multiline_strings(test_str)
        self.assertEqual(result, 'simple string')

    def test_insert_comment(self):
        """Test the insert_comment function."""
        code = 'line1\nline2\nline3\nline4\n'
        comment = 'This is a comment\nwith multiple lines'

        # Insert at the beginning
        result = insert_comment(code, comment, '#', 1)
        self.assertIn('# This is a comment', result)

        # Insert in the middle
        result = insert_comment(code, comment, '//', 3)
        self.assertIn('// This is a comment', result)

        # Test with invalid location
        with self.assertRaises(ValueError):
            insert_comment(code, comment, '#', 10)

    def test_get_delta(self):
        """Test the get_delta method."""
        code = '\n'.join([f'line{i}' for i in range(1, 21)])

        # Test getting delta from the middle
        delta, start, end = self.react.get_delta(code, 10, window=3)
        self.assertEqual(start, 7)
        self.assertEqual(end, 13)
        self.assertIn('line7', delta)
        self.assertIn('line13', delta)

        # Test getting delta from the beginning
        delta, start, end = self.react.get_delta(code, 1, window=3)
        self.assertEqual(start, 1)
        self.assertEqual(end, 4)

        # Test getting delta from the end
        delta, start, end = self.react.get_delta(code, 20, window=3)
        self.assertEqual(start, 17)
        self.assertEqual(end, 20)

    def test_apply_patch(self):
        """Test the apply_patch method."""
        full_code = '\n'.join([f'line{i}' for i in range(1, 11)])
        patch = 'patched_line1\npatched_line2\n'

        # Apply patch in the middle
        result = self.react.apply_patch(full_code, patch, 4, 6)
        self.assertIn('line3', result)
        self.assertIn('patched_line1', result)
        self.assertIn('patched_line2', result)
        self.assertIn('line7', result)
        self.assertNotIn('line4', result)
        self.assertNotIn('line5', result)
        self.assertNotIn('line6', result)

        # Apply patch at the beginning
        result = self.react.apply_patch(full_code, patch, 1, 2)
        self.assertIn('patched_line1', result)
        self.assertIn('line3', result)
        self.assertTrue(result.startswith('patched_line1'))
        self.assertFalse(result.startswith('line1'))

        # Apply patch at the end
        result = self.react.apply_patch(full_code, patch, 9, 10)
        self.assertIn('line8', result)
        self.assertIn('patched_line1', result)
        self.assertFalse('line9\n' in result)
        self.assertFalse('line10' in result)

    def test_get_log(self):
        """Test the get_log method."""
        self.react.setup()
        self.assertEqual(self.react.get_log(), [])

        # Add some log entries
        self.react._log.append({'iteration': 1, 'check': None, 'fix': None})
        logs = self.react.get_log()
        self.assertEqual(len(logs), 1)
        self.assertEqual(logs[0]['iteration'], 1)

    def test_react_cycle_success(self):
        """Test the react_cycle method with successful fix."""
        self.react.setup(max_iterations=3)

        # Mock callbacks
        def check_callback(code: str) -> List[Diagnostic]:
            if 'error' in code:
                return [MockDiagnostic('Test error', 1)]
            return []

        # Track if fix_callback was called
        fix_called = [False]

        def fix_callback(code: str, diag: Diagnostic, fix_example: Memory_shot, delta: bool, iteration: int) -> str:
            fix_called[0] = True
            # For debugging
            print(f'Fix callback called with code: {code}')
            return 'This code has a fixed'

        # Test with code that has an error
        result = self.react.react_cycle('This code has an error', check_callback, fix_callback)

        # Verify fix_callback was called
        self.assertTrue(fix_called[0], 'Fix callback was not called')

        self.assertIn('This code has a fixed', result)
        self.assertIn('This code has a fixed', self.react.last_code)

        # Check log
        logs = self.react.get_log()
        self.assertEqual(len(logs), 1)
        self.assertEqual(logs[0]['iteration'], 1)

    def test_react_cycle_failure(self):
        """Test the react_cycle method with unsuccessful fix."""
        self.react.setup(max_iterations=3)

        # Mock callbacks
        def check_callback(code: str) -> List[Diagnostic]:
            return [MockDiagnostic('Test error', 1)]

        def fix_callback(code: str, diag: Diagnostic, fix_example: Dict[str, str], delta: bool, iteration: int) -> str:
            return code  # Return the same code (no fix)

        # Test with code that has an error that can't be fixed
        result = self.react.react_cycle('This code has an error', check_callback, fix_callback)
        self.assertEqual(result, '')  # Should return empty string if can't fix
        self.assertIn('This code has an error', self.react.last_code)

        # Check log
        logs = self.react.get_log()
        self.assertEqual(len(logs), 3)  # Should have 3 iterations

    def test_react_cycle_not_ready(self):
        """Test the react_cycle method when React is not ready."""
        # Don't call setup, so _is_ready is False
        result = self.react.react_cycle('code', lambda x: [], lambda x, y, z, d, i: x)
        self.assertEqual(result, '')
        self.assertIn('not ready', self.react.error_message)

    # Edge case tests from test_react_edge_cases.py

    def test_react_cycle_no_diagnostics(self):
        """Test react_cycle when check_callback returns no diagnostics."""
        self.react.setup()

        # Mock callbacks
        def check_callback(code: str) -> List[Diagnostic]:
            return []  # No diagnostics

        def fix_callback(code: str, diag: Diagnostic, fix_example: Memory_shot, delta: bool, iteration: int) -> str:
            return code  # No changes

        # Test with code that has no errors
        result = self.react.react_cycle('This code has no errors', check_callback, fix_callback)
        self.assertEqual(result, 'This code has no errors')
        self.assertEqual(self.react.last_code, 'This code has no errors')

        # Check log
        logs = self.react.get_log()
        self.assertEqual(len(logs), 1)
        self.assertEqual(logs[0]['iteration'], 1)

    def test_react_cycle_insert_comment_exception_in_delta(self):
        """Test react_cycle when insert_comment raises an exception in delta mode."""
        self.react.setup(max_iterations=3)

        # Mock callbacks
        def check_callback(code: str) -> List[Diagnostic]:
            return [MockDiagnosticWithError('Test error', 1, raise_on_insert=True)]

        def fix_callback(code: str, diag: Diagnostic, fix_example: Memory_shot, delta: bool, iteration: int) -> str:
            return code.replace('error', 'fixed')

        # Test with code that will cause an exception in insert_comment
        result = self.react.react_cycle('This code has an error', check_callback, fix_callback)
        self.assertEqual(result, '')  # Should return empty string on error
        self.assertIn('Failed to insert diagnostic comment in delta', self.react.error_message)

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
                return [MockDiagnosticWithError('Test error', 1)]
            else:
                # Second iteration - return a diagnostic that raises on insert
                return [MockDiagnosticWithError('Test error', 1, raise_on_insert=True)]

        def fix_callback(code: str, diag: Diagnostic, fix_example: Memory_shot, delta: bool, iteration: int) -> str:
            # Return a modified code that still has an error
            return code + ' modified'

        # Test with code that will cause an exception in insert_comment on the second iteration
        result = self.react.react_cycle('This code has an error', check_callback, fix_callback)
        self.assertEqual(result, '')  # Should return empty string on error
        self.assertIn('Failed to insert diagnostic comment', self.react.error_message)

        # Check log
        logs = self.react.get_log()
        self.assertEqual(len(logs), 2)  # Should have 2 iterations

    @patch('hagent.tool.react.FewShotMemory')
    def test_save_db_exception_during_setup(self, mock_memory):
        """Test exception handling in memory creation during setup."""
        mock_memory.side_effect = Exception('Test exception')

        result = self.react.setup(db_path='nonexistent_db.yaml', learn=True)

        self.assertFalse(result)
        self.assertIn('Failed to initialize memory system', self.react.error_message)
        self.assertIn('Test exception', self.react.error_message)


if __name__ == '__main__':
    unittest.main()
