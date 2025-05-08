# hagent/tool/memory/test_react_utils_memory.py

"""
Test file for utility functions in react_memory.py.
"""

import unittest
from pathlib import Path
import os
import tempfile

from hagent.tool.memory.react_memory import insert_comment


class TestReactMemoryUtils(unittest.TestCase):
    """Test class for utility functions in react_memory.py."""
    
    def test_insert_comment_basic(self):
        """Test basic functionality of insert_comment."""
        code = "line1\nline2\nline3\nline4\n"
        comment = "This is a comment"
        
        # Insert at line 1
        result = insert_comment(code, comment, "#", 1)
        expected = "# This is a comment\nline1\nline2\nline3\nline4\n"
        self.assertEqual(result, expected)
        
        # Insert at line 3
        result = insert_comment(code, comment, "//", 3)
        expected = "line1\nline2\n// This is a comment\nline3\nline4\n"
        self.assertEqual(result, expected)
    
    def test_insert_comment_multiline(self):
        """Test insert_comment with a multi-line comment."""
        code = "line1\nline2\nline3\nline4\n"
        comment = "This is a comment\nwith multiple lines"
        
        # Insert at line 2
        result = insert_comment(code, comment, "#", 2)
        expected = "line1\n# This is a comment\n# with multiple lines\nline2\nline3\nline4\n"
        self.assertEqual(result, expected)
    
    def test_insert_comment_empty_code(self):
        """Test insert_comment with empty code."""
        code = ""
        comment = "This is a comment"
        
        # For empty code, the function should add the comment as the first line
        result = insert_comment(code, comment, "#", 1)
        self.assertEqual(result, "# This is a comment\n")
    
    def test_insert_comment_invalid_location(self):
        """Test insert_comment with an invalid location."""
        code = "line1\nline2\nline3\n"
        comment = "This is a comment"
        
        # Test with location 0 (invalid)
        with self.assertRaises(ValueError):
            insert_comment(code, comment, "#", 0)
        
        # Test with location beyond the end of the file
        with self.assertRaises(ValueError):
            insert_comment(code, comment, "#", 5)
    
    def test_insert_comment_at_end(self):
        """Test insert_comment at the end of the file."""
        code = "line1\nline2\nline3\n"
        comment = "This is a comment"
        
        # Insert at the last line
        result = insert_comment(code, comment, "#", 3)
        expected = "line1\nline2\n# This is a comment\nline3\n"
        self.assertEqual(result, expected)
        
        # Insert after the last line (at position len(lines) + 1)
        result = insert_comment(code, comment, "#", 4)
        expected = "line1\nline2\nline3\n# This is a comment\n"
        self.assertEqual(result, expected)
    
    def test_comment_prefixes(self):
        """Test insert_comment with different comment prefixes."""
        code = "line1\nline2\n"
        comment = "This is a comment"
        
        # Test with different comment prefixes
        prefixes = {
            "//": "// This is a comment",  # C/C++/Java
            "#": "# This is a comment",    # Python, Ruby, Bash
            "--": "-- This is a comment",  # SQL, Lua
            ";": "; This is a comment",    # Assembly, Lisp
            "!": "! This is a comment",    # Fortran
            "%": "% This is a comment",    # MATLAB, LaTeX
            "/*": "/* This is a comment",  # C-style block comment start
            "*/": "*/ This is a comment",  # C-style block comment end
            "<!--": "<!-- This is a comment", # HTML/XML
            "'''": "''' This is a comment"  # Python multi-line string
        }
        
        for prefix, expected_line in prefixes.items():
            result = insert_comment(code, comment, prefix, 1)
            self.assertIn(expected_line, result)


if __name__ == "__main__":
    unittest.main() 