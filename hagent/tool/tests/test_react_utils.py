#!/usr/bin/env python3
"""
Test file for utility functions in react.py.
"""

import unittest
from ruamel.yaml import YAML
from ruamel.yaml.scalarstring import LiteralScalarString
import tempfile
import os

from hagent.tool.react import process_multiline_strings, insert_comment


class TestReactUtils(unittest.TestCase):
    """Test class for utility functions in react.py."""
    
    def test_process_multiline_strings_with_dict(self):
        """Test process_multiline_strings with a dictionary."""
        test_dict = {
            "key1": "value1",
            "key2": "value2\nwith\nnewlines",
            "key3": {
                "nested_key": "nested_value\nwith\nnewlines"
            },
            "key4": ["item1", "item2\nwith\nnewlines"]
        }
        
        result = process_multiline_strings(test_dict)
        
        # Check that strings without newlines are unchanged
        self.assertEqual(result["key1"], "value1")
        
        # Check that strings with newlines are converted to LiteralScalarString
        self.assertIsInstance(result["key2"], LiteralScalarString)
        self.assertEqual(str(result["key2"]), "value2\nwith\nnewlines")
        
        # Check that nested dictionaries are processed
        self.assertIsInstance(result["key3"]["nested_key"], LiteralScalarString)
        self.assertEqual(str(result["key3"]["nested_key"]), "nested_value\nwith\nnewlines")
        
        # Check that nested lists are processed
        self.assertIsInstance(result["key4"][1], LiteralScalarString)
        self.assertEqual(str(result["key4"][1]), "item2\nwith\nnewlines")
    
    def test_process_multiline_strings_with_list(self):
        """Test process_multiline_strings with a list."""
        test_list = [
            "item1",
            "item2\nwith\nnewlines",
            ["nested_item1", "nested_item2\nwith\nnewlines"],
            {"key": "value\nwith\nnewlines"}
        ]
        
        result = process_multiline_strings(test_list)
        
        # Check that strings without newlines are unchanged
        self.assertEqual(result[0], "item1")
        
        # Check that strings with newlines are converted to LiteralScalarString
        self.assertIsInstance(result[1], LiteralScalarString)
        self.assertEqual(str(result[1]), "item2\nwith\nnewlines")
        
        # Check that nested lists are processed
        self.assertIsInstance(result[2][1], LiteralScalarString)
        self.assertEqual(str(result[2][1]), "nested_item2\nwith\nnewlines")
        
        # Check that nested dictionaries are processed
        self.assertIsInstance(result[3]["key"], LiteralScalarString)
        self.assertEqual(str(result[3]["key"]), "value\nwith\nnewlines")
    
    def test_process_multiline_strings_with_string(self):
        """Test process_multiline_strings with a string."""
        # Test with a string without newlines
        test_str1 = "simple string"
        result1 = process_multiline_strings(test_str1)
        self.assertEqual(result1, "simple string")
        
        # Test with a string with newlines
        test_str2 = "string\nwith\nnewlines"
        result2 = process_multiline_strings(test_str2)
        self.assertIsInstance(result2, LiteralScalarString)
        self.assertEqual(str(result2), "string\nwith\nnewlines")
    
    def test_yaml_output_format(self):
        """Test that the processed strings are correctly formatted in YAML output."""
        test_data = {
            "key1": "value1",
            "key2": "value2\nwith\nnewlines"
        }
        
        processed_data = process_multiline_strings(test_data)
        
        # Write to a temporary file
        with tempfile.NamedTemporaryFile(delete=False, suffix='.yaml') as tmp:
            tmp_name = tmp.name
        
        try:
            yaml_writer = YAML()
            yaml_writer.indent(mapping=2, sequence=4, offset=2)
            
            with open(tmp_name, 'w', encoding='utf-8') as f:
                yaml_writer.dump(processed_data, f)
            
            # Read the file and check the format
            with open(tmp_name, 'r', encoding='utf-8') as f:
                content = f.read()
                
                # The multiline string should be in literal block style (with |)
                self.assertIn("key2: |", content)
                self.assertIn("  value2", content)
                self.assertIn("  with", content)
                self.assertIn("  newlines", content)
        finally:
            if os.path.exists(tmp_name):
                os.remove(tmp_name)
    
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
        
        # This should raise a ValueError because there are no lines
        with self.assertRaises(ValueError):
            insert_comment(code, comment, "#", 1)
    
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


if __name__ == "__main__":
    unittest.main() 
