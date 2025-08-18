#!/usr/bin/env python3
"""
Unit tests for the Fuzzy_grep tool.
"""

import os
import tempfile
import unittest
from unittest.mock import patch
from hagent.tool.fuzzy_grep import Fuzzy_grep


class TestFuzzGrep(unittest.TestCase):
    def setUp(self):
        self.tool = Fuzzy_grep()
        # Use no language filtering by default.
        self.tool.setup()

    def test_preprocess_and_extract(self):
        text = 'Hello_World123'
        self.assertEqual(self.tool.preprocess(text), 'helloworld')
        words = self.tool.extract_words('This_is a test123')
        self.assertIn('This_is', words)
        self.assertIn('test123', words)

    def test_line_matches(self):
        line = 'This line has Example_3 string and _test_4 value.'
        self.assertTrue(self.tool.line_matches(line, ['example', 'test'], threshold=70))
        self.assertTrue(self.tool.line_matches(line, ['example', 'absent'], threshold=70))
        self.assertFalse(self.tool.line_matches(line, ['potato', 'absent'], threshold=70))
        self.assertFalse(self.tool.line_matches(line, ['potato', 'absent'], threshold=50))

    def test_find_matches_in_text(self):
        text = '\n'.join(
            [
                'First line',
                'This line has Example_string and test_value.',
                'Another line',
                'Yet another line with example and test3.',
                'Last line',
            ]
        )
        results = self.tool.find_matches_in_text(text, ['Example', 'test'], threshold=70)
        expected = [(1, 'This line has Example_string and test_value.'), (3, 'Yet another line with example and test3.')]
        self.assertEqual(results, expected)

    def test_search_text_input(self):
        text = '\n'.join(['Line one', 'Line two with Example string and test value.', 'Line three'])
        res = self.tool.search(text=text, search_terms=['example', 'test'], threshold=70)
        self.assertIn('text', res)
        self.assertTrue(len(res['text']) > 0)

    def test_search_file_input(self):
        # Create a temporary file.
        test_content = '\n'.join(['Alpha line', 'Beta line with __Example string and _3_test__123123 value.', 'Gamma line'])
        with tempfile.NamedTemporaryFile(mode='w', delete=False, suffix='.txt') as temp_file:
            temp_file.write(test_content)
            test_file = temp_file.name
        try:
            res = self.tool.search(files=[test_file], search_terms=['example', 'test'], threshold=70)
            self.assertIn(test_file, res)
            self.assertTrue(len(res[test_file]) > 0)
        finally:
            os.remove(test_file)

    def test_search_directory_input(self):
        # Create a temporary directory with two files.
        with tempfile.TemporaryDirectory() as test_dir:
            file1 = os.path.join(test_dir, 'file1.txt')
            file2 = os.path.join(test_dir, 'file2.txt')
            with open(file1, 'w', encoding='utf-8') as f:
                f.write('File one has Example string and test value.\nAnother line.')
            with open(file2, 'w', encoding='utf-8') as f:
                f.write('File two does not match.\nNothing here.')

            res = self.tool.search(directory=test_dir, search_terms=['example', 'test'], threshold=70)
            self.assertIn(file1, res)
            self.assertNotIn(file2, res)

    def test_setup_with_unsupported_language(self):
        """Test setup with an unsupported language."""
        result = self.tool.setup('unsupported_language')
        self.assertFalse(result)
        self.assertEqual(self.tool.error_message, 'Unsupported language: unsupported_language')

    def test_setup_with_supported_languages(self):
        """Test setup with all supported languages."""
        # Test Verilog
        result = self.tool.setup('verilog')
        self.assertTrue(result)
        self.assertEqual(self.tool.language, 'verilog')
        self.assertTrue(len(self.tool.reserved_keywords) > 0)

        # Test Scala
        result = self.tool.setup('scala')
        self.assertTrue(result)
        self.assertEqual(self.tool.language, 'scala')
        self.assertTrue(len(self.tool.reserved_keywords) > 0)

        # Test Chisel
        result = self.tool.setup('chisel')
        self.assertTrue(result)
        self.assertEqual(self.tool.language, 'chisel')
        self.assertTrue(len(self.tool.reserved_keywords) > 0)

        # Test case insensitivity
        result = self.tool.setup('VERILOG')
        self.assertTrue(result)
        self.assertEqual(self.tool.language, 'verilog')

    def test_get_reserved_keywords(self):
        """Test get_reserved_keywords for all supported languages."""
        # Test Verilog keywords
        verilog_keywords = Fuzzy_grep.get_reserved_keywords('verilog')
        self.assertTrue('module' in verilog_keywords)
        self.assertTrue('always' in verilog_keywords)
        self.assertTrue('endmodule' in verilog_keywords)

        # Test Scala keywords
        scala_keywords = Fuzzy_grep.get_reserved_keywords('scala')
        self.assertTrue('class' in scala_keywords)
        self.assertTrue('object' in scala_keywords)
        self.assertTrue('trait' in scala_keywords)

        # Test Chisel keywords (should include Scala keywords plus Chisel-specific ones)
        chisel_keywords = Fuzzy_grep.get_reserved_keywords('chisel')
        self.assertTrue('class' in chisel_keywords)  # From Scala
        self.assertTrue('module' in chisel_keywords)  # Chisel-specific
        self.assertTrue('io' in chisel_keywords)  # Chisel-specific

        # Test unsupported language
        unsupported_keywords = Fuzzy_grep.get_reserved_keywords('unsupported')
        self.assertEqual(unsupported_keywords, set())

    def test_find_matches_in_file_with_error(self):
        """Test find_matches_in_file with a file that causes an error."""
        with patch('builtins.open', side_effect=Exception('Test file error')):
            results = self.tool.find_matches_in_file('nonexistent_file.txt', ['test'], 70)
            self.assertEqual(results, [])
            self.assertEqual(self.tool.error_message, 'Test file error')

    def test_search_with_invalid_directory(self):
        """Test search with an invalid directory."""
        results = self.tool.search(directory='nonexistent_directory', search_terms=['test'], threshold=70)
        self.assertEqual(results, {})
        self.assertEqual(self.tool.error_message, 'nonexistent_directory is not a valid directory.')

    def test_search_with_nonexistent_file(self):
        """Test search with a nonexistent file."""
        results = self.tool.search(files=['nonexistent_file.txt'], search_terms=['test'], threshold=70)
        self.assertIn('nonexistent_file.txt', results)
        self.assertEqual(results['nonexistent_file.txt'], [])

    def test_line_matches_with_reserved_keywords(self):
        """Test line_matches with reserved keywords."""
        # Setup with Verilog language to enable keyword filtering
        self.tool.setup('verilog')

        # Line with only reserved keywords
        line = 'module test endmodule'
        self.assertFalse(self.tool.line_matches(line, ['module'], threshold=70))

        # Line with both reserved and non-reserved words
        line = 'module custom_module endmodule'
        self.assertTrue(self.tool.line_matches(line, ['custommodule'], threshold=70))


if __name__ == '__main__':
    unittest.main()
