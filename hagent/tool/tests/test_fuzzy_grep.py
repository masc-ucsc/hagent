#!/usr/bin/env python3
"""
Unit tests for the Fuzzy_grep tool.
"""

import os
import unittest
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
        self.assertFalse(self.tool.line_matches(line, ['example', 'absent'], threshold=70))

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
        results = self.tool.find_matches_in_text(text, ['Example', 'test'], context=0, threshold=70)
        print(results)
        expected = [(4, 'Yet another line with example and test3.', True)]
        self.assertEqual(results, expected)

    def test_search_text_input(self):
        text = '\n'.join(['Line one', 'Line two with Example string and test value.', 'Line three'])
        res = self.tool.search(text=text, search_terms=['example', 'test'], context=1, threshold=70)
        self.assertIn('text', res)
        self.assertTrue(len(res['text']) > 0)

    def test_search_file_input(self):
        # Create a temporary file.
        test_content = '\n'.join(['Alpha line', 'Beta line with __Example string and _3_test__123123 value.', 'Gamma line'])
        test_file = 'temp_fuzzy_grep_test.txt'
        with open(test_file, 'w', encoding='utf-8') as f:
            f.write(test_content)
        try:
            res = self.tool.search(files=[test_file], search_terms=['example', 'test'], context=0, threshold=70)
            self.assertIn(test_file, res)
            self.assertTrue(len(res[test_file]) > 0)
        finally:
            os.remove(test_file)

    def test_search_directory_input(self):
        # Create a temporary directory with two files.
        test_dir = 'temp_fuzzy_grep_dir'
        os.makedirs(test_dir, exist_ok=True)
        file1 = os.path.join(test_dir, 'file1.txt')
        file2 = os.path.join(test_dir, 'file2.txt')
        with open(file1, 'w', encoding='utf-8') as f:
            f.write('File one has Example string and test value.\nAnother line.')
        with open(file2, 'w', encoding='utf-8') as f:
            f.write('File two does not match.\nNothing here.')
        try:
            res = self.tool.search(directory=test_dir, search_terms=['example', 'test'], context=0, threshold=70)
            self.assertIn(file1, res)
            self.assertNotIn(file2, res)
        finally:
            os.remove(file1)
            os.remove(file2)
            os.rmdir(test_dir)


if __name__ == '__main__':
    unittest.main()
