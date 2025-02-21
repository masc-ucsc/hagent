#!/usr/bin/env python3
"""
Script: extract_verilog_diff_keywords.py

This script:
  1. Reads an original Verilog file and a fixed Verilog file.
  2. Generates a unified diff between the two.
  3. Extracts the main words (identifiers/keywords) from the diff while ignoring comments.
  4. Prints the extracted words.

Usage example:
  poetry run python3 extract_verilog_diff_keywords.py \
      --original_verilog ~/feri/original.v \
      --fixed_verilog ~/feri/fixed.v
"""

import argparse
import difflib
import re


class FuzzyGrepFilter:
    """
    Utility class to generate a unified diff and extract keywords from it.
    """

    @staticmethod
    def generate_diff(old_code: str, new_code: str) -> str:
        """
        Generate a unified diff string comparing old_code vs. new_code.

        :param old_code: Content of the original file.
        :param new_code: Content of the modified file.
        :return: A unified diff as a string.
        """
        old_lines = old_code.splitlines()
        new_lines = new_code.splitlines()
        diff_lines = difflib.unified_diff(
            old_lines, new_lines, fromfile='verilog_original.v', tofile='verilog_fixed.v', lineterm=''
        )
        return '\n'.join(diff_lines)

    @staticmethod
    def extract_keywords_from_diff(diff_text: str) -> list:
        """
        Extract keywords from a unified diff. It scans lines that are marked as changes
        (starting with '+' or '-' but ignoring file header lines) and extracts all alphanumeric words.
        Comments are removed before processing so that only meaningful code identifiers are retained.

        :param diff_text: The unified diff string.
        :return: A list of unique keywords.
        """
        keywords = set()
        for line in diff_text.splitlines():
            # Look only at changed lines (ignore header lines like '+++' and '---')
            if (line.startswith('+') and not line.startswith('+++')) or (line.startswith('-') and not line.startswith('---')):
                # Remove the diff marker (+ or -)
                content = line[1:]
                # Remove single-line comments (//...) and inline block comments (/* ... */)
                content = re.sub(r'//.*', '', content)
                content = re.sub(r'/\*.*?\*/', '', content)
                # Extract all alphanumeric words from the cleaned line
                words = re.findall(r'\w+', content)
                keywords.update(words)
        return list(keywords)


def main():
    parser = argparse.ArgumentParser(description='Extract main words from a unified Verilog diff (ignoring comments).')
    parser.add_argument('--original_verilog', required=True, help='Path to the original Verilog file (e.g., original.v)')
    parser.add_argument('--fixed_verilog', required=True, help='Path to the fixed Verilog file (e.g., fixed.v)')
    args = parser.parse_args()

    # Read the Verilog files
    try:
        with open(args.original_verilog, 'r', encoding='utf-8') as f:
            original_v = f.read()
        with open(args.fixed_verilog, 'r', encoding='utf-8') as f:
            fixed_v = f.read()
    except Exception as e:
        print(f'Error reading files: {e}')
        exit(1)

    # Generate the unified diff from the two files
    diff_text = FuzzyGrepFilter.generate_diff(original_v, fixed_v)
    print('*********************')
    print(diff_text)
    print('*********************')

    # Extract keywords from the diff (ignoring comments)
    keywords = FuzzyGrepFilter.extract_keywords_from_diff(diff_text)

    # Print the extracted keywords
    print('Extracted keywords from Verilog diff (ignoring comments):')
    for word in keywords:
        print(word)


if __name__ == '__main__':
    main()
