#!/usr/bin/env python3
import argparse
from hagent.tool.fuzzy_grep import Fuzzy_grep

def main():
    parser = argparse.ArgumentParser(
        description='Fuzzy grep-like search in files using fuzzy matching for all search terms.'
    )
    parser.add_argument(
        '-p', '--pattern', action='append', required=True,
        help='Search pattern. Specify multiple times for multiple patterns. A line must match all patterns.'
    )
    parser.add_argument('-C', '--context', type=int, default=0,
                        help='Number of context lines to include around matching lines.')
    parser.add_argument('-t', '--threshold', type=int, default=70,
                        help='Fuzzy matching threshold (0-100).')
    parser.add_argument('--language', choices=['verilog', 'scala', 'chisel'], default=None,
                        help='Programming language to filter out reserved keywords from fuzzy matching.')
    parser.add_argument('files', nargs='+', help='Files to search.')
    args = parser.parse_args()

    # Instantiate and set up the Fuzzy_grep tool.
    fg = Fuzzy_grep()
    if not fg:
        print(f"Intialization error: {fg.error_message}")
        exit(1)

    if not fg.setup(args.language):
        print(f"Setup error: {fg.error_message}")
        exit(1)

    # Search the specified files using the provided options.
    results = fg.search(files=args.files, search_terms=args.pattern,
                        context=args.context, threshold=args.threshold)

    # Output results in a grep-like format.
    for source, matches in results.items():
        print(f"File: {source}")
        for lineno, line, central in matches:
            marker = "->" if central else "  "
            print(f"{marker}{lineno:4d}: {line}")
        print()  # Blank line between files.

if __name__ == '__main__':
    main()

