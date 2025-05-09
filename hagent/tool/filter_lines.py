# hagent/tool/filter_lines.py
# See LICENSE file for details

import re
from collections import defaultdict
from typing import List, Set


class FilterLines:
    """
    A tool to filter Chisel code lines based on a generated Verilog diff.

    It extracts tokens (including multi-digit numbers) from the diff’s code portion,
    normalizes them (by splitting on underscores and camel-case boundaries), and then scores
    each Chisel line (using only its code portion, ignoring inline comments) based on simple substring matching.

    The union of candidate lines (excluding pure comment and import lines) is returned as a string
    with each matching line prefixed with "-> <line_no>:". An optional context parameter works similar
    to grep’s -C flag.

    This module supports both diff formats:
      - The “old” style with lines beginning with "<" or ">".
      - Unified diff format (as generated by difflib) with headers (---, +++, @@) and lines starting with "-" or "+".
    """

    def __init__(self):
        self.error_message = ''

    def _split_on_underscore(self, token: str) -> List[str]:
        """Split a token on underscores and return non-empty parts (of length ≥2)."""
        parts = token.split('_')
        return [part for part in parts if len(part) >= 2]

    def _split_camel(self, token: str) -> List[str]:
        """
        Split a camel-case token into its components.
        For example, "instrOut" becomes ["instr", "Out"].
        Only parts of length ≥2 are returned.
        """
        parts = re.findall(r'[A-Z]?[a-z]+', token)
        return [p for p in parts if len(p) >= 2]

    def _extract_tokens(self, diff_code_line: str) -> Set[str]:
        """
        Given a diff code line (without diff markers or inline comments),
        extract tokens (words, numbers, and operators) and normalize them.

        Rules:
          - Numeric tokens are kept only if they have more than one digit.
          - Skip tokens that are a single alphabetical character.
          - If a token starts with "io_" or "in_", remove that prefix.
          - If the resulting token ends with "Out", also add the version without "Out".
          - Additionally, if the token contains underscores, split it and add each part.
          - Also perform camel-case splitting and add each part.
        """
        tokens = re.findall(r'\d+|[A-Za-z_]+|==+|!=+|&&|\|\||[&|+\-*/%<>]+', diff_code_line)
        normalized = set()
        for token in tokens:
            if token.isdigit():
                if len(token) > 1:
                    normalized.add(token)
                continue
            if token.isalpha() and len(token) == 1:
                continue
            if token.startswith('io_') or token.startswith('in_'):
                token = token.split('_', 1)[1]
            normalized.add(token)
            if token.endswith('Out'):
                normalized.add(token[:-3])
            if '_' in token:
                for part in self._split_on_underscore(token):
                    normalized.add(part)
            for part in self._split_camel(token):
                normalized.add(part)
        return normalized

    def _extract_hint_lines(self, comment: str) -> List[int]:
        """
        Given a comment from the diff line, extract hint line numbers.
        The regex is generic and will match any Scala file reference like:
            "src/main/scala/ModuleName.scala:50"
        """
        hints = re.findall(r'[\w/]+\.scala:(\d+)', comment)
        return [int(num) for num in hints]

    def filter_lines(self, diff_file: str, chisel_file: str, context: int = 0) -> str:
        """
        Reads the diff file and the Chisel source file.

        For each diff line that begins with a valid marker (after stripping leading whitespace)
        ("<", ">", "-", or "+"), the marker is stripped and the remaining text (ignoring inline comments)
        is used to extract tokens. Any diff header lines (starting with '---', '+++', or '@@') are skipped.

        Each Chisel line (using only its code portion, before any inline comment) is scored based on the
        occurrence of these tokens. Additionally, if the diff line contains hint line numbers in its comment,
        those candidate Chisel lines receive a score boost.

        Pure comment lines and import statements in the Chisel file are skipped.

        The union of candidate lines (i.e. lines with a positive score) is returned.
        If 'context' is set to a value > 0, the specified number of lines before and after each candidate
        line are also included. Candidate lines are prefixed with "-> <line_no>:", while context lines are prefixed
        with four spaces.
        """
        # Read diff file
        try:
            with open(diff_file, 'r', encoding='utf-8') as df:
                diff_lines = df.readlines()
        except Exception as e:
            self.error_message = f"Failed to read diff file '{diff_file}': {e}"
            raise RuntimeError(self.error_message)

        # Read Chisel file
        try:
            with open(chisel_file, 'r', encoding='utf-8') as cf:
                chisel_lines = cf.readlines()
        except Exception as e:
            self.error_message = f"Failed to read Chisel file '{chisel_file}': {e}"
            raise RuntimeError(self.error_message)

        candidate_scores = defaultdict(int)

        # Process each diff line.
        for diff_line in diff_lines:
            diff_line = diff_line.rstrip('\n')
            # Remove leading whitespace so markers are at the front.
            stripped = diff_line.lstrip()
            # Skip unified diff header lines.
            if stripped.startswith('---') or stripped.startswith('+++') or stripped.startswith('@@'):
                continue
            # Process lines that start with one of our diff markers.
            if stripped and stripped[0] in {'<', '>', '-', '+'}:
                code_line = stripped[1:].strip()
                # Split off inline comment (if any).
                if '//' in code_line:
                    code_part, comment_part = code_line.split('//', 1)
                else:
                    code_part = code_line
                    comment_part = ''
                tokens = self._extract_tokens(code_part)
                hint_lines = self._extract_hint_lines(comment_part)
                for i, chisel_line in enumerate(chisel_lines, start=1):
                    chisel_code_portion = chisel_line.split('//')[0]
                    score = 0
                    for token in tokens:
                        if token and token in chisel_code_portion:
                            score += 1
                    if score > 3:
                        candidate_scores[i] += score
                for line_no in hint_lines:
                    candidate_scores[line_no] += 100

        candidate_line_nums = set(line_no for line_no, score in candidate_scores.items() if score > 0)
        if context > 0:
            total_lines = len(chisel_lines)
            extended_line_nums = set(candidate_line_nums)
            for line_no in candidate_line_nums:
                start = max(1, line_no - context)
                end = min(total_lines, line_no + context)
                for num in range(start, end + 1):
                    extended_line_nums.add(num)
            output_line_nums = sorted(extended_line_nums)
        else:
            output_line_nums = sorted(candidate_line_nums)

        output_lines = []
        for line_no in output_line_nums:
            line = chisel_lines[line_no - 1].rstrip()
            stripped_line = line.lstrip()
            if stripped_line.startswith('//') or stripped_line.startswith('import '):
                continue
            if line_no in candidate_line_nums:
                output_lines.append(f"->    {line_no}: {line}")
            else:
                output_lines.append(f'    {line}')

        return '\n'.join(output_lines)
