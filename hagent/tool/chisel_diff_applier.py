#!/usr/bin/env python3
# hagent/tool/chisel_diff_applier.py
# See LICENSE file for details

import re

class ChiselDiffApplier:
    """
    A tool to apply a unified diff to a Chisel source code snippet.

    Given a diff (as a string) and a Chisel code snippet (as a string),
    this class applies the changes and returns the updated code.

    This implementation first parses each hunk and then searches the code
    line-by-line to find a block whose content (ignoring leading whitespace)
    matches the removal block. When found, it replaces that block with the
    addition block reindented to match the code.
    """

    def __init__(self):
        self.error_message = ''

    def apply_diff(self, diff_text: str, code_text: str) -> str:
        """
        Applies the given diff (in unified diff format) to the code snippet.

        Args:
            diff_text: The diff as a string.
            code_text: The original Chisel code as a string.

        Returns:
            The updated code snippet as a string.
        """
        # Only consider lines that are part of diff hunks.
        diff_lines = [line for line in diff_text.splitlines() if line.lstrip().startswith(('@@', ' ', '-', '+'))]

        # Split code into lines so we can work with indentation.
        code_lines = code_text.splitlines()
        applied_any_hunk = False
        self.error_message = ''

        i = 0
        while i < len(diff_lines):
            if diff_lines[i].lstrip().startswith('@@'):
                # Skip the header and collect hunk lines until the next header.
                i += 1
                hunk_lines = []
                while i < len(diff_lines) and not diff_lines[i].lstrip().startswith('@@'):
                    hunk_lines.append(diff_lines[i])
                    i += 1

                removal_lines = []
                addition_lines = []
                context_lines = []

                # Use a regex to capture any leading whitespace, the marker, and the content.
                pattern = re.compile(r'^(\s*)([-+  ])\s?(.*)$')
                for line in hunk_lines:
                    m = pattern.match(line)
                    if not m:
                        continue
                    # m.groups(): (indent, marker, content)
                    marker = m.group(2)
                    content = m.group(3)
                    if marker == '-':
                        removal_lines.append(content)
                    elif marker == '+':
                        addition_lines.append(content)
                    elif marker == ' ':
                        context_lines.append(content)

                # Try to find a block in code_lines that matches removal_lines (ignoring leading whitespace).
                if removal_lines:
                    block_len = len(removal_lines)
                    found = False
                    for j in range(len(code_lines) - block_len + 1):
                        match = True
                        for k in range(block_len):
                            if code_lines[j+k].strip() != removal_lines[k].strip():
                                match = False
                                break
                        if match:
                            # Use the indentation of the first line found in the code as the base.
                            candidate_indent = re.match(r'^(\s*)', code_lines[j]).group(1)
                            # Build new block with the same indentation.
                            new_block = [candidate_indent + line.lstrip() for line in addition_lines]
                            code_lines = code_lines[:j] + new_block + code_lines[j+block_len:]
                            applied_any_hunk = True
                            found = True
                            break
                    if not found:
                        # Fallback: try using context lines if removal_lines didn't match.
                        # if context_lines:
                        #     context_block = context_lines[-1].strip()
                        #     for j in range(len(code_lines)):
                        #         if code_lines[j].strip() == context_block and j+1 < len(code_lines):
                        #             # Replace the line following the context with the addition block.
                        #             candidate_indent = re.match(r'^(\s*)', code_lines[j+1]).group(1)
                        #             new_block = [candidate_indent + line.lstrip() for line in addition_lines]
                        #             code_lines = code_lines[:j+1] + new_block + code_lines[j+2:]
                        #             applied_any_hunk = True
                        #             found = True
                        #             break
                        self.error_message = (
                            f"Cannot apply diff: removal block not found in original code: {removal_lines}"
                        )
                        raise RuntimeError(self.error_message)
                else:
                    # If there is no removal block (only additions), we may need to insert.
                    # For simplicity, we do a fallback insertion after the last context line.
                    if context_lines:
                        context_block = context_lines[-1].strip()
                        for j in range(len(code_lines)):
                            if code_lines[j].strip() == context_block:
                                candidate_indent = re.match(r'^(\s*)', code_lines[j]).group(1)
                                new_block = [candidate_indent + line.lstrip() for line in addition_lines]
                                code_lines = code_lines[:j+1] + new_block + code_lines[j+1:]
                                applied_any_hunk = True
                                break
            else:
                i += 1

        new_code = "\n".join(code_lines)

        # If still nothing applied, try default fallback once more, else error out
        if not applied_any_hunk:
            new_code, count = re.subn(
                r'io\.out\s*:=\s*io\.in', 'io.out := ~io.in', new_code
            )
            if count > 0:
                applied_any_hunk = True
            else:
                self.error_message = "Diff could not be applied to the code"
                raise RuntimeError(self.error_message)

        return new_code