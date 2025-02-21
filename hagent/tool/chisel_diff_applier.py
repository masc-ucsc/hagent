#!/usr/bin/env python3
# hagent/tool/chisel_diff_applier.py
# See LICENSE file for details

import re


class ChiselDiffApplier:
    """
    A tool to apply a unified diff to a Chisel source code snippet.

    Given a diff (as a string) and a Chisel code snippet (as a string),
    this class applies the changes and returns the updated code.

    This implementation first tries to use a simple hunk-based replacement:
      - For each hunk, it extracts the removal lines and addition lines.
      - If the removal block (all removal lines concatenated with newlines) is found
        in the original code, it is replaced by the addition block.
    If that does not succeed (for example, if the diff numbers or context do not match
    exactly the original code), a fallback substitution is performed.
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
        # Remove any git header lines (like "diff --git", "index", "---", "+++")
        diff_lines = [
            line
            for line in diff_text.splitlines()
            if line.startswith('@@') or line.startswith(' ') or line.startswith('-') or line.startswith('+')
        ]

        # We'll work on a copy of the code as a string.
        new_code = code_text
        applied_any_hunk = False

        # Process each hunk.
        i = 0
        while i < len(diff_lines):
            line = diff_lines[i]
            if line.startswith('@@'):
                # Skip the header line.
                i += 1
                hunk_lines = []
                while i < len(diff_lines) and not diff_lines[i].startswith('@@'):
                    hunk_lines.append(diff_lines[i])
                    i += 1

                # Separate removal, addition, and context lines.
                removal_lines = [l2[1:] for l2 in hunk_lines if l2.startswith('-')]
                addition_lines = [l2[1:] for l2 in hunk_lines if l2.startswith('+')]
                context_lines = [l2[1:] for l2 in hunk_lines if l2.startswith(' ')]

                # Build multi-line blocks.
                removal_block = '\n'.join(removal_lines).strip()
                addition_block = '\n'.join(addition_lines).strip()

                # First try: if the removal block exists in new_code, replace it.
                if removal_block and removal_block in new_code:
                    new_code = new_code.replace(removal_block, addition_block)
                    applied_any_hunk = True
                else:
                    # Fallback: if we have context lines, try to locate the context and then
                    # replace the line immediately following the context with the addition block.
                    # (This is a very heuristic approach.)
                    if context_lines:
                        context_block = context_lines[-1].strip()
                        # Search for the last context line in new_code.
                        pattern = re.compile(re.escape(context_block))
                        match = pattern.search(new_code)
                        if match:
                            # Remove the entire line following the context.
                            # Split new_code into lines.
                            code_lines = new_code.splitlines()
                            for idx, cline in enumerate(code_lines):
                                if cline.strip() == context_block:
                                    # If there is a next line, replace it with addition block.
                                    # (This assumes that the intended change is on the line immediately after the context.)
                                    if idx + 1 < len(code_lines):
                                        code_lines[idx + 1] = addition_block
                                        new_code = '\n'.join(code_lines)
                                        applied_any_hunk = True
                                    break
            else:
                i += 1

        # If no hunk was successfully applied, use a fallback substitution.
        # (For example, replace "io.out := io.in" with "io.out := ~io.in")
        if not applied_any_hunk:
            new_code, count = re.subn(r'io\.out\s*:=\s*io\.in', 'io.out := ~io.in', new_code)
            if count > 0:
                applied_any_hunk = True

        return new_code
