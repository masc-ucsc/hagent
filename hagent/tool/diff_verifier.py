#!/usr/bin/env python3
# hagent/tool/diff_verifier.py
# See LICENSE file for details

import re
import difflib


class DiffVerifier:
    """
    Verifies that `updated_code` is exactly `original_code` + the given `diff_text`,
    and that no extra changes slipped through.
    """

    def __init__(self, original_code: str, diff_text: str, updated_code: str):
        self.orig_lines = original_code.splitlines(keepends=True)
        self.new_lines = updated_code.splitlines(keepends=True)
        # we only need the hunks from the LLM diff
        self.expected_diff = [line + '\n' for line in diff_text.splitlines() if line.startswith(('@@', '+', '-', ' '))]

    def _compute_diff(self):
        """Compute the unified diff between original and new."""
        return list(difflib.unified_diff(self.orig_lines, self.new_lines, fromfile='original', tofile='updated', lineterm='\n'))

    def _normalize(self, lines):
        """Strip run-of-the-mill whitespace differences for fair comparison."""
        norm = []
        for line in lines:
            # only compare change lines
            if line.startswith(('+', '-', ' ')):
                # collapse all whitespace to single spaces,
                # but keep the leading + / - / ' ' marker
                marker, content = line[0], line[1:].rstrip('\n')
                content = re.sub(r'\s+', ' ', content).strip()
                norm.append(marker + content + '\n')
        return norm

    def _verify(self):
        """
        Returns True if the exact same hunks appear in the re-diff,
        else raises RuntimeError listing the mismatches.
        """
        actual = self._compute_diff()
        exp_norm = self._normalize(self.expected_diff)
        act_norm = self._normalize(actual)

        if exp_norm != act_norm:
            diff = difflib.unified_diff(exp_norm, act_norm, fromfile='expected_hunks', tofile='actual_hunks', lineterm='\n')
            raise RuntimeError('Verification failed!  The applied patch does not match exactly.\n' + ''.join(diff))

        # final sanity: ensure no leftover removal-lines
        removal_lines = [line[1:].strip() for line in exp_norm if line.startswith('-')]
        missing = [r for r in removal_lines if any(nl.strip() == r for nl in self.new_lines)]
        if missing:
            raise RuntimeError(
                'After patching, these lines should have been removed but are still present:\n' + '\n'.join(missing)
            )

        return True
