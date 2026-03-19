# See LICENSE for details
"""
Parse and apply search-and-replace patch blocks to Verilog source code.

Expected LLM output format::

    <<<<<<< SEARCH
    <exact lines from original code>
    =======
    <replacement lines>
    >>>>>>> REPLACE

Multiple blocks per response are supported and applied sequentially.
"""

import re
from dataclasses import dataclass
from typing import List, Optional, Tuple


@dataclass
class PatchBlock:
    """A single search-and-replace block parsed from LLM output."""

    search: str
    replace: str
    raw_block: str  # original raw text for debug logging


# Regex to extract search-and-replace blocks.
# Handles optional whitespace after markers and works across markdown fences.
_PATCH_PATTERN = re.compile(
    r'<{3,}\s*SEARCH\s*\n'  # <<<<<<< SEARCH
    r'(.*?)\n'  # search content (non-greedy)
    r'={3,}\s*\n'  # =======
    r'(.*?)\n'  # replace content (non-greedy)
    r'>{3,}\s*REPLACE',  # >>>>>>> REPLACE
    re.DOTALL,
)


class VerilogPatchApplier:
    """Parse and apply search-and-replace blocks to Verilog source code.

    Supports flexible whitespace matching so that minor formatting
    differences between the LLM's SEARCH text and the actual code
    do not prevent the patch from being applied.

    Comments are **preserved** during normalization — only whitespace
    around operators is normalized for matching purposes.
    """

    def __init__(self):
        self.error_message: str = ''

    # ------------------------------------------------------------------
    # Public API
    # ------------------------------------------------------------------

    def parse_patches(self, llm_response: str) -> List[PatchBlock]:
        """Parse all search-and-replace blocks from an LLM response.

        Handles blocks both inside and outside markdown code fences.
        Returns an ordered list of :class:`PatchBlock` objects.
        """
        # Strip markdown fences so markers inside fences are still found
        text = re.sub(r'```\w*\n?', '', llm_response)

        patches: List[PatchBlock] = []
        for m in _PATCH_PATTERN.finditer(text):
            search_text = m.group(1)
            replace_text = m.group(2)
            patches.append(
                PatchBlock(
                    search=search_text,
                    replace=replace_text,
                    raw_block=m.group(0),
                )
            )
        return patches

    # Regexes for diagnose_format
    _SEARCH_MARKER_RE = re.compile(r'<{3,}\s*SEARCH', re.IGNORECASE)
    _VALID_CLOSE_RE = re.compile(r'>{3,}\s*REPLACE', re.IGNORECASE)
    _WRONG_CLOSE_RE = re.compile(r'>{3,}\s*(END|DONE|FINISHED|COMPLETE|ORIGINAL)\b', re.IGNORECASE)
    _SEPARATOR_RE = re.compile(r'={3,}')

    def diagnose_format(self, llm_response: str) -> Optional[str]:
        """Detect common format mistakes that prevent patch parsing.

        Returns a human-readable diagnostic string if format issues are
        detected, or ``None`` if no SEARCH markers exist at all (the LLM
        simply did not produce any patches).

        Does **not** append the expected-format reminder — callers should
        append ``PATCH_FORMAT_CONTRACT`` themselves when building feedback.
        """
        if not llm_response or not llm_response.strip():
            return None

        # Strip markdown fences (same as parse_patches)
        text = re.sub(r'```\w*\n?', '', llm_response)

        search_count = len(self._SEARCH_MARKER_RE.findall(text))
        if search_count == 0:
            return None  # no patch markers at all

        problems: List[str] = []

        # Check for wrong closing markers
        wrong_matches = self._WRONG_CLOSE_RE.findall(text)
        if wrong_matches:
            variants = ', '.join(f'"{v}"' for v in set(wrong_matches))
            problems.append(f'Found closing marker with {variants} but the closing marker must be ">>>>>>> REPLACE".')

        # Count valid closing markers
        valid_close_count = len(self._VALID_CLOSE_RE.findall(text))
        if valid_close_count != search_count and not wrong_matches:
            problems.append(f'Found {search_count} SEARCH marker(s) but {valid_close_count} number of REPLACE closing marker(s).')

        # If we have SEARCH + REPLACE but no separator between them
        if not problems and valid_close_count > 0:
            # Check if any complete block is actually parseable
            if not _PATCH_PATTERN.search(text):
                problems.append(
                    'Found SEARCH and REPLACE markers but could not parse '
                    'complete patch blocks. Check that each block has a '
                    '"=======" separator between SEARCH and REPLACE sections.'
                )

        # If no problems detected, the format is valid
        if not problems:
            return None

        return '\n'.join(problems)

    def apply_patches(self, original_code: str, patches: List[PatchBlock]) -> str:
        """Apply *patches* sequentially to *original_code*.

        Each patch's SEARCH block is located in the (possibly already-
        modified) code via flexible matching, then replaced with the
        REPLACE block.

        Returns:
            The patched code.

        Raises:
            RuntimeError: If any SEARCH block cannot be found.
        """
        self.error_message = ''
        code_lines = original_code.splitlines()

        for _, patch in enumerate(patches):
            code_lines, _ = self._apply_single_patch(code_lines, patch, search_start=0)

        return '\n'.join(code_lines)

    def try_apply(self, original_code: str, llm_response: str) -> Optional[str]:
        """Convenience: parse patches then apply them.

        Returns:
            Patched code string, or ``None`` if no patches were found.

        Raises:
            RuntimeError: If patches were found but could not be applied
            (SEARCH block not located in code).
        """
        patches = self.parse_patches(llm_response)
        if not patches:
            return None
        return self.apply_patches(original_code, patches)

    # ------------------------------------------------------------------
    # Normalization
    # ------------------------------------------------------------------

    # Single-pass regex for Verilog operators, ordered by decreasing length
    # so that === matches before ==, !== before !=, etc.
    _OP_RE = re.compile(r'\s*(===|!==|<=|>=|==|!=)\s*')

    def _normalize_verilog_line(self, line: str, strip_comments: bool=False) -> str:
        """Normalize a single line for flexible matching.

        Does **not** strip comments — only normalizes whitespace around
        common Verilog operators and punctuation.
        """
        # Normalize operators in a single pass to avoid partial-match issues
        line = self._OP_RE.sub(lambda m: f' {m.group(1)} ', line)

        # Single-char punctuation
        line = re.sub(r'\s*,\s*', ', ', line)
        line = re.sub(r'\s*;\s*', '; ', line)
        line = re.sub(r'\s*\(\s*', '(', line)
        line = re.sub(r'\s*\)\s*', ') ', line)
        line = re.sub(r'\s*\[\s*', '[', line)
        line = re.sub(r'\s*\]\s*', '] ', line)
        line = re.sub(r'\s*\{\s*', '{ ', line)
        line = re.sub(r'\s*\}\s*', '} ', line)

        # Collapse whitespace and strip
        line = re.sub(r'\s+', ' ', line)
        if strip_comments:
            # Drop line comments
            line = re.sub(r'//.*$', '', line)
        return line.strip()

    # ------------------------------------------------------------------
    # Block matching
    # ------------------------------------------------------------------

    def _strip_line_comment(self, s: str) -> str:
        return re.sub(r'//.*$', '', s)
    
    def _is_effectively_blank(self, s: str) -> bool:
        return self._strip_line_comment(s).strip() == ''

    def _find_block_in_code(
        self,
        code_lines: List[str],
        search_lines: List[str],
        start_from: int = 0,
    ) -> Optional[Tuple[int, int]]:
        """Find a contiguous block of *search_lines* in *code_lines*.

        Uses normalized comparison. Blank lines in the code are skipped
        during matching (but still counted for index purposes).

        Returns:
            ``(start_index, end_index_exclusive)`` or ``None``.
        """
        # Filter out completely blank search lines and line comments for matching
        search_clean = [self._strip_line_comment(ln) for ln in search_lines]
        search_stripped = [ln for ln in search_clean if ln.strip()]
        comment_only_search = False
        if not search_stripped:
            # fallback: use original search_lines (comment-aware)
            comment_only_search = True
            search_stripped = [ln for ln in search_lines if ln.strip()]
            norm_search = [self._normalize_verilog_line(ln, strip_comments=False) for ln in search_stripped]
        else:
            norm_search = [self._normalize_verilog_line(ln, strip_comments=True) for ln in search_stripped]

        for i in range(start_from, len(code_lines)):
            # Try to match starting at position i
            si = 0  # search index
            ci = i  # code index
            while si < len(norm_search) and ci < len(code_lines):
                if not comment_only_search and self._is_effectively_blank(code_lines[ci]):
                    ci += 1  # skip blank lines in code
                    continue
                if self._normalize_verilog_line(code_lines[ci], strip_comments=(not comment_only_search)) == norm_search[si]:
                    si += 1
                    ci += 1
                else:
                    break

            if si == len(norm_search):
                return (i, ci)

        return None

    # ------------------------------------------------------------------
    # Single patch application
    # ------------------------------------------------------------------

    def _apply_single_patch(
        self,
        code_lines: List[str],
        patch: PatchBlock,
        search_start: int = 0,
    ) -> Tuple[List[str], int]:
        """Apply one patch to *code_lines*.

        Handles indentation: detects the indent delta between the SEARCH
        block and the matched code, then applies that delta to every line
        in the REPLACE block.

        Returns:
            ``(new_code_lines, position_after_replacement)``

        Raises:
            RuntimeError: If the SEARCH block cannot be found.
        """
        search_lines = patch.search.splitlines()
        replace_lines = patch.replace.splitlines() if patch.replace.strip() else []

        loc = self._find_block_in_code(code_lines, search_lines, start_from=search_start)
        if loc is None:
            self.error_message = (
                f'SEARCH block not found in code:\n{patch}'
            )
            raise RuntimeError(self.error_message)

        match_start, match_end = loc

        # Compute indentation delta
        code_indent = self._leading_whitespace(code_lines[match_start])
        search_non_blank = [ln for ln in search_lines if ln.strip()]
        search_indent = self._leading_whitespace(search_non_blank[0]) if search_non_blank else ''

        indent_delta = len(code_indent) - len(search_indent)

        # Re-indent replacement lines
        reindented = []
        for rline in replace_lines:
            if not rline.strip():
                reindented.append('')
            elif indent_delta > 0:
                reindented.append(' ' * indent_delta + rline)
            elif indent_delta < 0:
                # Remove up to |indent_delta| leading spaces
                stripped = rline.lstrip(' ')
                removed = len(rline) - len(stripped)
                keep = max(0, removed + indent_delta)
                reindented.append(' ' * keep + stripped)
            else:
                reindented.append(rline)

        new_lines = code_lines[:match_start] + reindented + code_lines[match_end:]
        next_pos = match_start + len(reindented)
        return new_lines, next_pos

    @staticmethod
    def _leading_whitespace(line: str) -> str:
        """Return the leading whitespace of *line*."""
        return line[: len(line) - len(line.lstrip(' \t'))]
