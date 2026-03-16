from typing import List, Tuple, Optional


# Comment delimiters: (open, close)
_BLOCK_COMMENTS = [('/*', '*/'), ('(*', '*)')]


def _is_in_string(line: str, pos: int) -> bool:
    """Check whether character at `pos` sits inside a string literal."""
    in_str = False
    for j in range(pos):
        if line[j] in ('"', "'"):
            in_str = not in_str
    return in_str


def _is_word_boundary(line: str, pos: int, length: int) -> bool:
    """Return True if the token at line[pos:pos+length] is a standalone word."""
    if pos > 0 and line[pos - 1].isalnum():
        return False
    if pos + length < len(line) and line[pos + length].isalnum():
        return False
    return True


def _strip_block_comments(raw: str, in_block: bool, opener: Optional[str]) -> Tuple[str, bool, Optional[str]]:
    """Remove block-comment content from *raw*, tracking cross-line state."""
    out: List[str] = []
    j = 0
    while j < len(raw):
        if not in_block:
            started = False
            for op, _ in _BLOCK_COMMENTS:
                if raw[j : j + 2] == op:
                    in_block, opener, started = True, op, True
                    j += 2
                    break
            if started:
                continue
            out.append(raw[j])
            j += 1
        else:
            close = next(cl for op, cl in _BLOCK_COMMENTS if op == opener)
            if raw[j : j + 2] == close:
                in_block, opener = False, None
                j += 2
            else:
                j += 1
    return ''.join(out), in_block, opener


class Code_scope:
    """
    A class to find upper scopes in code for languages like Scala, C++, and Verilog.
    Given a set of line numbers, it returns the continuous scopes that contain these lines.
    """

    def __init__(self, code_text: str, line_limit: int = 10) -> None:
        """
        Initialize with the code text.

        Args:
            code_text (str): The full source code text.
            line_limit (int): Maximum number of lines to search up/down for a scope boundary.
        """
        self.lines = code_text.splitlines()
        self.num_lines = len(self.lines)
        self.line_limit = line_limit
        self.scopes = self._parse_scopes()

    def _parse_scopes(self) -> List[Tuple[int, int]]:
        """
        Parse the code to identify all scopes.

        Returns:
            list: A list of tuples (start_line, end_line) representing scopes.
        """
        open_markers = ['{', 'begin']
        close_markers = ['}', 'end']
        scopes: List[Tuple[int, int]] = []
        scope_stack: List[Tuple[int, int]] = []
        in_block = False
        opener: Optional[str] = None

        for i in range(self.num_lines):
            line = self.lines[i]

            # --- strip block comments (cross-line aware) ---
            cleaned, in_block, opener = _strip_block_comments(line, in_block, opener)
            if in_block:
                continue

            # --- strip single-line comments ---
            for cm in ('//', '#'):
                pos = cleaned.find(cm)
                if pos != -1:
                    cleaned = cleaned[:pos]

            stripped = cleaned.strip()
            if not stripped:
                continue

            # --- check opening markers ---
            for idx, marker in enumerate(open_markers):
                pos = stripped.find(marker)
                if pos == -1:
                    continue
                if marker == 'begin' and not _is_word_boundary(stripped, pos, len(marker)):
                    continue
                if marker == '{' and _is_in_string(stripped, pos):
                    continue
                scope_stack.append((i, idx))
                break

            # --- check closing markers ---
            for idx, marker in enumerate(close_markers):
                pos = stripped.find(marker)
                if pos == -1:
                    continue
                if marker == 'end' and not _is_word_boundary(stripped, pos, len(marker)):
                    continue
                if marker == '}' and _is_in_string(stripped, pos):
                    continue
                if scope_stack and scope_stack[-1][1] == idx:
                    start_line, _ = scope_stack.pop()
                    if i - start_line <= self.line_limit:
                        scopes.append((start_line, i))
                    else:
                        scopes.append((max(0, i - self.line_limit), i))
                break

            # Handle unclosed scopes
        while scope_stack:
            start_line, _ = scope_stack.pop()
            end_line = min(start_line + self.line_limit, self.num_lines - 1)
            scopes.append((start_line, end_line))

        return scopes

    def find_scopes_for_lines(self, line_numbers):
        """
        Find all continuous scopes that contain the specified line numbers.

        Args:
            line_numbers (list): A list of line numbers (0-indexed).

        Returns:
            list: A list of tuples (start_line, end_line) representing continuous scopes.
        """
        # Validate line numbers
        valid_line_numbers = [ln for ln in line_numbers if 0 <= ln < self.num_lines]
        if not valid_line_numbers:
            return []

        # Sort the line numbers
        valid_line_numbers.sort()

        # Find containing scopes for each line
        containing_scopes = []
        for line_num in valid_line_numbers:
            for start, end in self.scopes:
                if start <= line_num <= end:
                    containing_scopes.append((start, end))

        # If no scopes found, create artificial scopes using line limit
        if not containing_scopes:
            for line_num in valid_line_numbers:
                start = max(0, line_num - self.line_limit)
                end = min(self.num_lines - 1, line_num + self.line_limit)
                containing_scopes.append((start, end))

        # Sort scopes by start line
        containing_scopes.sort()

        # Merge continuous scopes
        merged_scopes = []
        if containing_scopes:
            current_scope = containing_scopes[0]

            for scope in containing_scopes[1:]:
                # If the current scope is continuous with the next one, merge them
                if scope[0] <= current_scope[1] + 1:
                    current_scope = (current_scope[0], max(current_scope[1], scope[1]))
                else:
                    merged_scopes.append(current_scope)
                    current_scope = scope

            merged_scopes.append(current_scope)

        return merged_scopes

    def find_nearest_upper_scopes(self, line_numbers):
        """
        Find the nearest upper scopes that contain the specified line numbers.

        Args:
            line_numbers (list): A list of line numbers (0-indexed).

        Returns:
            list: A list of tuples (start_line, end_line) representing the nearest upper scopes.
        """
        valid_line_numbers = [ln for ln in line_numbers if 0 <= ln < self.num_lines]
        if not valid_line_numbers:
            return []

        # Group continuous line numbers
        valid_line_numbers.sort()
        line_groups = []
        current_group = [valid_line_numbers[0]]

        for line in valid_line_numbers[1:]:
            if line == current_group[-1] + 1:
                current_group.append(line)
            else:
                line_groups.append(current_group)
                current_group = [line]

        line_groups.append(current_group)

        # Find the nearest upper scope for each group
        upper_scopes = []
        for group in line_groups:
            group_min, group_max = min(group), max(group)

            # Find all scopes that contain this group
            containing_scopes = [(start, end) for start, end in self.scopes if start <= group_min and group_max <= end]

            # Sort by scope size (smaller scopes first)
            containing_scopes.sort(key=lambda x: x[1] - x[0])

            if containing_scopes:
                # Get the smallest scope that contains the entire group
                upper_scopes.append(containing_scopes[0])
            else:
                # If no scope found, create artificial scope using line limit
                start = max(0, group_min - self.line_limit)
                end = min(self.num_lines - 1, group_max + self.line_limit)
                upper_scopes.append((start, end))

        # Handle overlap between scopes
        upper_scopes.sort()
        merged_scopes = []
        if upper_scopes:
            current_scope = upper_scopes[0]

            for scope in upper_scopes[1:]:
                # If the scopes overlap, merge them
                if scope[0] <= current_scope[1]:
                    current_scope = (current_scope[0], max(current_scope[1], scope[1]))
                else:
                    merged_scopes.append(current_scope)
                    current_scope = scope

            merged_scopes.append(current_scope)

        return merged_scopes

    def get_code(self, scope, mark, hint):
        """
        Extract code from a specified scope and mark certain lines with a hint.

        Args:
            scope (tuple): A tuple (start_line, end_line) representing the scope to extract.
            mark (list): A list of line numbers to mark with the hint.
            hint (str): The string to add before marked lines.

        Returns:
            str: Formatted code with line numbers and hints.
        """
        # Ensure the scope is valid
        start_line, end_line = scope

        # Convert mark to a set for faster lookups
        mark_set = set(mark)

        # Format each line in the scope
        result = []
        for line_num in range(start_line, end_line + 1):
            # Determine if this line should be marked
            prefix = hint if line_num in mark_set else ' ' * len(hint)

            # Format the line with line number
            formatted_line = f'{prefix} {line_num}: {self.lines[line_num]}'
            result.append(formatted_line)

        # Join all formatted lines with newlines
        return '\n'.join(result)
