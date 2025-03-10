class Code_scope:
    """
    A class to find upper scopes in code for languages like Scala, C++, and Verilog.
    Given a set of line numbers, it returns the continuous scopes that contain these lines.
    """

    def __init__(self, code_text, line_limit=10):
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

    def _parse_scopes(self):
        """
        Parse the code to identify all scopes.

        Returns:
            list: A list of tuples (start_line, end_line, level) representing scopes.
        """
        scopes = []
        scope_stack = []
        open_markers = ['{', 'begin']
        close_markers = ['}', 'end']

        # Track if we're in a comment
        in_block_comment = False
        block_comment_start = None

        i = 0
        while i < self.num_lines:
            line = self.lines[i].strip()
            original_line = self.lines[i]

            # Process comments first to avoid finding markers in comments

            # Handle single-line comments
            if not in_block_comment:
                # Check for single line comments (// or #)
                comment_pos = -1
                for comment_marker in ['//', '#']:
                    pos = line.find(comment_marker)
                    if pos != -1 and (comment_pos == -1 or pos < comment_pos):
                        comment_pos = pos

                if comment_pos != -1:
                    line = line[:comment_pos].strip()
                    if not line:
                        i += 1
                        continue

            # Handle multi-line comments (/* */, (* *))
            j = 0
            processed_line = ''
            while j < len(original_line):
                if not in_block_comment:
                    # Check for comment start
                    if j < len(original_line) - 1:
                        if original_line[j : j + 2] == '/*':
                            in_block_comment = True
                            block_comment_start = '/*'
                            j += 2
                            continue
                        elif original_line[j : j + 2] == '(*':
                            in_block_comment = True
                            block_comment_start = '(*'
                            j += 2
                            continue

                    if j < len(original_line):
                        processed_line += original_line[j]
                    j += 1
                else:
                    # Check for comment end
                    if j < len(original_line) - 1:
                        if block_comment_start == '/*' and original_line[j : j + 2] == '*/':
                            in_block_comment = False
                            j += 2
                            continue
                        elif block_comment_start == '(*' and original_line[j : j + 2] == '*)':
                            in_block_comment = False
                            j += 2
                            continue
                    j += 1

            # If we're in a comment, continue to next line
            if in_block_comment:
                i += 1
                continue

            # Skip empty lines after comment processing
            if not processed_line.strip():
                i += 1
                continue

            line = processed_line.strip()

            # Check for opening markers with line limit
            for idx, marker in enumerate(open_markers):
                if marker in line:
                    # Get position of the marker in the line
                    pos = line.find(marker)

                    # Make sure it's a real block opening, not part of another word (for 'begin')
                    if marker == 'begin':
                        if pos > 0 and line[pos - 1].isalnum():
                            continue
                        if pos + len(marker) < len(line) and line[pos + len(marker)].isalnum():
                            continue

                    # For C++ and Scala style, check if this is actually opening a scope
                    if marker == '{':
                        # Ensure we're not in a string or character literal
                        string_quotes = ['"', "'"]
                        in_string = False
                        for j in range(pos):
                            if line[j] in string_quotes:
                                in_string = not in_string
                        if in_string:
                            continue

                    scope_stack.append((i, idx))
                    break

            # Check for closing markers with line limit
            for idx, marker in enumerate(close_markers):
                if marker in line:
                    pos = line.find(marker)

                    # Similar checks as for opening markers
                    if marker == 'end':
                        if pos > 0 and line[pos - 1].isalnum():
                            continue
                        if pos + len(marker) < len(line) and line[pos + len(marker)].isalnum():
                            continue

                    # For C++ and Scala style, check if this is actually closing a scope
                    if marker == '}':
                        # Ensure we're not in a string
                        string_quotes = ['"', "'"]
                        in_string = False
                        for j in range(pos):
                            if line[j] in string_quotes:
                                in_string = not in_string
                        if in_string:
                            continue

                    # Try to match with an opening marker
                    if scope_stack and scope_stack[-1][1] == idx:
                        start_line, _ = scope_stack.pop()
                        # Only add scope if within the line limit
                        if i - start_line <= self.line_limit:
                            scopes.append((start_line, i))
                        else:
                            # Create limited scope based on the line limit
                            scopes.append((max(0, i - self.line_limit), i))

            i += 1

        # Handle unclosed scopes (using line limit)
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

