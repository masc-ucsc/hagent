class Diagnostic:
    def __init__(self, error_str: str):
        parts = error_str.split('\n', 1)
        main_msg = parts[0]
        self.hint: str = parts[1] if len(parts) > 1 else ''
        self.error: bool = False
        self.loc: int = 0
        self.file: str = ''

        try:
            msg_parts = main_msg.split(':')
            self.file = msg_parts[0]
            self.loc = int(msg_parts[1])
            self.msg = msg_parts[-1].strip()

            if 'error:' in main_msg:
                self.msg = main_msg.split('error:')[-1].strip()
                self.error = True
            elif 'warning:' in main_msg:
                self.msg = main_msg.split('warning:')[-1].strip()  # Fixed: split by warning
        except (ValueError, IndexError):  # Handle potential errors
            self.loc = -1
            self.msg = main_msg.strip()  # Fallback to the entire line

    def insert_comment(self, code: str, prefix: str) -> str:
        """
        Inserts a multi-line comment into a string of code at a specific line number.

        Args:
            code: The original multi-line string of code.
            prefix: The comment prefix (e.g., "#" for Python, "//" for C/C++).

        Returns:
            The modified string of code with the comment inserted.
        """
        code_lines = code.splitlines(keepends=True)
        add_lines = self.msg.splitlines() + self.hint.splitlines()
        if self.loc < 1 or self.loc > len(code_lines) + 1:
            raise ValueError('Invalid line number (self.loc)')
        # Create commented lines
        commented_add_lines = [f'{prefix} FIXME_HINT: {line.rstrip()}\n' for line in add_lines]
        # Insert commented lines at the specified location
        code_lines[self.loc - 1 : self.loc - 1] = commented_add_lines
        return ''.join(code_lines)

    def to_str(self):
        if self.error:
            txt = 'an error'
        else:
            txt = 'an warning'
        if self.hint:
            txt2 = f'Possible hint:\n{self.hint}'
        else:
            txt2 = ''

        return f"""File {self.file} Line {self.loc} has {txt} stating:
{self.msg}
{txt2}
"""
