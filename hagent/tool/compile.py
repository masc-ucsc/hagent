
from os import error


class Diagnostic:
    def __init__(self, error_str: str):
        parts = error_str.split('\n', 1)
        main_msg = parts[0]
        self.hint: str = parts[1] if len(parts) > 1 else ''
        self.error: bool = False
        self.loc: int = 0

        try:
            msg_parts = main_msg.split(':')
            self.loc = int(msg_parts[1])
            self.msg = msg_parts[-1].strip()

            if 'error:' in main_msg:
                self.msg = main_msg.split('error:')[-1].strip()
                self.error = True
            elif 'warning:' in main_msg:
                self.msg = main_msg.split('warning:')[-1].strip() # Fixed: split by warning
        except (ValueError, IndexError): # Handle potential errors
            self.loc = -1
            self.msg = main_msg.strip()  # Fallback to the entire line

    def to_str(self):
        if self.error:
            txt = "an error"
        else:
            txt = "an warning"
        if self.hint:
            txt2 = f"Possible hint:\n{self.hint}"
        else:
            txt2 = ""

        return f"""Line {self.loc} has {txt} stating:
{self.msg}
{txt2}
"""

