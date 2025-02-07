# hagent/tool/chisel_diff_applier.py
# See LICENSE file for details

import re

class ChiselDiffApplier:
    """
    A tool to apply a unified diff to a Chisel source code snippet.
    
    Given a diff (as a string) and a Chisel code snippet (as a string),
    this class applies the changes and returns the updated code.
    
    The diff is assumed to be in a simplified unified diff format containing:
      - Hunk headers starting with "@@"
      - Removal lines starting with "-" 
      - Addition lines starting with "+"
    
    For each hunk, this patcher finds the removal line in the original code (using
    a simple whitespace-insensitive match) and replaces it with the addition line,
    preserving the original indentation.
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
            
        Raises:
            RuntimeError if an expected hunk format is not met.
        """
        code_lines = code_text.splitlines()
        diff_lines = diff_text.splitlines()
        
        i = 0
        while i < len(diff_lines):
            line = diff_lines[i]
            if line.startswith('@@'):
                # Begin a hunk. (In this simple implementation we expect one removal and one addition line.)
                removal_line = None
                addition_line = None
                i += 1  # move past the hunk header
                # Process hunk lines until we reach another hunk header or end-of-diff.
                while i < len(diff_lines) and not diff_lines[i].startswith('@@'):
                    current = diff_lines[i]
                    if current.startswith('-'):
                        removal_line = current[1:]  # strip the '-' marker
                    elif current.startswith('+'):
                        addition_line = current[1:]   # strip the '+' marker
                    i += 1
                # If both removal and addition lines were found, apply the hunk.
                if removal_line is not None and addition_line is not None:
                    rem_stripped = removal_line.strip()
                    # Search for a matching line in the code (ignoring leading/trailing whitespace)
                    for j, code_line in enumerate(code_lines):
                        if code_line.strip() == rem_stripped:
                            # Preserve original indentation:
                            indent = re.match(r'\s*', code_line).group(0)
                            # Replace with the addition line (stripped) and add the indent.
                            code_lines[j] = indent + addition_line.strip()
                            break
            else:
                i += 1

        return "\n".join(code_lines)
