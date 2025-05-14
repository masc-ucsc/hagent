# hagent/tool/memory/utils.py

import re

def normalize_code(code: str) -> str:
    """Normalize code for better comparison by removing extra whitespace and comments"""
    # Remove C++ style comments
    code = re.sub(r'//.*?\n', '\n', code)
    code = re.sub(r'/\*.*?\*/', '', code, flags=re.DOTALL)
    
    # Remove blank lines and leading/trailing whitespace
    lines = [line.strip() for line in code.splitlines() if line.strip()]
    
    # Remove whitespace between tokens while preserving tokens
    normalized_lines = []
    for line in lines:
        # Keep important whitespace (between words/identifiers) but normalize it
        normalized_line = re.sub(r'\s+', ' ', line)
        normalized_lines.append(normalized_line)
    
    return '\n'.join(normalized_lines)
