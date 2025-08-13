import re


class MetadataMapper:
    """
    Parses metadata comments in Verilog code and maps them to Scala (Chisel) source lines.

    Usage:
        mapper = MetadataMapper(verilog_original_str, verilog_fixed_str)
        pointers = mapper.pointers_for_diff(verilog_diff_str)
        if pointers:
            snippet = mapper.slice_chisel_by_pointers(chisel_code_str, pointers, before=5, after=20)
    """

    METADATA_REGEX = re.compile(r'//\s*(?P<path>[\w/\.\-]+):(?P<line>\d+)')

    def __init__(self, verilog_orig: str = '', verilog_fixed: str = ''):
        # Store Verilog lines for both original and fixed versions
        self.verilog_orig_lines = verilog_orig.splitlines()
        self.verilog_fixed_lines = verilog_fixed.splitlines()

        # Build metadata maps for quick lookup if needed
        self.metadata_map_orig = self.build_metadata_map(self.verilog_orig_lines)
        self.metadata_map_fixed = self.build_metadata_map(self.verilog_fixed_lines)

    def build_metadata_map(self, lines: list) -> dict:
        """
        Build a mapping from line index (0-based) to (scala_file_path, scala_line_no).
        """
        metadata_map = {}
        for idx, line in enumerate(lines):
            m = self.METADATA_REGEX.search(line)
            if m:
                path = m.group('path')
                lineno = int(m.group('line'))
                metadata_map[idx] = (path, lineno)
        return metadata_map

    def pointers_for_diff(self, diff_text: str) -> list:
        """
        Given unified diff text, collect metadata pointers found in diff lines.
        Returns a deduplicated list of (scala_path, scala_line_no).
        """
        pointers = []
        for line in diff_text.splitlines():
            m = self.METADATA_REGEX.search(line)
            if not m:
                continue
            path = m.group('path')
            lineno = int(m.group('line'))
            pointers.append((path, lineno))
        # Deduplicate preserving order
        seen = set()
        unique = []
        for p in pointers:
            if p not in seen:
                seen.add(p)
                unique.append(p)
        return unique

    def slice_chisel_by_pointers(self, chisel_code: str, pointers: list, before: int = 5, after: int = 5) -> str:
        """
        Extract code snippets around each scala_line_no in the Chisel code string.
        Marks the target line with '->'.

        Args:
            chisel_code: full Chisel (Scala) source as string.
            pointers: list of (scala_path, scala_line_no) tuples.
            before: number of lines before the pointer to include.
            after: number of lines after the pointer to include.

        Returns:
            A single string containing one or more snippets.
        """
        code_lines = chisel_code.splitlines()
        snippets = []
        for path, lineno in pointers:
            idx = lineno - 1  # convert to 0-based index
            start = max(0, idx - before)
            end = min(len(code_lines), idx + after + 1)
            snippets.append(f'Code snippet from {path} lines {start + 1}-{end}:')
            for i in range(start, end):
                marker = '->' if i == idx else '  '
                snippets.append(f'{marker} {i + 1}: {code_lines[i]}')
            snippets.append('')
        return '\n'.join(snippets)
