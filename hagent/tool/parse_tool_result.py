# See LICENSE for details

"""
Framework for parsing EDA tool output into LLM-friendly feedback.

Design: Strategy Pattern + Template Method with auto-detection registry.

Usage:
    from hagent.tool.parse_tool_result import get_tool_result_parser

    parser = get_tool_result_parser(Path('elab.log'))
    if parser:
        parser.parse()
        feedback = parser.format_for_llm(target_module='cva6_mmu')

Each child class:
  1. Defines its own internal data structures
  2. Detects whether raw text belongs to its tool (classmethod detect())
  3. Parses raw text into internal structures (parse())
  4. Formats into LLM-consumable strings (format_for_llm())
"""

import os
import re
from abc import abstractmethod
from dataclasses import dataclass
from pathlib import Path
from typing import Dict, List, Optional, Union

from hagent.core.tracer import TracerABCMetaClass


@dataclass
class CategorizedError:
    """An error categorized for FewShotMemory lookup.

    Attributes:
        error_type: Category string, e.g. "missing_port", "undeclared_identifier",
            "type_mismatch", "syntax_error". Used as the FewShotMemory error_type key.
        context: Short description with specifics (e.g. "port satp_ppn_i in cva6_mmu").
    """

    error_type: str
    context: str


class ParseToolResultForLLM(metaclass=TracerABCMetaClass):
    """Abstract base for parsing tool output into LLM-friendly feedback."""

    def __init__(self):
        self.raw_text: str = ''
        self.last_error: str = ''

    def load(self, source: Union[str, Path]) -> bool:
        """Load raw text from a string or file path. Returns success."""
        try:
            if isinstance(source, Path):
                self.raw_text = source.read_text(errors='replace')
            elif isinstance(source, str) and os.path.isfile(source):
                self.raw_text = Path(source).read_text(errors='replace')
            else:
                self.raw_text = source
            return True
        except Exception as e:
            self.last_error = f'Failed to load source: {e}'
            return False

    @classmethod
    @abstractmethod
    def detect(cls, text: str) -> bool:
        """Return True if this parser handles the given tool output."""

    @abstractmethod
    def parse(self) -> bool:
        """Parse self.raw_text into child-specific internal structures. Returns success."""

    @abstractmethod
    def format_for_llm(self, **kwargs) -> str:
        """Format parsed results into LLM-friendly text. kwargs are child-specific."""

    @abstractmethod
    def categorize_errors(self) -> List[CategorizedError]:
        """Categorize parsed errors for FewShotMemory lookup.

        Returns a list of CategorizedError with error_type suitable for
        memory.find(error_type=...) and memory.add(error_type=...).

        Must be called after parse().
        """

    def get_primary_error_type(self) -> str:
        """Return the most prominent error category, or 'unknown'.

        Convenience method: returns the error_type of the first categorized
        error. Useful as the single key for FewShotMemory queries.
        """
        cats = self.categorize_errors()
        return cats[0].error_type if cats else 'unknown'


# ---------------------------------------------------------------------------
# Registry and factory
# ---------------------------------------------------------------------------

_PARSER_REGISTRY: List[type] = []


def register_parser(cls):
    """Decorator to register a parser class for auto-detection."""
    _PARSER_REGISTRY.append(cls)
    return cls


def get_tool_result_parser(source: Union[str, Path]) -> Optional[ParseToolResultForLLM]:
    """Auto-detect and return the right parser for the given tool output.

    Args:
        source: Raw text string, or a Path / filepath string pointing to a log file.

    Returns:
        An initialized and loaded parser, or None if no parser matches.
    """
    if isinstance(source, Path):
        text = source.read_text(errors='replace')
    elif isinstance(source, str) and os.path.isfile(source):
        text = Path(source).read_text(errors='replace')
    else:
        text = source

    for parser_cls in _PARSER_REGISTRY:
        if parser_cls.detect(text):
            p = parser_cls()
            p.raw_text = text
            return p
    return None


# ---------------------------------------------------------------------------
# Slang elaboration parser
# ---------------------------------------------------------------------------


@dataclass
class SlangDiagnostic:
    """A single diagnostic from the slang frontend."""

    file: str  # basename, e.g. "cva6_mmu.sv"
    line: int
    col: int
    severity: str  # "error", "warning", "note", "fatal error"
    message: str
    source_line: str = ''  # the actual code line if captured


@register_parser
class ParseSlangElabForLLM(ParseToolResultForLLM):
    """Parses yosys read_slang (slang frontend) elaboration logs.

    Detects via "Executing SLANG frontend" marker in the log.
    """

    # file:line:col: severity: message
    _DIAG_RE = re.compile(r'^(.+?):(\d+):(\d+):\s+(error|warning|note|fatal error):\s+(.+)$')

    def __init__(self):
        super().__init__()
        self.diagnostics: List[SlangDiagnostic] = []

    @classmethod
    def detect(cls, text: str) -> bool:
        return 'Executing SLANG frontend' in text

    def parse(self) -> bool:
        self.diagnostics = []
        lines = self.raw_text.splitlines()
        i = 0
        while i < len(lines):
            m = self._DIAG_RE.match(lines[i])
            if m:
                filepath, line_no, col_no, severity, message = m.groups()
                basename = os.path.basename(filepath)
                source_line = ''

                # Next line is typically the source code line, followed by a caret line
                if i + 1 < len(lines) and not self._DIAG_RE.match(lines[i + 1]):
                    candidate = lines[i + 1]
                    # Skip if it's a caret/pointer line
                    if not re.match(r'^\s*[\^~]+\s*$', candidate.strip()):
                        source_line = candidate.strip()
                    # Skip source line + caret line
                    i += 1
                    if i + 1 < len(lines) and re.match(r'^\s*[\^~]+\s*$', lines[i + 1].strip()):
                        i += 1

                self.diagnostics.append(
                    SlangDiagnostic(
                        file=basename,
                        line=int(line_no),
                        col=int(col_no),
                        severity=severity,
                        message=message,
                        source_line=source_line,
                    )
                )
            i += 1
        return True

    def format_for_llm(self, **kwargs) -> str:
        """Format slang diagnostics for LLM consumption.

        Keyword Args:
            target_module: Name of the module being optimized (without extension).
                Errors in the target module get compact inline format.
                Errors in other modules get grouped by category.
        """
        target_module = kwargs.get('target_module', '')

        if not self.diagnostics:
            return 'No diagnostics found in elaboration log.'

        # Split diagnostics by whether they belong to the target module's file
        target_files = set()
        if target_module:
            target_files = {f'{target_module}.sv', f'{target_module}.v'}

        target_diags: List[SlangDiagnostic] = []
        other_diags: List[SlangDiagnostic] = []

        for d in self.diagnostics:
            if d.file in target_files:
                target_diags.append(d)
            else:
                other_diags.append(d)

        parts = []

        # Format target module errors/warnings: compact inline
        if target_diags:
            parts.append(f'Errors in {target_module} (the module you are optimizing):')
            for d in target_diags:
                if d.severity == 'note':
                    continue
                src = f' [{d.source_line}]' if d.source_line else ''
                parts.append(f'  {d.file}:{d.line}:{d.col}{src}: {d.severity}: {d.message}')
                # Attach any following notes
                for n in self.diagnostics:
                    if n.severity == 'note' and n.file == d.file:
                        # Only attach notes that are contextually close (within 100 lines)
                        if abs(n.line - d.line) < 100:
                            nsrc = f' [{n.source_line}]' if n.source_line else ''
                            parts.append(f'    {n.file}:{n.line}:{n.col}{nsrc}: note: {n.message}')

        # Format other-module errors: group by error category
        if other_diags:
            other_formatted = self._format_other_module_diags(other_diags)
            if other_formatted:
                parts.append('')
                parts.append(other_formatted)

        return '\n'.join(parts)

    # Patterns for error categorization
    _PORT_NOT_EXIST_RE = re.compile(r"port '(\w+)' does not exist in '(\w+)'")
    _UNDECLARED_RE = re.compile(r"use of undeclared identifier '(\w+)'")
    _TYPE_MISMATCH_RE = re.compile(r'inequivalent type|type mismatch', re.IGNORECASE)
    _DECL_AFTER_STMT_RE = re.compile(r'declaration must come before all statements', re.IGNORECASE)

    def categorize_errors(self) -> List[CategorizedError]:
        """Categorize slang diagnostics for FewShotMemory lookup."""
        result: List[CategorizedError] = []
        seen: set = set()

        for d in self.diagnostics:
            if d.severity in ('note'):
                continue

            m = self._PORT_NOT_EXIST_RE.search(d.message)
            if m:
                key = ('missing_port', m.group(1))
                if key not in seen:
                    seen.add(key)
                    result.append(CategorizedError('missing_port', f'port {m.group(1)} in {m.group(2)}'))
                continue

            m = self._UNDECLARED_RE.search(d.message)
            if m:
                key = ('undeclared_identifier', m.group(1))
                if key not in seen:
                    seen.add(key)
                    result.append(CategorizedError('undeclared_identifier', f'identifier {m.group(1)} at {d.file}:{d.line}'))
                continue

            if self._TYPE_MISMATCH_RE.search(d.message):
                key = ('type_mismatch', d.message)
                if key not in seen:
                    seen.add(key)
                    result.append(CategorizedError('type_mismatch', f'{d.file}:{d.line}: {d.message}'))
                continue

            if self._DECL_AFTER_STMT_RE.search(d.message):
                key = ('declaration_after_statement', d.file)
                if key not in seen:
                    seen.add(key)
                    result.append(CategorizedError('declaration_after_statement', f'{d.file}:{d.line}: {d.message}'))
                continue

            # Fallback: use first few words of the message as context
            key = ('syntax_error', d.message)
            if key not in seen:
                seen.add(key)
                result.append(CategorizedError('syntax_error', f'{d.file}:{d.line}: {d.message}'))

        return result

    def _format_other_module_diags(self, diags: List[SlangDiagnostic]) -> str:
        """Group other-module diagnostics by category for concise LLM feedback."""
        # Category 1: "port 'X' does not exist in 'MODULE'"
        port_not_exist_re = re.compile(r"port '(\w+)' does not exist in '(\w+)'")
        missing_ports: Dict[str, set] = {}  # module_name -> set of port names

        # Category 2: type mismatch
        type_mismatch: List[str] = []

        # Category 3: everything else
        other: List[str] = []

        for d in diags:
            if d.severity == 'note' or d.severity == 'warning':
                continue

            m = port_not_exist_re.search(d.message)
            if m:
                port_name, module_name = m.groups()
                missing_ports.setdefault(module_name, set()).add(port_name)
                continue

            if 'type' in d.message.lower() and ('mismatch' in d.message.lower() or 'inequivalent' in d.message.lower()):
                src = f' [{d.source_line}]' if d.source_line else ''
                type_mismatch.append(f'  {d.file}:{d.line}:{d.col}{src}: {d.message}')
                continue

            src = f' [{d.source_line}]' if d.source_line else ''
            other.append(f'  {d.file}:{d.line}:{d.col}{src}: {d.severity}: {d.message}')

        parts = []
        if missing_ports:
            parts.append('Errors from other modules instantiating your optimized module:')
            for mod, ports in missing_ports.items():
                sorted_ports = sorted(ports)
                parts.append(f'  Missing ports in {mod}: {{{", ".join(sorted_ports)}}}')
                parts.append('  You MUST keep all original ports. Do not remove or rename any port.')

        if type_mismatch:
            parts.append('Port type mismatches:')
            parts.extend(type_mismatch)

        if other:
            parts.append('Other errors from surrounding modules:')
            parts.extend(other)

        return '\n'.join(parts)


# ---------------------------------------------------------------------------
# Yosys read_verilog elaboration parser
# ---------------------------------------------------------------------------


@dataclass
class YosysVerilogDiagnostic:
    """A single diagnostic from yosys read_verilog."""

    file: str
    line: int
    severity: str  # "ERROR", "Warning"
    message: str


@register_parser
class ParseYosysVerilogElabForLLM(ParseToolResultForLLM):
    """Parses yosys read_verilog (Verilog-2005 frontend) elaboration logs.

    Detects via "Executing Verilog-2005 frontend" or yosys ERROR patterns.
    """

    # pattern: path/file.sv:LINE: ERROR: message
    _DIAG_RE = re.compile(r'^(.+?):(\d+):\s+(ERROR|Warning):\s+(.+)$')
    # pattern: ERROR: message (no file context)
    _BARE_ERROR_RE = re.compile(r'^ERROR:\s+(.+)$')

    def __init__(self):
        super().__init__()
        self.diagnostics: List[YosysVerilogDiagnostic] = []

    @classmethod
    def detect(cls, text: str) -> bool:
        return 'Executing Verilog-2005 frontend' in text or 'verilog frontend filename' in text

    def parse(self) -> bool:
        self.diagnostics = []
        for line in self.raw_text.splitlines():
            m = self._DIAG_RE.match(line.strip())
            if m:
                filepath, line_no, severity, message = m.groups()
                self.diagnostics.append(
                    YosysVerilogDiagnostic(
                        file=os.path.basename(filepath),
                        line=int(line_no),
                        severity=severity.lower(),
                        message=message,
                    )
                )
                continue

            m2 = self._BARE_ERROR_RE.match(line.strip())
            if m2:
                self.diagnostics.append(
                    YosysVerilogDiagnostic(
                        file='',
                        line=0,
                        severity='error',
                        message=m2.group(1),
                    )
                )
        return True

    def categorize_errors(self) -> List[CategorizedError]:
        """Categorize yosys read_verilog diagnostics for FewShotMemory lookup."""
        result: List[CategorizedError] = []
        for d in self.diagnostics:
            if d.severity == 'warning':
                continue
            result.append(CategorizedError('syntax_error', f'{d.file}:{d.line}: {d.message}'))
        return result

    def format_for_llm(self, **kwargs) -> str:
        """Format yosys verilog diagnostics for LLM consumption.

        Keyword Args:
            target_module: Name of the module being optimized.
        """
        target_module = kwargs.get('target_module', '')

        if not self.diagnostics:
            return 'No diagnostics found in elaboration log.'

        target_files = set()
        if target_module:
            target_files = {f'{target_module}.sv', f'{target_module}.v'}

        parts = []
        for d in self.diagnostics:
            loc = f'{d.file}:{d.line}' if d.file else '(global)'
            prefix = ''
            if d.file and d.file not in target_files:
                prefix = '(other module) '
            parts.append(f'  {prefix}{loc}: {d.severity}: {d.message}')

        header = 'Yosys elaboration errors:'
        return header + '\n' + '\n'.join(parts)
