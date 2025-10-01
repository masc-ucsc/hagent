"""
Data structures for multi-strategy hint generation.

This module defines the core data models used throughout the hint generation
pipeline, including module spans, hints, candidates, and trial records.
"""

from dataclasses import dataclass, field
from typing import Dict, Any, List, Set


@dataclass
class ModuleSpan:
    """
    Represents a Scala/Chisel class or object span in a file.

    Attributes:
        file: Absolute path or docker:container:path format
        name: Class or object name
        start_line: Starting line number (1-indexed)
        end_line: Ending line number (1-indexed, inclusive)
        span_type: Either "class" or "object"
    """

    file: str
    name: str
    start_line: int
    end_line: int
    span_type: str  # "class" or "object"

    def __post_init__(self):
        """Validate span data."""
        if self.start_line < 1:
            raise ValueError(f'start_line must be >= 1, got {self.start_line}')
        if self.end_line < self.start_line:
            raise ValueError(f'end_line ({self.end_line}) < start_line ({self.start_line})')
        if self.span_type not in ('class', 'object'):
            raise ValueError(f"span_type must be 'class' or 'object', got {self.span_type}")

    @property
    def module_id(self) -> str:
        """Unique identifier for this module: file::name"""
        return f'{self.file}::{self.name}'

    def contains_line(self, line: int) -> bool:
        """Check if a line number falls within this span."""
        return self.start_line <= line <= self.end_line

    def line_count(self) -> int:
        """Number of lines in this span."""
        return self.end_line - self.start_line + 1


@dataclass
class ModuleHint:
    """
    Evidence from a single strategy about a candidate module.

    Attributes:
        module_id: Unique identifier (file::name)
        span: The module span this hint refers to
        confidence: Confidence score [0.0, 1.0]
        source: Strategy name ("module_finder", "source_locator", "fuzzy_grep")
        evidence: Strategy-specific metadata
    """

    module_id: str
    span: ModuleSpan
    confidence: float
    source: str
    evidence: Dict[str, Any] = field(default_factory=dict)

    def __post_init__(self):
        """Validate hint data."""
        if not 0.0 <= self.confidence <= 1.0:
            raise ValueError(f'confidence must be in [0.0, 1.0], got {self.confidence}')
        if self.source not in ('module_finder', 'source_locator', 'fuzzy_grep'):
            raise ValueError(f'Invalid source: {self.source}')


@dataclass
class ModuleCandidate:
    """
    Unified candidate module with evidence from multiple sources.

    Attributes:
        module_id: Unique identifier (file::name)
        span: The module span
        scores: Per-source confidence scores {"mf": 0.88, "sl": 0.95, "fg": 0.76}
        fused_score: Combined confidence [0.0, 1.0]
        sources_hit: Number of strategies that found this module (1-3)
        all_evidence: All ModuleHints contributing to this candidate
    """

    module_id: str
    span: ModuleSpan
    scores: Dict[str, float]
    fused_score: float
    sources_hit: int
    all_evidence: List[ModuleHint] = field(default_factory=list)

    def __post_init__(self):
        """Validate candidate data."""
        if not 0.0 <= self.fused_score <= 1.0:
            raise ValueError(f'fused_score must be in [0.0, 1.0], got {self.fused_score}')
        if not 1 <= self.sources_hit <= 3:
            raise ValueError(f'sources_hit must be in [1, 3], got {self.sources_hit}')

    def get_tier(self, tier_high: float = 0.95, tier_medium: float = 0.70, tier_low: float = 0.50) -> str:
        """
        Classify candidate into tier based on fused score.

        Args:
            tier_high: Threshold for high tier
            tier_medium: Threshold for medium tier
            tier_low: Threshold for low tier

        Returns:
            "high", "medium", "low", or "none"
        """
        if self.fused_score >= tier_high:
            return 'high'
        elif self.fused_score >= tier_medium:
            return 'medium'
        elif self.fused_score >= tier_low:
            return 'low'
        else:
            return 'none'


@dataclass
class TrialRecord:
    """
    Ledger entry tracking attempt history for a module candidate.

    Attributes:
        module_id: Dictionary with "file" and "name" keys
        score: Fused score at time of trial
        sources: Per-source scores {"mf": 0.88, "sl": 0.95, "fg": 0.76}
        tried: Whether this module has been attempted
        attempts: Number of attempts made
        iteration_last: Most recent iteration number
        outcome_last: Most recent outcome
        commit_hash: Git commit hash to detect code changes
        timestamps: ISO-formatted timestamps of each attempt
        notes: Optional human-readable notes
    """

    module_id: Dict[str, str]
    score: float
    sources: Dict[str, float]
    tried: bool
    attempts: int
    iteration_last: int
    outcome_last: str
    commit_hash: str
    timestamps: List[str] = field(default_factory=list)
    notes: str = ''

    def __post_init__(self):
        """Validate trial record."""
        valid_outcomes = ('success', 'compile_fail', 'lec_fail', 'rejected', 'none')
        if self.outcome_last not in valid_outcomes:
            raise ValueError(f'outcome_last must be one of {valid_outcomes}, got {self.outcome_last}')

    @property
    def module_key(self) -> str:
        """Unique key for this module: file::name"""
        return f"{self.module_id['file']}::{self.module_id['name']}"


@dataclass
class DiffInfo:
    """
    Input information about the bug/diff to analyze.

    Attributes:
        verilog_file: RTL file name (e.g., "ALU.sv")
        verilog_module: Module name extracted from file
        unified_diff: Verilog unified diff content
        changed_lines: Line numbers changed in RTL (for locality calculations)
        identifiers: Extracted identifiers from diff
    """

    verilog_file: str
    verilog_module: str
    unified_diff: str
    changed_lines: Set[int] = field(default_factory=set)
    identifiers: Dict[str, List[str]] = field(default_factory=dict)

    @classmethod
    def from_bug_info(cls, bug_info) -> 'DiffInfo':
        """
        Create DiffInfo from a BugInfo object.

        Args:
            bug_info: BugInfo instance from v2chisel_batch

        Returns:
            DiffInfo instance
        """
        # Extract changed lines from diff
        changed_lines = cls._extract_changed_lines(bug_info.unified_diff)

        # Extract identifiers (will be populated by strategies later if needed)
        identifiers = {}

        return cls(
            verilog_file=bug_info.file_name,
            verilog_module=bug_info.module_name or '',
            unified_diff=bug_info.unified_diff,
            changed_lines=changed_lines,
            identifiers=identifiers,
        )

    @staticmethod
    def _extract_changed_lines(unified_diff: str) -> Set[int]:
        """
        Extract line numbers of changed lines from unified diff.

        Parses @@ hunk headers to determine which lines were modified.

        Args:
            unified_diff: Unified diff content

        Returns:
            Set of line numbers (1-indexed)
        """
        import re

        changed_lines = set()
        current_line = 0

        for line in unified_diff.split('\n'):
            # Parse hunk header: @@ -old_start,old_count +new_start,new_count @@
            if line.startswith('@@'):
                match = re.match(r'@@\s+-\d+(?:,\d+)?\s+\+(\d+)(?:,(\d+))?\s+@@', line)
                if match:
                    new_start = int(match.group(1))
                    current_line = new_start
                continue

            # Track changed/added lines
            if line.startswith('+') and not line.startswith('+++'):
                changed_lines.add(current_line)
                current_line += 1
            elif line.startswith('-') and not line.startswith('---'):
                # Deleted lines don't increment new line counter
                pass
            elif line.startswith(' '):
                # Context line
                current_line += 1

        return changed_lines
