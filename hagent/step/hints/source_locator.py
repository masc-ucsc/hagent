"""
SourceLocator strategy: Maps RTL metadata breadcrumbs to Chisel modules.

This strategy parses RTL files for @[file:line:col] metadata comments,
maps each referenced line to its enclosing Chisel module, and computes
a confidence score based on breadcrumb density and locality to changed lines.
"""

import re
import math
from typing import List, Dict, Set, Tuple
from collections import defaultdict
from .strategy_base import HintStrategy
from .models import DiffInfo, ModuleHint
from .span_index import SpanIndex


class SourceLocator(HintStrategy):
    """
    Strategy that uses RTL metadata breadcrumbs to locate relevant Chisel modules.

    Workflow:
    1. Parse RTL file for @[file:line:col] metadata
    2. Map each line to its enclosing Chisel module via span_index
    3. Compute locality factor (distance to changed lines)
    4. Aggregate evidence per module and compute confidence
    """

    def __init__(
        self, breadcrumb_scale: float = 10.0, locality_decay: float = 100.0, locality_clamp: Tuple[float, float] = (0.5, 1.0)
    ):
        """
        Initialize SourceLocator strategy.

        Args:
            breadcrumb_scale: Scale factor for breadcrumb density (default 10.0)
            locality_decay: Decay rate for locality factor (default 100.0)
            locality_clamp: Min/max clamp for locality factor (default (0.5, 1.0))
        """
        self.breadcrumb_scale = breadcrumb_scale
        self.locality_decay = locality_decay
        self.locality_clamp = locality_clamp

        # Regex pattern for @[file:line:col] metadata
        self.metadata_pattern = re.compile(r'(?://|/\*)\s*@\[([^:]+):(\d+):(\d+)\]')

    @property
    def name(self) -> str:
        """Strategy identifier."""
        return 'source_locator'

    def generate_hints(self, diff_info: DiffInfo, span_index: SpanIndex, builder=None) -> List[ModuleHint]:
        """
        Generate hints by parsing RTL metadata breadcrumbs.

        Args:
            diff_info: Information about the bug/diff
            span_index: Pre-built index of module spans
            builder: Builder instance for file I/O

        Returns:
            List of ModuleHint objects sorted by confidence (descending)
        """
        if not builder:
            # SourceLocator requires builder to read RTL files
            return []

        # Parse RTL metadata to get file:line mappings
        file_line_mappings = self._parse_rtl_metadata(diff_info, builder)
        if not file_line_mappings:
            return []

        # Map lines to modules and aggregate evidence
        module_evidence = self._map_lines_to_modules(file_line_mappings, span_index, diff_info.changed_lines)

        # Convert evidence to ModuleHints
        hints = self._create_hints(module_evidence, span_index)

        # Sort by confidence (descending)
        hints.sort(key=lambda h: h.confidence, reverse=True)

        return hints

    def _parse_rtl_metadata(self, diff_info: DiffInfo, builder) -> Dict[str, List[int]]:
        """
        Parse RTL file for @[file:line:col] metadata comments.

        Args:
            diff_info: Information about the bug
            builder: Builder instance for file I/O

        Returns:
            Dictionary mapping Chisel file paths to lists of referenced line numbers
        """
        # Construct RTL file path
        rtl_path = f'/code/workspace/build/build_dbg/rtl/{diff_info.verilog_file}'

        try:
            # Read RTL content using builder
            rtl_content = builder.filesystem.read_text(rtl_path)
        except Exception as e:
            print(f'Warning: Failed to read RTL file {rtl_path}: {e}')
            return {}

        # Parse metadata comments
        file_mappings = defaultdict(list)
        for match in self.metadata_pattern.finditer(rtl_content):
            file_path = match.group(1)
            line_num = int(match.group(2))
            # col_num = int(match.group(3))  # Not used currently

            file_mappings[file_path].append(line_num)

        return dict(file_mappings)

    def _map_lines_to_modules(
        self, file_line_mappings: Dict[str, List[int]], span_index: SpanIndex, changed_lines: Set[int]
    ) -> Dict[str, Dict]:
        """
        Map referenced lines to their enclosing modules and aggregate evidence.

        Args:
            file_line_mappings: File → list of line numbers
            span_index: Index of module spans
            changed_lines: Set of changed line numbers in RTL (for locality)

        Returns:
            Dictionary mapping module_id to aggregated evidence
        """
        module_evidence = defaultdict(lambda: {'breadcrumbs': [], 'files': set(), 'span': None})

        for file_path, line_numbers in file_line_mappings.items():
            for line_num in line_numbers:
                # Find enclosing module
                module_span = span_index.get_enclosing_module(file_path, line_num)
                if module_span:
                    module_id = module_span.module_id
                    module_evidence[module_id]['breadcrumbs'].append(line_num)
                    module_evidence[module_id]['files'].add(file_path)
                    module_evidence[module_id]['span'] = module_span

        return dict(module_evidence)

    def _create_hints(self, module_evidence: Dict[str, Dict], span_index: SpanIndex) -> List[ModuleHint]:
        """
        Convert module evidence into ModuleHint objects.

        Args:
            module_evidence: Aggregated evidence per module
            span_index: Index of module spans (unused but kept for consistency)

        Returns:
            List of ModuleHint objects
        """
        hints = []

        for module_id, evidence in module_evidence.items():
            breadcrumb_count = len(evidence['breadcrumbs'])
            if breadcrumb_count == 0:
                continue

            # Compute breadcrumb density score
            # Formula: min(1.0, log1p(breadcrumb_count) / log1p(breadcrumb_scale))
            breadcrumb_score = min(1.0, math.log1p(breadcrumb_count) / math.log1p(self.breadcrumb_scale))

            # For now, locality_factor is 1.0 (we don't have RTL line numbers mapped to Chisel lines easily)
            # In a full implementation, we'd compute distance from changed RTL lines to metadata lines
            locality_factor = 1.0

            # Combined confidence
            confidence = breadcrumb_score * locality_factor

            hint = ModuleHint(
                module_id=module_id,
                span=evidence['span'],
                confidence=confidence,
                source=self.name,
                evidence={
                    'breadcrumb_count': breadcrumb_count,
                    'breadcrumb_score': breadcrumb_score,
                    'locality_factor': locality_factor,
                    'files': list(evidence['files']),
                },
            )
            hints.append(hint)

        return hints

    def _compute_locality_factor(self, breadcrumb_lines: List[int], changed_lines: Set[int]) -> float:
        """
        Compute locality factor based on distance to changed lines.

        Formula: 1 / (1 + mean_distance / locality_decay)
        Clamped to locality_clamp range.

        Args:
            breadcrumb_lines: List of line numbers from breadcrumbs
            changed_lines: Set of changed line numbers in RTL

        Returns:
            Locality factor in [locality_clamp[0], locality_clamp[1]]
        """
        if not breadcrumb_lines or not changed_lines:
            return 1.0

        # Compute minimum distance for each breadcrumb to any changed line
        distances = []
        for b_line in breadcrumb_lines:
            min_dist = min(abs(b_line - c_line) for c_line in changed_lines)
            distances.append(min_dist)

        # Mean distance
        mean_distance = sum(distances) / len(distances)

        # Apply decay formula
        locality_factor = 1.0 / (1.0 + mean_distance / self.locality_decay)

        # Clamp to range
        locality_factor = max(self.locality_clamp[0], min(self.locality_clamp[1], locality_factor))

        return locality_factor
