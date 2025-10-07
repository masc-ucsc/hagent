"""
FuzzyGrep strategy: Wraps existing Fuzzy_grep tool to search for identifiers.

This strategy extracts identifiers from the Verilog diff using Extract_verilog_diff_keywords,
then uses Fuzzy_grep to search for them in Chisel source files, maps matched lines
to enclosing modules, and computes confidence based on match quality.
"""

from typing import List, Dict
from collections import defaultdict
from .strategy_base import HintStrategy
from .models import DiffInfo, ModuleHint, ModuleSpan
from .span_index import SpanIndex

# Import existing tools
from hagent.tool.fuzzy_grep import Fuzzy_grep
from hagent.tool.extract_verilog_diff_keywords import Extract_verilog_diff_keywords


class FuzzyGrepStrategy(HintStrategy):
    """
    Strategy that uses existing Fuzzy_grep tool to search for identifiers.

    Workflow:
    1. Extract identifiers from Verilog diff using Extract_verilog_diff_keywords
    2. Use Fuzzy_grep to search in Chisel source files
    3. Map matched lines to enclosing modules
    4. Aggregate matches per module and compute confidence
    """

    def __init__(self, threshold: int = 70, min_matches: int = 1):
        """
        Initialize FuzzyGrepStrategy.

        Args:
            threshold: Fuzzy match threshold (0-100, default 70)
            min_matches: Minimum matches required for a module (default 1)
        """
        self.threshold = threshold
        self.min_matches = min_matches
        self.fuzzy_grep = Fuzzy_grep()
        self.fuzzy_grep.setup('chisel')  # Configure for Chisel/Scala

    @property
    def name(self) -> str:
        """Strategy identifier."""
        return 'fuzzy_grep'

    def generate_hints(self, diff_info: DiffInfo, span_index: SpanIndex, builder=None) -> List[ModuleHint]:
        """
        Generate hints by fuzzy-searching for identifiers.

        Args:
            diff_info: Information about the bug/diff
            span_index: Pre-built index of module spans
            builder: Builder instance for file I/O

        Returns:
            List of ModuleHint objects sorted by confidence (descending)
        """
        # Extract identifiers from diff using existing tool
        identifiers = Extract_verilog_diff_keywords.get_user_variables(diff_info.unified_diff)
        if not identifiers:
            return []

        # Get all Chisel modules
        all_modules = span_index.get_all_modules()
        if not all_modules:
            return []

        # Search for identifiers in each module
        module_matches = self._search_in_modules(identifiers, all_modules, builder)

        # Convert matches to hints
        hints = self._create_hints(module_matches)

        # Sort by confidence (descending)
        hints.sort(key=lambda h: h.confidence, reverse=True)

        return hints

    def _search_in_modules(self, identifiers: List[str], modules: List[ModuleSpan], builder) -> Dict[str, Dict]:
        """
        Search for identifiers in each module's source file.

        Args:
            identifiers: List of identifiers to search for
            modules: List of module spans
            builder: Builder instance for file I/O

        Returns:
            Dictionary mapping module_id to match evidence
        """
        module_matches = defaultdict(lambda: {'matches': [], 'span': None, 'match_count': 0})

        # Group modules by file for efficient searching
        file_to_modules = defaultdict(list)
        for module in modules:
            file_to_modules[module.file].append(module)

        # Search in each file
        for file_path, file_modules in file_to_modules.items():
            try:
                # Read file content
                content = self._read_file(file_path, builder)
                if not content:
                    continue

                # Search for identifiers in this file
                matches = self.fuzzy_grep.find_matches_in_text(content, identifiers, self.threshold)
                if not matches:
                    continue

                # Map matched lines to enclosing modules
                for line_num, line_content in matches:
                    # Find which module contains this line (line_num is 0-indexed from fuzzy_grep)
                    actual_line = line_num + 1  # Convert to 1-indexed
                    for module in file_modules:
                        if module.contains_line(actual_line):
                            module_id = module.module_id
                            module_matches[module_id]['matches'].append((actual_line, line_content))
                            module_matches[module_id]['span'] = module
                            module_matches[module_id]['match_count'] += 1
                            break  # One match per line

            except Exception as e:
                print(f'Warning: Failed to search in {file_path}: {e}')
                continue

        return dict(module_matches)

    def _read_file(self, file_path: str, builder) -> str:
        """
        Read file content using Builder API if available, else direct file I/O.

        Args:
            file_path: Path to file (may be docker: format)
            builder: Builder instance

        Returns:
            File content as string
        """
        if file_path.startswith('docker:'):
            # Parse docker path: docker:container:file_path
            parts = file_path.split(':', 2)
            if len(parts) != 3:
                raise ValueError(f'Invalid docker path format: {file_path}')
            actual_path = parts[2]

            if builder:
                return builder.filesystem.read_text(actual_path)
            else:
                raise RuntimeError('Builder required for docker: paths')
        else:
            # Local file
            with open(file_path, 'r', encoding='utf-8') as f:
                return f.read()

    def _create_hints(self, module_matches: Dict[str, Dict]) -> List[ModuleHint]:
        """
        Convert module matches into ModuleHint objects.

        Args:
            module_matches: Aggregated matches per module

        Returns:
            List of ModuleHint objects
        """
        hints = []

        for module_id, match_data in module_matches.items():
            match_count = match_data['match_count']
            span = match_data['span']

            if match_count < self.min_matches:
                continue

            # Compute match density: matches / module size
            match_density = min(1.0, match_count / span.line_count()) if span.line_count() > 0 else 0.0

            # Confidence is based on match density
            # Scale it: few matches = lower confidence, many matches = higher confidence
            confidence = min(1.0, match_density * 10.0)  # Scale up match_density

            hint = ModuleHint(
                module_id=module_id,
                span=span,
                confidence=confidence,
                source=self.name,
                evidence={
                    'match_count': match_count,
                    'match_density': match_density,
                    'matched_lines': [line_num for line_num, _ in match_data['matches'][:10]],  # Top 10 for brevity
                },
            )
            hints.append(hint)

        return hints
