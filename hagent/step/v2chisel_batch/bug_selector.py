#!/usr/bin/env python3
# hagent/step/v2chisel_batch/bug_selector.py
# See LICENSE file for details

"""
Helper module for selecting and filtering bugs in v2chisel_batch.

This module provides utilities for:
- Selecting bugs by index range (e.g., '1-10', '1,3,5', '1-5,8-10')
- Skipping bugs that already passed LEC in previous runs
- Combining multiple selection criteria
"""

from pathlib import Path
from typing import Dict, List, Set

from ruamel.yaml import YAML


class BugSelector:
    """
    Helper class for selecting and filtering bugs based on various criteria.

    Example usage:
        # Select bugs 1-10 only
        selector = BugSelector(all_bugs)
        selected = selector.select_by_range('1-10').get_bugs()

        # Skip bugs that passed LEC and select range 5-15
        selector = BugSelector(all_bugs)
        selected = selector.skip_successful('output.yaml').select_by_range('5-15').get_bugs()
    """

    def __init__(self, bugs: List[Dict]):
        """
        Initialize bug selector with list of bugs.

        Args:
            bugs: List of bug dictionaries from input YAML
        """
        self.all_bugs = bugs
        self.selected_bugs = list(bugs)  # Make a copy
        self.filters_applied = []

    def select_by_range(self, range_spec: str) -> 'BugSelector':
        """
        Select bugs by index range specification.

        Supports multiple formats:
        - Single: '5' (just bug #5)
        - Range: '1-10' (bugs 1 through 10)
        - List: '1,3,5' (bugs 1, 3, and 5)
        - Combined: '1-5,8-10,15' (bugs 1-5, 8-10, and 15)

        Args:
            range_spec: Range specification string (1-based indices)

        Returns:
            Self for chaining

        Example:
            selector.select_by_range('1-10,15,20-25')
        """
        if not range_spec or not range_spec.strip():
            return self

        indices = self._parse_range_spec(range_spec)

        # Get currently selected bug indices
        current_indices = set(self.get_selected_indices())

        # Intersect range with currently selected bugs
        selected_indices = indices & current_indices

        # Filter bugs by selected indices
        self.selected_bugs = [bug for i, bug in enumerate(self.all_bugs, start=1) if i in selected_indices]

        self.filters_applied.append(f'range={range_spec} ({len(self.selected_bugs)} bugs selected)')

        if len(self.selected_bugs) == 0:
            print(f'⚠️  [BugSelector] No bugs matched range specification: {range_spec}')
        else:
            print(f'✅ [BugSelector] Selected {len(self.selected_bugs)} bugs from range: {range_spec}')

        return self

    def skip_successful(self, output_file: str) -> 'BugSelector':
        """
        Skip bugs that already passed LEC in a previous run.

        Reads the output YAML file and excludes bugs where:
        - lec_success: true
        - lec_equivalent: true

        Args:
            output_file: Path to previous output YAML file

        Returns:
            Self for chaining

        Example:
            selector.skip_successful('previous_results.yaml')
        """
        if not output_file:
            return self

        output_path = Path(output_file)
        if not output_path.exists():
            print(f'⚠️  [BugSelector] Output file not found, cannot skip successful: {output_file}')
            print('    All bugs will be processed.')
            return self

        successful_indices = self._load_successful_bugs(output_file)

        if not successful_indices:
            print('ℹ️  [BugSelector] No successful bugs found in previous run, processing all bugs.')
            return self

        # Filter out successful bugs
        original_count = len(self.selected_bugs)
        self.selected_bugs = [bug for i, bug in enumerate(self.all_bugs, start=1) if i not in successful_indices]

        skipped_count = original_count - len(self.selected_bugs)
        self.filters_applied.append(f'skip-successful ({skipped_count} bugs skipped)')

        print(f'✅ [BugSelector] Skipped {skipped_count} successful bugs from: {output_file}')
        print(f'   Successful bugs: {sorted(successful_indices)}')
        print(f'   Remaining to process: {len(self.selected_bugs)} bugs')

        return self

    def get_bugs(self) -> List[Dict]:
        """
        Get the filtered bug list.

        Returns:
            List of selected bug dictionaries
        """
        return self.selected_bugs

    def get_selection_summary(self) -> str:
        """
        Get a summary of the selection.

        Returns:
            String summary of what was selected
        """
        if not self.filters_applied:
            return f'Selected all {len(self.all_bugs)} bugs (no filters applied)'

        filters_str = ' → '.join(self.filters_applied)
        return f'Selected {len(self.selected_bugs)} of {len(self.all_bugs)} bugs ({filters_str})'

    def get_selected_indices(self) -> List[int]:
        """
        Get the 1-based indices of selected bugs.

        Returns:
            List of 1-based bug indices
        """
        # Find indices of selected bugs in original list
        indices = []
        for selected_bug in self.selected_bugs:
            for i, original_bug in enumerate(self.all_bugs, start=1):
                if selected_bug is original_bug:
                    indices.append(i)
                    break
        return indices

    @staticmethod
    def _parse_range_spec(range_spec: str) -> Set[int]:
        """
        Parse range specification into set of indices.

        Supports:
        - Single: '5' → {5}
        - Range: '1-10' → {1, 2, 3, ..., 10}
        - List: '1,3,5' → {1, 3, 5}
        - Combined: '1-5,8-10,15' → {1, 2, 3, 4, 5, 8, 9, 10, 15}

        Args:
            range_spec: Range specification string

        Returns:
            Set of 1-based indices

        Raises:
            ValueError: If range spec is invalid
        """
        indices = set()

        # Split by comma to get segments
        segments = [s.strip() for s in range_spec.split(',')]

        for segment in segments:
            if not segment:
                continue

            if '-' in segment:
                # Range: '1-10'
                parts = segment.split('-')
                if len(parts) != 2:
                    raise ValueError(f'Invalid range format: {segment} (expected "start-end")')

                # Check for empty parts (e.g., "-5" or "5-")
                if not parts[0].strip() or not parts[1].strip():
                    raise ValueError(f'Invalid range format: {segment} (empty start or end)')

                try:
                    start = int(parts[0].strip())
                    end = int(parts[1].strip())
                except ValueError:
                    raise ValueError(f'Invalid range numbers: {segment} (expected integers)')

                if start < 1 or end < 1:
                    raise ValueError(f'Bug indices must be >= 1: {segment}')

                if start > end:
                    raise ValueError(f'Range start must be <= end: {segment}')

                # Add all indices in range
                indices.update(range(start, end + 1))
            else:
                # Single number: '5'
                try:
                    index = int(segment.strip())
                except ValueError:
                    raise ValueError(f'Invalid bug index: {segment} (expected integer)')

                if index < 1:
                    raise ValueError(f'Bug index must be >= 1: {segment}')

                indices.add(index)

        return indices

    @staticmethod
    def _load_successful_bugs(output_file: str) -> Set[int]:
        """
        Load bug indices that passed LEC from output file.

        Args:
            output_file: Path to output YAML file

        Returns:
            Set of 1-based bug indices that passed LEC
        """
        try:
            yaml = YAML()
            with open(output_file, 'r') as f:
                data = yaml.load(f)

            if not data:
                return set()

            # Look for bug results
            bug_results = data.get('v2chisel_batch_with_llm', {}).get('bug_results', [])

            if not bug_results:
                return set()

            # Find bugs where LEC passed
            successful = set()
            for result in bug_results:
                # Check both lec_success and lec_equivalent
                lec_success = result.get('lec_success', False)
                lec_equivalent = result.get('lec_equivalent', False)

                if lec_success and lec_equivalent:
                    # bug_index is 0-based in the results, convert to 1-based
                    bug_index = result.get('bug_index', -1)
                    if bug_index >= 0:
                        successful.add(bug_index + 1)  # Convert to 1-based

            return successful

        except Exception as e:
            print(f'⚠️  [BugSelector] Error loading output file: {e}')
            return set()


def parse_bug_range(range_spec: str) -> List[int]:
    """
    Convenience function to parse bug range specification.

    Args:
        range_spec: Range specification (e.g., '1-10', '1,3,5')

    Returns:
        Sorted list of 1-based bug indices

    Example:
        >>> parse_bug_range('1-5,8,10-12')
        [1, 2, 3, 4, 5, 8, 10, 11, 12]
    """
    indices = BugSelector._parse_range_spec(range_spec)
    return sorted(indices)


def load_successful_bugs(output_file: str) -> List[int]:
    """
    Convenience function to load successful bug indices.

    Args:
        output_file: Path to output YAML file

    Returns:
        Sorted list of 1-based bug indices that passed LEC

    Example:
        >>> load_successful_bugs('results.yaml')
        [1, 3, 5, 7]
    """
    indices = BugSelector._load_successful_bugs(output_file)
    return sorted(indices)
