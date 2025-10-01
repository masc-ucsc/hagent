#!/usr/bin/env python3
"""
HintsGeneratorV2 - New multi-strategy hint generation system.

This is the V2 implementation using the new unified hint generation pipeline
with ModuleFinder, SourceLocator, and FuzzyGrep strategies.

Maintains the same interface as the original HintsGenerator for drop-in replacement.
"""

from typing import List, Dict, Any
from pathlib import Path

# Import new hint generation components
import sys

sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from hagent.step.hints.span_index import SpanIndex
from hagent.step.hints.models import DiffInfo, ModuleCandidate
from hagent.step.hints.module_finder_strategy import ModuleFinder
from hagent.step.hints.source_locator import SourceLocator
from hagent.step.hints.fuzzy_grep_strategy import FuzzyGrepStrategy
from hagent.step.hints.unifier import HintUnifier


class HintsGeneratorV2:
    """
    V2 Hints Generator using multi-strategy pipeline.

    This class provides the same interface as the original HintsGenerator
    but uses the new multi-strategy system internally.
    """

    def __init__(self, module_finder=None, builder=None, debug: bool = True):
        """
        Initialize HintsGeneratorV2.

        Args:
            module_finder: Legacy parameter, ignored in V2 (strategies are built-in)
            builder: Builder instance for Docker operations
            debug: Enable debug output
        """
        self.builder = builder
        self.debug = debug

        # Initialize strategies
        self.strategies = [
            ModuleFinder(min_confidence=0.3),
            SourceLocator(),
            FuzzyGrepStrategy(threshold=70),
        ]

        # SpanIndex will be built per request (cached if possible)
        self.span_index = None
        self.cached_files = None  # Track files used to build index

    def find_hints(self, bug_info, all_files: List[str], docker_container: str) -> Dict[str, Any]:
        """
        Find hints for a specific bug using multi-strategy pipeline.

        Args:
            bug_info: BugInfo object containing bug details
            all_files: List of all available Chisel files (local + docker)
            docker_container: Docker container name for file access

        Returns:
            Dict with 'hints', 'source', 'success', and 'hits' keys
            (compatible with original HintsGenerator interface)
        """
        try:
            if self.debug:
                print('🔍 [HintsGeneratorV2] Starting multi-strategy hint generation...')

            # Step 1: Build or reuse SpanIndex
            if self._should_rebuild_index(all_files):
                if self.debug:
                    print(f'   📚 Building SpanIndex from {len(all_files)} files...')
                self.span_index = SpanIndex(builder=self.builder, repo_path='.')
                self.span_index.build(all_files)
                self.cached_files = all_files.copy()
                if self.debug:
                    print(f'   ✅ SpanIndex built: {len(self.span_index)} modules indexed')
            else:
                if self.debug:
                    print(f'   ♻️  Reusing cached SpanIndex: {len(self.span_index)} modules')

            # Step 2: Create DiffInfo from BugInfo
            diff_info = DiffInfo(
                verilog_file=bug_info.file_name,
                verilog_module=bug_info.module_name,
                unified_diff=bug_info.unified_diff,
            )

            if self.debug:
                print(f'   🎯 Target module: {diff_info.verilog_module}')

            # Step 3: Run multi-strategy pipeline
            unifier = HintUnifier(self.span_index, self.strategies)
            candidates = unifier.run_and_aggregate(diff_info, builder=self.builder)

            if self.debug:
                print(f'   📊 Found {len(candidates)} candidate modules')

            # Step 4: Convert candidates to old format
            if not candidates:
                if self.debug:
                    print('   ⚠️  No candidates found by any strategy')
                return {
                    'hints': f'// No hints found for {bug_info.module_name}',
                    'source': 'none',
                    'success': False,
                    'hits': [],
                }

            # Select top candidate
            top_candidate = candidates[0]

            if self.debug:
                print(f'   🏆 Top candidate: {top_candidate.span.name} (score: {top_candidate.fused_score:.3f})')

            # Step 5: Extract code hints
            hints = self._format_hints(top_candidate, candidates[:5], docker_container)

            # Step 6: Convert to compatible format
            # Create "hits" in old format for backwards compatibility
            hits = self._candidates_to_hits(candidates[:5])

            # Determine source (which strategy found it)
            source = self._determine_source(top_candidate)

            if self.debug:
                print(f'   ✅ Generated {len(hints)} chars of hints from {source}')

            return {
                'hints': hints,
                'source': source,
                'success': True,
                'hits': hits,
            }

        except Exception as e:
            if self.debug:
                print(f'   ❌ HintsGeneratorV2 failed: {e}')
                import traceback

                traceback.print_exc()
            return {
                'hints': f'// HintsGeneratorV2 error: {str(e)}',
                'source': 'error',
                'success': False,
                'hits': [],
            }

    def _should_rebuild_index(self, all_files: List[str]) -> bool:
        """Check if we need to rebuild the index."""
        if self.span_index is None:
            return True
        if self.cached_files is None:
            return True
        if set(all_files) != set(self.cached_files):
            return True
        return False

    def _format_hints(
        self, top_candidate: 'ModuleCandidate', all_candidates: List['ModuleCandidate'], docker_container: str
    ) -> str:
        """Format candidates into hint text."""
        hints_parts = []

        hints_parts.append(f'// Multi-strategy hint generation for {top_candidate.span.name}')
        hints_parts.append(f'// Top candidate score: {top_candidate.fused_score:.3f} (tier: {top_candidate.get_tier()})')
        hints_parts.append(f'// Strategies matched: {top_candidate.sources_hit}/3')
        hints_parts.append('')

        # Show top candidates
        for i, candidate in enumerate(all_candidates, 1):
            file_path = candidate.span.file
            # Strip docker prefix for display
            if file_path.startswith('docker:'):
                parts = file_path.split(':', 2)
                if len(parts) == 3:
                    file_path = parts[2]

            hints_parts.append(f'// ========== CANDIDATE {i}: {candidate.span.name} ==========')
            hints_parts.append(f'// File: {file_path}')
            hints_parts.append(f'// Lines: {candidate.span.start_line}-{candidate.span.end_line}')
            hints_parts.append(f'// Confidence: {candidate.fused_score:.3f}')
            hints_parts.append(f'// Matched by: {", ".join(self._get_strategy_names(candidate))}')
            hints_parts.append('')

            # Extract code content
            code = self._extract_code_from_candidate(candidate, docker_container)
            if code:
                hints_parts.append(code)
                hints_parts.append('')

        return '\n'.join(hints_parts)

    def _extract_code_from_candidate(self, candidate: 'ModuleCandidate', docker_container: str) -> str:
        """Extract code content from a candidate module."""
        try:
            file_path = candidate.span.file

            # Handle Docker vs local paths
            if file_path.startswith('docker:'):
                # Parse docker path: docker:container_name:file_path
                parts = file_path.split(':', 2)
                actual_file_path = parts[2]

                # Read from Docker container using Builder API
                if self.builder:
                    full_content = self.builder.filesystem.read_text(actual_file_path)
                    lines = full_content.split('\n')
                    # Extract specific lines (1-indexed)
                    start_idx = max(0, candidate.span.start_line - 1)
                    end_idx = min(len(lines), candidate.span.end_line)
                    selected_lines = lines[start_idx:end_idx]
                    return '\n'.join(selected_lines).strip()
            else:
                # Local file - read directly
                with open(file_path, 'r') as f:
                    lines = f.readlines()
                    # Extract specific lines (1-indexed)
                    start_idx = max(0, candidate.span.start_line - 1)
                    end_idx = min(len(lines), candidate.span.end_line)
                    selected_lines = lines[start_idx:end_idx]
                    return ''.join(selected_lines).strip()

        except Exception as e:
            if self.debug:
                print(f'     ⚠️  Failed to extract code: {e}')
            return f'// Failed to extract code: {e}'

    def _candidates_to_hits(self, candidates: List['ModuleCandidate']) -> List:
        """Convert ModuleCandidates to old-style hits format."""
        hits = []
        for candidate in candidates:
            # Create a simple object mimicking the old Hit structure
            hit = type(
                'Hit',
                (),
                {
                    'file_name': candidate.span.file,
                    'module_name': candidate.span.name,
                    'start_line': candidate.span.start_line,
                    'end_line': candidate.span.end_line,
                    'confidence': candidate.fused_score,
                },
            )()
            hits.append(hit)
        return hits

    def _determine_source(self, candidate: 'ModuleCandidate') -> str:
        """Determine which strategy found this candidate."""
        # Check which strategies contributed
        if 'mf' in candidate.scores and candidate.scores['mf'] > 0:
            return 'module_finder'
        elif 'sl' in candidate.scores and candidate.scores['sl'] > 0:
            return 'source_locator'
        elif 'fg' in candidate.scores and candidate.scores['fg'] > 0:
            return 'fuzzy_grep'
        else:
            return 'multi_strategy'

    def _get_strategy_names(self, candidate: 'ModuleCandidate') -> List[str]:
        """Get list of strategy names that matched this candidate."""
        names = []
        strategy_map = {'mf': 'ModuleFinder', 'sl': 'SourceLocator', 'fg': 'FuzzyGrep'}
        for key, name in strategy_map.items():
            if key in candidate.scores and candidate.scores[key] > 0:
                names.append(name)
        return names

    def cleanup_temp_files(self):
        """Cleanup method for compatibility with original interface."""
        # V2 doesn't use temp files (everything goes through Builder)
        pass
