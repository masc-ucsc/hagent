"""
HintUnifier: Aggregates hints from multiple strategies into ranked candidates.

This module runs multiple strategies in parallel, collects their hints,
aggregates evidence by module, and computes fused confidence scores.
"""

import concurrent.futures
from typing import List, Dict, Optional
from collections import defaultdict
from .strategy_base import HintStrategy
from .models import ModuleHint, ModuleCandidate, DiffInfo
from .span_index import SpanIndex


class HintUnifier:
    """
    Aggregates hints from multiple strategies into ranked candidates.

    This class orchestrates the parallel execution of hint strategies,
    collects their outputs, and fuses evidence into unified candidates.
    """

    def __init__(self, span_index: SpanIndex, strategies: List[HintStrategy], fusion_config: Optional[Dict] = None):
        """
        Initialize HintUnifier.

        Args:
            span_index: Pre-built index of module spans
            strategies: List of hint strategies to run
            fusion_config: Configuration for fusion scoring (optional)
        """
        self.span_index = span_index
        self.strategies = strategies
        self.fusion_config = fusion_config or self._default_fusion_config()

    @staticmethod
    def _default_fusion_config() -> Dict:
        """Default fusion configuration."""
        return {'cross_source_bonus': 0.05, 'max_score': 1.0}

    def run_strategies(self, diff_info: DiffInfo, builder=None) -> List[ModuleHint]:
        """
        Run all strategies in parallel and collect hints.

        Args:
            diff_info: Information about the bug/diff
            builder: Builder instance for file I/O

        Returns:
            List of all ModuleHint objects from all strategies
        """
        all_hints = []

        # Run strategies in parallel using ThreadPoolExecutor
        with concurrent.futures.ThreadPoolExecutor(max_workers=len(self.strategies)) as executor:
            # Submit all strategy tasks
            future_to_strategy = {
                executor.submit(strategy.generate_hints, diff_info, self.span_index, builder): strategy
                for strategy in self.strategies
            }

            # Collect results as they complete
            for future in concurrent.futures.as_completed(future_to_strategy):
                strategy = future_to_strategy[future]
                try:
                    hints = future.result()
                    all_hints.extend(hints)
                    if hints:
                        print(f'✅ {strategy.name}: found {len(hints)} hints')
                    else:
                        print(f'ℹ️  {strategy.name}: no hints found')
                except Exception as e:
                    print(f'❌ {strategy.name} failed: {e}')
                    continue

        return all_hints

    def aggregate_evidence(self, hints: List[ModuleHint]) -> List[ModuleCandidate]:
        """
        Group hints by module_id and compute fused scores.

        Fusion formula:
            fused_score = min(max_score, max(scores) + cross_source_bonus * (sources_hit - 1))

        Args:
            hints: List of ModuleHint objects from all strategies

        Returns:
            List of ModuleCandidate objects sorted by fused_score (descending)
        """
        if not hints:
            return []

        # Group hints by module_id
        module_evidence = defaultdict(list)
        for hint in hints:
            module_evidence[hint.module_id].append(hint)

        # Create ModuleCandidate for each module
        candidates = []
        for module_id, hint_list in module_evidence.items():
            # Extract per-source scores
            scores = {}
            source_map = {'module_finder': 'mf', 'source_locator': 'sl', 'fuzzy_grep': 'fg'}

            for hint in hint_list:
                source_key = source_map.get(hint.source, hint.source)
                scores[source_key] = hint.confidence

            # Compute fused score
            sources_hit = len(scores)
            max_score = max(scores.values()) if scores else 0.0
            cross_source_bonus = self.fusion_config['cross_source_bonus']
            fused_score = min(self.fusion_config['max_score'], max_score + cross_source_bonus * (sources_hit - 1))

            # Use the span from the first hint (all should have same span)
            span = hint_list[0].span

            candidate = ModuleCandidate(
                module_id=module_id,
                span=span,
                scores=scores,
                fused_score=fused_score,
                sources_hit=sources_hit,
                all_evidence=hint_list,
            )
            candidates.append(candidate)

        # Sort by fused_score (descending)
        candidates.sort(key=lambda c: c.fused_score, reverse=True)

        return candidates

    def run_and_aggregate(self, diff_info: DiffInfo, builder=None) -> List[ModuleCandidate]:
        """
        Convenience method: run strategies + aggregate in one call.

        Args:
            diff_info: Information about the bug/diff
            builder: Builder instance for file I/O

        Returns:
            List of ModuleCandidate objects sorted by fused_score
        """
        print('\n🔍 Running hint generation strategies...')
        hints = self.run_strategies(diff_info, builder)

        if not hints:
            print('⚠️  No hints found from any strategy')
            return []

        print(f'\n📊 Aggregating {len(hints)} hints...')
        candidates = self.aggregate_evidence(hints)

        print(f'\n✅ Generated {len(candidates)} module candidates')
        for i, candidate in enumerate(candidates[:5], 1):  # Show top 5
            tier = candidate.get_tier()
            sources_str = ', '.join(f'{k}={v:.2f}' for k, v in candidate.scores.items())
            print(f'  {i}. {candidate.span.name} (fused={candidate.fused_score:.2f}, tier={tier}, {sources_str})')

        return candidates
