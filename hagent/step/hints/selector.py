"""
CandidateSelector: Selects module candidates using tier-based weighted random policy.

This module implements the selection strategy that chooses which module candidate
to try for a given iteration, using confidence tiers and weighted randomization.
"""

import random
from typing import List, Optional
from .models import ModuleCandidate
from .trial_ledger import TrialLedger


class CandidateSelector:
    """
    Selects module candidates using tier-based weighted random policy.

    Selection policy:
    1. Filter to untried candidates
    2. Classify into tiers (high ≥0.95, medium ≥0.70, low ≥0.50)
    3. Select from highest non-empty tier
    4. Use weighted random within tier (weights = fused_score + ε-noise)
    """

    TIER_HIGH = 0.95
    TIER_MEDIUM = 0.70
    TIER_LOW = 0.50

    def __init__(self, trial_ledger_path: str, epsilon_noise: float = 0.01):
        """
        Initialize CandidateSelector.

        Args:
            trial_ledger_path: Path to trial ledger JSON file
            epsilon_noise: Small noise for tie-breaking (default 0.01)
        """
        self.ledger = TrialLedger(trial_ledger_path)
        self.epsilon_noise = epsilon_noise

    def select(self, candidates: List[ModuleCandidate], commit_hash: str, iteration: int) -> Optional[ModuleCandidate]:
        """
        Select a candidate using tier-based weighted random policy.

        Args:
            candidates: List of module candidates
            commit_hash: Current git commit hash
            iteration: Current iteration number

        Returns:
            Selected candidate or None if all exhausted
        """
        if not candidates:
            return None

        # Filter to untried candidates
        untried = self.ledger.get_untried(candidates, commit_hash)

        if not untried:
            print('⚠️  All candidates have been tried')
            return None

        print(f'\n🎯 Selecting from {len(untried)} untried candidates (iteration {iteration})')

        # Classify into tiers
        high_tier = [c for c in untried if c.fused_score >= self.TIER_HIGH]
        medium_tier = [c for c in untried if self.TIER_MEDIUM <= c.fused_score < self.TIER_HIGH]
        low_tier = [c for c in untried if self.TIER_LOW <= c.fused_score < self.TIER_MEDIUM]

        print(f'   Tiers: high={len(high_tier)}, medium={len(medium_tier)}, low={len(low_tier)}')

        # Select from highest non-empty tier
        if high_tier:
            selected = self._weighted_random_select(high_tier, 'high')
        elif medium_tier:
            selected = self._weighted_random_select(medium_tier, 'medium')
        elif low_tier:
            selected = self._weighted_random_select(low_tier, 'low')
        else:
            print('⚠️  No candidates meet minimum threshold')
            return None

        if selected:
            sources_str = ', '.join(f'{k}={v:.2f}' for k, v in selected.scores.items())
            print(f'   Selected: {selected.span.name} (score={selected.fused_score:.2f}, {sources_str})')

        return selected

    def _weighted_random_select(self, candidates: List[ModuleCandidate], tier_name: str) -> Optional[ModuleCandidate]:
        """
        Weighted random selection within a tier.

        Args:
            candidates: List of candidates in the tier
            tier_name: Name of the tier (for logging)

        Returns:
            Selected candidate
        """
        if not candidates:
            return None

        if len(candidates) == 1:
            return candidates[0]

        # Compute weights: fused_score + epsilon_noise for tie-breaking
        weights = [c.fused_score + random.uniform(0, self.epsilon_noise) for c in candidates]

        # Weighted random choice
        selected = random.choices(candidates, weights=weights, k=1)[0]

        return selected

    def record_outcome(
        self,
        module_id: str,
        outcome: str,
        iteration: int,
        commit_hash: str,
        score: float,
        sources: dict,
        notes: str = '',
    ) -> None:
        """
        Record trial outcome to ledger.

        Args:
            module_id: Module identifier (file::name)
            outcome: Outcome string ("success", "compile_fail", "lec_fail", etc.)
            iteration: Iteration number
            commit_hash: Git commit hash
            score: Fused score
            sources: Per-source scores
            notes: Optional notes
        """
        self.ledger.mark_tried(module_id, outcome, iteration, commit_hash, score, sources, notes)

        # Print summary
        summary = self.ledger.get_summary()
        print(f"\n📊 Ledger summary: {summary['tried']}/{summary['total']} tried, {summary['success']} successful")

    def get_ledger_summary(self) -> dict:
        """
        Get summary of trial ledger.

        Returns:
            Dictionary with summary statistics
        """
        return self.ledger.get_summary()

    def __repr__(self) -> str:
        """String representation of selector."""
        return f'CandidateSelector(ledger={self.ledger})'
