"""
Unit tests for HintUnifier, CandidateSelector, and TrialLedger.

Tests cover:
- Hint aggregation and fusion scoring
- Tier-based candidate selection
- Trial ledger persistence and filtering
"""

import tempfile
from pathlib import Path
import pytest

from hagent.step.hints.span_index import SpanIndex
from hagent.step.hints.models import ModuleHint, ModuleSpan, ModuleCandidate
from hagent.step.hints.module_finder_strategy import ModuleFinder
from hagent.step.hints.source_locator import SourceLocator
from hagent.step.hints.fuzzy_grep_strategy import FuzzyGrepStrategy
from hagent.step.hints.unifier import HintUnifier
from hagent.step.hints.selector import CandidateSelector
from hagent.step.hints.trial_ledger import TrialLedger


class TestHintUnifier:
    """Test suite for HintUnifier."""

    @pytest.fixture
    def span_index(self):
        """Create span index with test fixtures."""
        fixture_dir = Path(__file__).parent / 'fixtures'
        alu_file = str(fixture_dir / 'ALU.scala')
        control_file = str(fixture_dir / 'Control.scala')

        index = SpanIndex()
        index.build([alu_file, control_file])
        return index

    @pytest.fixture
    def strategies(self):
        """Create list of strategies."""
        return [ModuleFinder(), SourceLocator(), FuzzyGrepStrategy()]

    @pytest.fixture
    def unifier(self, span_index, strategies):
        """Create HintUnifier."""
        return HintUnifier(span_index, strategies)

    def test_aggregate_empty_hints(self, unifier):
        """Test aggregating empty hint list."""
        candidates = unifier.aggregate_evidence([])
        assert candidates == []

    def test_aggregate_single_source(self, unifier, span_index):
        """Test aggregating hints from a single source."""
        # Create mock hints from module_finder only
        alu_span = span_index.get_modules_in_file(list(span_index.cache.keys())[0])[0]

        hints = [
            ModuleHint(
                module_id=alu_span.module_id,
                span=alu_span,
                confidence=0.9,
                source='module_finder',
                evidence={'test': 'data'},
            )
        ]

        candidates = unifier.aggregate_evidence(hints)

        assert len(candidates) == 1
        assert candidates[0].module_id == alu_span.module_id
        assert candidates[0].fused_score == 0.9  # max(0.9) + 0 * (1-1)
        assert candidates[0].sources_hit == 1

    def test_aggregate_multiple_sources(self, unifier, span_index):
        """Test fusion of hints from multiple sources."""
        alu_span = span_index.get_modules_in_file(list(span_index.cache.keys())[0])[0]

        hints = [
            ModuleHint(module_id=alu_span.module_id, span=alu_span, confidence=0.8, source='module_finder', evidence={}),
            ModuleHint(module_id=alu_span.module_id, span=alu_span, confidence=0.9, source='source_locator', evidence={}),
            ModuleHint(module_id=alu_span.module_id, span=alu_span, confidence=0.7, source='fuzzy_grep', evidence={}),
        ]

        candidates = unifier.aggregate_evidence(hints)

        assert len(candidates) == 1
        candidate = candidates[0]
        assert candidate.sources_hit == 3
        # fused_score = max(0.8, 0.9, 0.7) + 0.05 * (3 - 1) = 0.9 + 0.1 = 1.0
        assert candidate.fused_score == 1.0
        assert 'mf' in candidate.scores
        assert 'sl' in candidate.scores
        assert 'fg' in candidate.scores

    def test_fusion_bonus(self, unifier, span_index):
        """Test cross-source bonus calculation."""
        alu_span = span_index.get_modules_in_file(list(span_index.cache.keys())[0])[0]

        # Two sources
        hints_two = [
            ModuleHint(module_id=alu_span.module_id, span=alu_span, confidence=0.7, source='module_finder', evidence={}),
            ModuleHint(module_id=alu_span.module_id, span=alu_span, confidence=0.6, source='source_locator', evidence={}),
        ]

        candidates = unifier.aggregate_evidence(hints_two)
        # fused_score = max(0.7, 0.6) + 0.05 * (2 - 1) = 0.7 + 0.05 = 0.75
        assert candidates[0].fused_score == 0.75

    def test_candidates_sorted_by_score(self, unifier, span_index):
        """Test that candidates are sorted by fused_score."""
        # Get modules with unique names
        all_modules = span_index.get_all_modules()
        unique_modules = []
        seen_names = set()
        for m in all_modules:
            if m.name not in seen_names:
                unique_modules.append(m)
                seen_names.add(m.name)
            if len(unique_modules) == 3:
                break

        hints = [
            ModuleHint(
                module_id=unique_modules[0].module_id, span=unique_modules[0], confidence=0.6, source='module_finder', evidence={}
            ),
            ModuleHint(
                module_id=unique_modules[1].module_id, span=unique_modules[1], confidence=0.9, source='module_finder', evidence={}
            ),
            ModuleHint(
                module_id=unique_modules[2].module_id, span=unique_modules[2], confidence=0.7, source='module_finder', evidence={}
            ),
        ]

        candidates = unifier.aggregate_evidence(hints)

        assert len(candidates) == 3
        assert candidates[0].fused_score >= candidates[1].fused_score
        assert candidates[1].fused_score >= candidates[2].fused_score


class TestTrialLedger:
    """Test suite for TrialLedger."""

    @pytest.fixture
    def ledger_path(self):
        """Create temporary ledger path."""
        with tempfile.TemporaryDirectory() as tmpdir:
            yield Path(tmpdir) / 'trial_ledger.json'

    def test_create_empty_ledger(self, ledger_path):
        """Test creating an empty ledger."""
        ledger = TrialLedger(str(ledger_path))
        assert len(ledger) == 0
        assert ledger.get_summary()['total'] == 0

    def test_mark_tried(self, ledger_path):
        """Test marking a candidate as tried."""
        ledger = TrialLedger(str(ledger_path))

        module_id = 'test.scala::TestModule'
        ledger.mark_tried(module_id, 'success', 1, 'abc123', 0.95, {'mf': 0.9, 'sl': 0.95}, 'test note')

        assert len(ledger) == 1
        record = ledger.get_record(module_id)
        assert record is not None
        assert record.tried
        assert record.outcome_last == 'success'
        assert record.attempts == 1

    def test_persist_and_load(self, ledger_path):
        """Test persistence and loading."""
        # Create ledger and add record
        ledger1 = TrialLedger(str(ledger_path))
        module_id = 'test.scala::TestModule'
        ledger1.mark_tried(module_id, 'compile_fail', 2, 'def456', 0.8, {'mf': 0.8})

        # Load in new instance
        ledger2 = TrialLedger(str(ledger_path))
        assert len(ledger2) == 1
        record = ledger2.get_record(module_id)
        assert record.outcome_last == 'compile_fail'
        assert record.iteration_last == 2

    def test_get_untried_new_candidates(self, ledger_path):
        """Test filtering untried candidates."""
        ledger = TrialLedger(str(ledger_path))

        # Create mock candidates
        span1 = ModuleSpan(file='test.scala', name='Module1', start_line=1, end_line=10, span_type='class')
        span2 = ModuleSpan(file='test.scala', name='Module2', start_line=11, end_line=20, span_type='class')

        candidates = [
            ModuleCandidate(
                module_id=span1.module_id, span=span1, scores={'mf': 0.9}, fused_score=0.9, sources_hit=1, all_evidence=[]
            ),
            ModuleCandidate(
                module_id=span2.module_id, span=span2, scores={'mf': 0.8}, fused_score=0.8, sources_hit=1, all_evidence=[]
            ),
        ]

        # All should be untried
        untried = ledger.get_untried(candidates, 'abc123')
        assert len(untried) == 2

    def test_get_untried_after_trial(self, ledger_path):
        """Test filtering after marking one as tried."""
        ledger = TrialLedger(str(ledger_path))

        span1 = ModuleSpan(file='test.scala', name='Module1', start_line=1, end_line=10, span_type='class')
        span2 = ModuleSpan(file='test.scala', name='Module2', start_line=11, end_line=20, span_type='class')

        candidates = [
            ModuleCandidate(
                module_id=span1.module_id, span=span1, scores={'mf': 0.9}, fused_score=0.9, sources_hit=1, all_evidence=[]
            ),
            ModuleCandidate(
                module_id=span2.module_id, span=span2, scores={'mf': 0.8}, fused_score=0.8, sources_hit=1, all_evidence=[]
            ),
        ]

        # Mark first as tried
        ledger.mark_tried(span1.module_id, 'lec_fail', 1, 'abc123', 0.9, {'mf': 0.9})

        # Only second should be untried
        untried = ledger.get_untried(candidates, 'abc123')
        assert len(untried) == 1
        assert untried[0].module_id == span2.module_id

    def test_get_untried_commit_changed(self, ledger_path):
        """Test that commit change resets tried status."""
        ledger = TrialLedger(str(ledger_path))

        span = ModuleSpan(file='test.scala', name='Module1', start_line=1, end_line=10, span_type='class')
        candidates = [
            ModuleCandidate(
                module_id=span.module_id, span=span, scores={'mf': 0.9}, fused_score=0.9, sources_hit=1, all_evidence=[]
            )
        ]

        # Mark as tried at old commit
        ledger.mark_tried(span.module_id, 'lec_fail', 1, 'abc123', 0.9, {'mf': 0.9})

        # At new commit, should be untried
        untried = ledger.get_untried(candidates, 'def456')
        assert len(untried) == 1


class TestCandidateSelector:
    """Test suite for CandidateSelector."""

    @pytest.fixture
    def ledger_path(self):
        """Create temporary ledger path."""
        with tempfile.TemporaryDirectory() as tmpdir:
            yield Path(tmpdir) / 'trial_ledger.json'

    @pytest.fixture
    def selector(self, ledger_path):
        """Create CandidateSelector."""
        return CandidateSelector(str(ledger_path))

    def test_select_from_empty(self, selector):
        """Test selecting from empty list."""
        selected = selector.select([], 'abc123', 1)
        assert selected is None

    def test_select_high_tier(self, selector):
        """Test selection from high tier."""
        span = ModuleSpan(file='test.scala', name='HighScore', start_line=1, end_line=10, span_type='class')
        candidates = [
            ModuleCandidate(
                module_id=span.module_id, span=span, scores={'mf': 0.98}, fused_score=0.98, sources_hit=1, all_evidence=[]
            )
        ]

        selected = selector.select(candidates, 'abc123', 1)
        assert selected is not None
        assert selected.fused_score >= 0.95  # High tier

    def test_select_medium_tier(self, selector):
        """Test selection from medium tier when high tier empty."""
        span = ModuleSpan(file='test.scala', name='MediumScore', start_line=1, end_line=10, span_type='class')
        candidates = [
            ModuleCandidate(
                module_id=span.module_id, span=span, scores={'mf': 0.8}, fused_score=0.8, sources_hit=1, all_evidence=[]
            )
        ]

        selected = selector.select(candidates, 'abc123', 1)
        assert selected is not None
        assert 0.70 <= selected.fused_score < 0.95  # Medium tier

    def test_select_exhausts_candidates(self, selector):
        """Test that selector exhausts all candidates."""
        span = ModuleSpan(file='test.scala', name='Module', start_line=1, end_line=10, span_type='class')
        candidates = [
            ModuleCandidate(
                module_id=span.module_id, span=span, scores={'mf': 0.9}, fused_score=0.9, sources_hit=1, all_evidence=[]
            )
        ]

        # First selection succeeds
        selected = selector.select(candidates, 'abc123', 1)
        assert selected is not None

        # Mark as tried
        selector.record_outcome(selected.module_id, 'lec_fail', 1, 'abc123', 0.9, {'mf': 0.9})

        # Second selection should return None (all tried)
        selected2 = selector.select(candidates, 'abc123', 2)
        assert selected2 is None

    def test_record_outcome(self, selector):
        """Test recording outcome."""
        module_id = 'test.scala::TestModule'
        selector.record_outcome(module_id, 'success', 1, 'abc123', 0.95, {'mf': 0.95, 'sl': 0.9})

        summary = selector.get_ledger_summary()
        assert summary['total'] == 1
        assert summary['tried'] == 1
        assert summary['success'] == 1
