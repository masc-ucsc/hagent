"""
End-to-end integration test for the complete hint generation pipeline.

This test simulates the full workflow from diff input to candidate selection,
ensuring all components work together correctly.
"""

import tempfile
from pathlib import Path
import pytest

from hagent.step.hints.span_index import SpanIndex
from hagent.step.hints.models import DiffInfo
from hagent.step.hints.module_finder_strategy import ModuleFinder
from hagent.step.hints.source_locator import SourceLocator
from hagent.step.hints.fuzzy_grep_strategy import FuzzyGrepStrategy
from hagent.step.hints.unifier import HintUnifier
from hagent.step.hints.selector import CandidateSelector


class TestEndToEndIntegration:
    """End-to-end integration tests for the complete pipeline."""

    @pytest.fixture
    def fixture_dir(self):
        """Get path to test fixtures."""
        return Path(__file__).parent / 'fixtures'

    @pytest.fixture
    def span_index(self, fixture_dir):
        """Build span index from fixtures."""
        alu_file = str(fixture_dir / 'ALU.scala')
        control_file = str(fixture_dir / 'Control.scala')

        index = SpanIndex()
        index.build([alu_file, control_file])
        return index

    @pytest.fixture
    def strategies(self):
        """Create all three strategies."""
        return [
            ModuleFinder(min_confidence=0.3),
            SourceLocator(),
            FuzzyGrepStrategy(threshold=70),
        ]

    @pytest.fixture
    def unifier(self, span_index, strategies):
        """Create HintUnifier with all strategies."""
        return HintUnifier(span_index, strategies)

    @pytest.fixture
    def selector(self):
        """Create CandidateSelector with temp ledger."""
        with tempfile.TemporaryDirectory() as tmpdir:
            ledger_path = Path(tmpdir) / 'ledger.json'
            yield CandidateSelector(str(ledger_path))

    def test_complete_pipeline_alu_bug(self, unifier, selector):
        """Test complete pipeline with ALU bug scenario."""
        # Create realistic DiffInfo for ALU bug
        diff = """--- a/ALU.v
+++ b/ALU.v
@@ -15,7 +15,7 @@ module ALU(
   always_comb begin
     case (operation)
-      4'b0000: result = inputx + inputy;  // ADD
+      4'b0000: result = inputx - inputy;  // ADD (BUG: should be +)
       4'b0001: result = inputx - inputy;  // SUB
       4'b0010: result = inputx & inputy;  // AND
"""

        diff_info = DiffInfo(verilog_file='ALU.sv', verilog_module='ALU', unified_diff=diff)

        # Step 1: Run strategies and aggregate
        print('\n' + '=' * 60)
        print('STEP 1: Running strategies and aggregating hints')
        print('=' * 60)
        candidates = unifier.run_and_aggregate(diff_info, builder=None)

        # Verify candidates generated
        assert len(candidates) > 0, 'Should generate at least one candidate'
        print(f'\n✅ Generated {len(candidates)} candidates')

        # Verify ALU is in candidates (should be high confidence)
        alu_candidates = [c for c in candidates if 'ALU' in c.span.name]
        assert len(alu_candidates) > 0, 'ALU should be in candidates'
        print(f'✅ Found ALU candidate(s): {[c.span.name for c in alu_candidates]}')

        # Step 2: Select a candidate
        print('\n' + '=' * 60)
        print('STEP 2: Selecting candidate for iteration 1')
        print('=' * 60)
        selected = selector.select(candidates, 'test_commit_1', iteration=1)

        assert selected is not None, 'Should select a candidate'
        print(f'\n✅ Selected: {selected.span.name} (score={selected.fused_score:.2f})')
        print(f'   Sources: {selected.scores}')
        print(f'   Tier: {selected.get_tier()}')

        # Step 3: Record outcome
        print('\n' + '=' * 60)
        print('STEP 3: Recording outcome')
        print('=' * 60)
        selector.record_outcome(
            selected.module_id,
            outcome='lec_fail',
            iteration=1,
            commit_hash='test_commit_1',
            score=selected.fused_score,
            sources=selected.scores,
        )

        summary = selector.get_ledger_summary()
        print(f'\n✅ Ledger updated: {summary}')

        # Step 4: Select again (should pick different candidate)
        print('\n' + '=' * 60)
        print('STEP 4: Selecting candidate for iteration 2')
        print('=' * 60)
        selected2 = selector.select(candidates, 'test_commit_1', iteration=2)

        if selected2:
            print(f'\n✅ Selected different candidate: {selected2.span.name}')
            assert selected2.module_id != selected.module_id, 'Should select different candidate'
        else:
            print('\nℹ️  No more untried candidates (expected if only one candidate)')

        print('\n' + '=' * 60)
        print('END-TO-END TEST PASSED ✅')
        print('=' * 60)

    def test_pipeline_control_bug(self, unifier, selector):
        """Test pipeline with Control module bug."""
        diff = """--- a/Control.v
+++ b/Control.v
@@ -20,7 +20,7 @@ module Control(
   // R-type instructions
-  if (opcode == 7'b0110011) begin
+  if (opcode == 7'b0110111) begin  // BUG: wrong opcode
     regwrite = 1'b1;
   end
"""

        diff_info = DiffInfo(verilog_file='Control.sv', verilog_module='Control', unified_diff=diff)

        print('\n' + '=' * 60)
        print('Testing Control module bug')
        print('=' * 60)

        candidates = unifier.run_and_aggregate(diff_info, builder=None)

        assert len(candidates) > 0
        # Should find Control module
        control_candidates = [c for c in candidates if 'Control' in c.span.name]
        assert len(control_candidates) > 0, 'Control should be in candidates'

        print(f'\n✅ Found Control candidate(s): {[c.span.name for c in control_candidates]}')

    def test_pipeline_no_matches(self, unifier):
        """Test pipeline with unrelated diff (should handle gracefully)."""
        diff = """--- a/Nonexistent.v
+++ b/Nonexistent.v
@@ -1,1 +1,1 @@
-  some_signal = value1;
+  some_signal = value2;
"""

        diff_info = DiffInfo(verilog_file='Nonexistent.sv', verilog_module='XyZZy123NoMatch', unified_diff=diff)

        print('\n' + '=' * 60)
        print('Testing with no matches (should handle gracefully)')
        print('=' * 60)

        candidates = unifier.run_and_aggregate(diff_info, builder=None)

        # Should complete without error
        print(f'\n✅ Handled gracefully: {len(candidates)} candidates')

    def test_multiple_iterations(self, unifier, selector):
        """Test multiple iteration workflow."""
        diff = """--- a/ALU.v
+++ b/ALU.v
@@ -15,1 +15,1 @@
-      result = inputx + inputy;
+      result = inputx - inputy;
"""

        diff_info = DiffInfo(verilog_file='ALU.sv', verilog_module='ALU', unified_diff=diff)

        print('\n' + '=' * 60)
        print('Testing multiple iteration workflow')
        print('=' * 60)

        # Get candidates
        candidates = unifier.run_and_aggregate(diff_info, builder=None)
        assert len(candidates) > 0

        # Iterate until exhausted or max iterations
        max_iterations = 5
        for i in range(1, max_iterations + 1):
            print(f'\n--- Iteration {i} ---')
            selected = selector.select(candidates, 'test_commit_multi', iteration=i)

            if selected is None:
                print(f'✅ Exhausted all candidates after {i-1} iterations')
                break

            print(f'Selected: {selected.span.name} (score={selected.fused_score:.2f})')

            # Simulate failure
            selector.record_outcome(
                selected.module_id,
                outcome='lec_fail',
                iteration=i,
                commit_hash='test_commit_multi',
                score=selected.fused_score,
                sources=selected.scores,
            )

        summary = selector.get_ledger_summary()
        print(f'\n✅ Final summary: {summary}')
        assert summary['tried'] > 0

    def test_commit_change_resets_tried(self, unifier, selector):
        """Test that commit change resets tried status."""
        diff = """--- a/ALU.v
+++ b/ALU.v
@@ -15,1 +15,1 @@
-      result = inputx + inputy;
+      result = inputx - inputy;
"""

        diff_info = DiffInfo(verilog_file='ALU.sv', verilog_module='ALU', unified_diff=diff)

        print('\n' + '=' * 60)
        print('Testing commit change behavior')
        print('=' * 60)

        candidates = unifier.run_and_aggregate(diff_info, builder=None)

        # Select and mark tried at commit1
        selected1 = selector.select(candidates, 'commit_v1', iteration=1)
        assert selected1 is not None
        selector.record_outcome(
            selected1.module_id,
            outcome='lec_fail',
            iteration=1,
            commit_hash='commit_v1',
            score=selected1.fused_score,
            sources=selected1.scores,
        )

        # Try selecting again at commit1 - should get different candidate or None
        selected2 = selector.select(candidates, 'commit_v1', iteration=2)
        print(f'\n✅ At commit1: {"Different candidate selected" if selected2 else "All candidates tried"}')

        # Now at commit2 - should be able to select again (code changed)
        selected3 = selector.select(candidates, 'commit_v2', iteration=3)
        assert selected3 is not None, 'Should allow retrying at new commit'
        print(f'✅ At commit2: Can retry - selected {selected3.span.name}')


def test_import_all_components():
    """Smoke test to ensure all components can be imported."""

    print('\n✅ All components imported successfully')
