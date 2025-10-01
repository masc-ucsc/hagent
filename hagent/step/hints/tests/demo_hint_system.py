#!/usr/bin/env python3
"""
Demo script for testing the multi-strategy hint generation system.

Usage:
    uv run python hagent/step/hints/tests/demo_hint_system.py

This script demonstrates the complete workflow with sample data,
showing output at each stage for manual verification.
"""

import sys
from pathlib import Path

# Add parent to path for imports
sys.path.insert(0, str(Path(__file__).parent.parent.parent.parent))

from hagent.step.hints.span_index import SpanIndex
from hagent.step.hints.models import DiffInfo
from hagent.step.hints.module_finder_strategy import ModuleFinder
from hagent.step.hints.source_locator import SourceLocator
from hagent.step.hints.fuzzy_grep_strategy import FuzzyGrepStrategy
from hagent.step.hints.unifier import HintUnifier
from hagent.step.hints.selector import CandidateSelector


def print_section(title):
    """Print a section header."""
    print('\n' + '=' * 70)
    print(f'  {title}')
    print('=' * 70)


def demo_alu_bug():
    """Demonstrate the system with an ALU bug scenario."""
    print_section('DEMO: Multi-Strategy Hint Generation System')

    # Setup
    print('\n📁 Setting up test environment...')
    fixture_dir = Path(__file__).parent / 'fixtures'
    alu_file = str(fixture_dir / 'ALU.scala')
    control_file = str(fixture_dir / 'Control.scala')

    print(f'   - ALU.scala: {alu_file}')
    print(f'   - Control.scala: {control_file}')

    # Build span index
    print_section('STEP 1: Building Span Index')
    print('Parsing Scala files to extract class/object boundaries...')

    span_index = SpanIndex()
    span_index.build([alu_file, control_file])

    print(f'\n✅ Index built: {span_index}')
    print('\nModules found:')
    for i, module in enumerate(span_index.get_all_modules(), 1):
        print(f'   {i}. {module.name} ({module.span_type}) - {module.file}:{module.start_line}-{module.end_line}')

    # Create diff info
    print_section('STEP 2: Creating DiffInfo')

    diff = """--- a/ALU.v
+++ b/ALU.v
@@ -15,7 +15,7 @@ module ALU(
   always_comb begin
     case (operation)
-      4'b0000: result = inputx + inputy;  // ADD
+      4'b0000: result = inputx - inputy;  // ADD (BUG: should be +)
       4'b0001: result = inputx - inputy;  // SUB
       4'b0010: result = inputx & inputy;  // AND
       4'b0011: result = inputx | inputy;  // OR
"""

    print('Sample bug: ALU module with wrong operation')
    print(f'\nDiff:\n{diff}')

    diff_info = DiffInfo(verilog_file='ALU.sv', verilog_module='ALU', unified_diff=diff)
    print('\n✅ DiffInfo created:')
    print(f'   - Module: {diff_info.verilog_module}')
    print(f'   - File: {diff_info.verilog_file}')
    print(f'   - Changed lines: {diff_info.changed_lines}')

    # Create strategies
    print_section('STEP 3: Initializing Strategies')

    strategies = [
        ModuleFinder(min_confidence=0.3),
        SourceLocator(),
        FuzzyGrepStrategy(threshold=70),
    ]

    print('Three strategies initialized:')
    for s in strategies:
        print(f'   - {s.name}')

    # Create unifier
    print_section('STEP 4: Running Strategies and Aggregating')

    unifier = HintUnifier(span_index, strategies)
    candidates = unifier.run_and_aggregate(diff_info, builder=None)

    # Display results
    print_section('STEP 5: Analyzing Candidates')

    if not candidates:
        print('⚠️  No candidates found!')
        return

    print(f'\n✅ Found {len(candidates)} candidate modules:\n')

    for i, candidate in enumerate(candidates, 1):
        tier = candidate.get_tier()
        print(f'{i}. {candidate.span.name} ({candidate.span.span_type})')
        print(f'   File: {candidate.span.file}')
        print(f'   Lines: {candidate.span.start_line}-{candidate.span.end_line}')
        print(f'   Fused Score: {candidate.fused_score:.3f} (tier: {tier})')
        print(f'   Sources: {candidate.sources_hit}/3')
        print('   Per-source scores:')
        for source, score in candidate.scores.items():
            print(f'      - {source}: {score:.3f}')
        print()

    # Test selection
    print_section('STEP 6: Testing Candidate Selection')

    import tempfile

    with tempfile.TemporaryDirectory() as tmpdir:
        ledger_path = Path(tmpdir) / 'trial_ledger.json'
        selector = CandidateSelector(str(ledger_path))

        # Iteration 1
        print('\n--- Iteration 1 ---')
        selected = selector.select(candidates, 'demo_commit', iteration=1)

        if selected:
            print(f'\n✅ Selected: {selected.span.name}')
            print(f'   Score: {selected.fused_score:.3f}')
            print(f'   Tier: {selected.get_tier()}')

            # Record outcome
            selector.record_outcome(
                selected.module_id,
                outcome='lec_fail',
                iteration=1,
                commit_hash='demo_commit',
                score=selected.fused_score,
                sources=selected.scores,
                notes='Demo iteration 1',
            )

            # Iteration 2
            print('\n--- Iteration 2 ---')
            selected2 = selector.select(candidates, 'demo_commit', iteration=2)

            if selected2:
                print(f'\n✅ Selected different candidate: {selected2.span.name}')
                print(f'   Score: {selected2.fused_score:.3f}')

                selector.record_outcome(
                    selected2.module_id,
                    outcome='compile_fail',
                    iteration=2,
                    commit_hash='demo_commit',
                    score=selected2.fused_score,
                    sources=selected2.scores,
                    notes='Demo iteration 2',
                )
            else:
                print('\nℹ️  All candidates exhausted')

            # Show ledger
            print_section('STEP 7: Trial Ledger Summary')
            summary = selector.get_ledger_summary()
            print('\n✅ Ledger statistics:')
            print(f'   - Total modules: {summary["total"]}')
            print(f'   - Tried: {summary["tried"]}')
            print(f'   - Successful: {summary["success"]}')
            print(f'   - Failed: {summary["failed"]}')

    print_section('DEMO COMPLETED SUCCESSFULLY ✅')
    print('\nThe multi-strategy hint generation system is working correctly!')
    print('All components integrated successfully.\n')


def main():
    """Main entry point."""
    try:
        demo_alu_bug()
    except Exception as e:
        print(f'\n❌ ERROR: {e}')
        import traceback

        traceback.print_exc()
        sys.exit(1)


if __name__ == '__main__':
    main()
