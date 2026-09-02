"""Integration: the components must agree with each other, not just work alone.

These use the REAL artifacts from the CVA6 ALU study, so they check the contract
between the emitted models, the prover's parsing, and the selector's view of
livehd -- the seams where a plausible-looking component pair silently disagrees.
"""
import os
from pathlib import Path

import pytest

from hagent.workflow.retime.graph import load_block
from hagent.workflow.retime.prover import render
from hagent.workflow.retime.selector import parse_coverage, select

BENCH = Path('/soe/czeng14/projects/retimed-benchmark/cva6/lean_pass/alu')
LIVEHD = Path('/soe/czeng14/projects/livehd-new')
BLOCKS = Path(__file__).parent.parent / 'blocks'

needs_bench = pytest.mark.skipif(not BENCH.is_dir(), reason='benchmark repo absent')
needs_livehd = pytest.mark.skipif(not LIVEHD.is_dir(), reason='livehd absent')


def test_block_descriptor_is_loadable_and_complete():
    blk = load_block(BLOCKS / 'cva6_alu.yaml')
    for k in ('block', 'top_prefix', 'bench_blk', 'common', 'sta_targets'):
        assert k in blk, f'descriptor missing {k}'
    # A single -D reports the target, not the design, so a sweep is mandatory.
    assert len(blk['sta_targets']) >= 2


@needs_bench
def test_prover_parses_the_real_emitted_model():
    """The prover builds its coercion and theorems from the emitted `structure`
    declarations.  If pass.lean's output shape drifts, this is where it shows."""
    src = (BENCH / 'work/base/lean/cva6_alu_base_Lgraph.lean').read_text()[:400000]
    proof, control = render('cva6_alu', 'base', 'a4', 0, src, src)
    # every real port must appear in the generated coercion
    for f in ('in_operand_a_i', 'in_operand_b_i', 'in_operation_i', 'in_clk_i'):
        assert f in proof, f'{f} missing from generated coercion'
    # every real output must get its own theorem
    for f in ('out_result_o', 'out_branch_res_o'):
        assert f'eq_{f}' in proof
    # and the control must actually differ, or it tests nothing
    assert control != proof
    assert 'in_operand_a_i := i.in_operand_b_i' in control


@needs_bench
def test_generated_proof_matches_handwritten_shape():
    """The hand-written Equiv_A4.lean is the ground truth this must reproduce."""
    hand = (BENCH / 'lean/Equiv_A4.lean').read_text()
    src = (BENCH / 'work/base/lean/cva6_alu_base_Lgraph.lean').read_text()[:400000]
    gen, _ = render('cva6_alu', 'base', 'a4', 0, src, src)
    for tactic in ('simp only', 'alu_norm', 'bv_decide'):
        assert tactic in hand and tactic in gen, f'{tactic} shape mismatch'
    assert 'import Normalize' in gen


@needs_livehd
def test_selector_reads_livehd_coverage():
    """The selector's eligibility list is livehd's own proven-blocks table."""
    md = (LIVEHD / 'pass/lean/CVA6_COVERAGE_PLAN.md').read_text()
    infos = parse_coverage(md)
    assert len(infos) >= 4, 'coverage table not parsed'
    names = {b.name for b in infos}
    assert any('alu' in n for n in names)
    # combinational + widest should outrank a narrow one: width is what the
    # transformations that actually worked (prefix adder/comparator) shorten.
    by = {b.name: b for b in infos}
    wide = max(infos, key=lambda b: b.max_width or 0)
    narrow = min((b for b in infos if b.max_width), key=lambda b: b.max_width)
    assert wide.score() > narrow.score()


@needs_livehd
def test_selector_picks_an_eligible_block():
    nxt, ranked = select(LIVEHD, BLOCKS, done=set())
    assert nxt is not None and nxt.proven


@needs_bench
def test_regimes_are_per_output_on_the_real_pipelined_model():
    """`p1` registers result_o but leaves branch_res_o combinational.  A single
    module-wide regime would assert something false about one of them."""
    from hagent.workflow.retime.regimes import output_regimes
    src = (BENCH / 'work/p1/lean/cva6_alu_p1_Lgraph.lean').read_text()
    reg = output_regimes(src, 'cva6_alu_p1')
    assert reg == {'out_branch_res_o': 0, 'out_result_o': 1}


@needs_bench
def test_regimes_flat_for_combinational_model():
    from hagent.workflow.retime.regimes import output_regimes
    src = (BENCH / 'work/a4/lean/cva6_alu_a4_Lgraph.lean').read_text()
    assert set(output_regimes(src, 'cva6_alu_a4').values()) == {0}


@needs_bench
def test_generated_pipelined_proof_matches_handwritten_regimes():
    """Ground truth is the hand-written Equiv_P1.lean: an equality for the
    combinational output, a refinement for the registered one."""
    import re
    b = (BENCH / 'work/base/lean/cva6_alu_base_Lgraph.lean').read_text()
    c = (BENCH / 'work/p1/lean/cva6_alu_p1_Lgraph.lean').read_text()
    proof, control = render('cva6_alu', 'base', 'p1', 1, b, c)
    names = re.findall(r'theorem (\w+)', proof)
    assert 'eq_out_branch_res_o' in names, 'branch output must be plain equality'
    assert 'refines_out_result_o' in names, 'result output must be a refinement'
    # the control must attack the registered output with the k=0 claim
    assert 'k0_out_result_o' in re.findall(r'theorem (\w+)', control)


@needs_bench
def test_truncated_source_would_break_regimes():
    """Regression: p1's _comb record sits ~9k lines into a 2.3 MB file, so a
    truncated read silently reverts to one module-wide regime."""
    from hagent.workflow.retime.regimes import output_regimes
    src = (BENCH / 'work/p1/lean/cva6_alu_p1_Lgraph.lean').read_text()
    assert output_regimes(src[:400000], 'cva6_alu_p1') == {}      # the trap
    assert output_regimes(src, 'cva6_alu_p1') != {}               # full text works
