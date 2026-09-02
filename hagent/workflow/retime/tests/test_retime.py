"""Tests for the retime orchestration layer.

The load-bearing ones are the HONESTY tests: an unattended loop must never record
a proof it did not get.  Each of these encodes a trap that was hit for real.
"""
import json
import tempfile
import time
from pathlib import Path

import pytest

from hagent.workflow.retime.durable import DurableRunner, DONE, LOST, NOT_STARTED, RUNNING
from hagent.workflow.retime.ledger import (
    Candidate, Ledger, rtl_sha, PROVEN, COUNTEREXAMPLE, NORMALIZER_GAP, TIMEOUT, TOOL_ERROR)
from hagent.workflow.retime.prover import classify, verdict, render


# ------------------------------------------------------------------ durable
@pytest.fixture
def runner(tmp_path):
    return DurableRunner(tmp_path / 'jobs')


def test_exit_code_is_reported(runner):
    runner.launch('ok', ['/bin/bash', '-c', 'exit 0'], cwd='/tmp')
    assert runner.wait('ok', poll_s=1, timeout_s=90).ok()
    runner.launch('bad', ['/bin/bash', '-c', 'exit 7'], cwd='/tmp')
    st = runner.wait('bad', poll_s=1, timeout_s=90)
    assert st.state == DONE and st.exit_code == 7 and not st.ok()


def test_unstarted_job_is_not_success(runner):
    """systemctl reports Result=success/ExecMainStatus=0 for a unit that never
    existed.  Trusting it would mark an unrun proof PROVEN."""
    assert runner.poll('never-ran').state == NOT_STARTED


def test_killed_job_is_lost_not_done(runner):
    """The single most important durability property: a job killed mid-flight
    must never surface as a clean exit 0."""
    runner.launch('k', ['/bin/bash', '-c', 'sleep 300'], cwd='/tmp')
    time.sleep(2)
    runner.cancel('k')
    time.sleep(2)
    st = runner.poll('k')
    assert st.state == LOST and st.exit_code is None


def test_launch_is_idempotent(runner):
    """A replayed checkpoint must not double-spend a 6-hour proof."""
    a = runner.launch('i', ['/bin/bash', '-c', 'sleep 10'], cwd='/tmp')
    b = runner.launch('i', ['/bin/bash', '-c', 'sleep 10'], cwd='/tmp')
    assert a.unit == b.unit and b.state == RUNNING
    runner.cancel('i')


def test_exclusive_slot_serializes(runner):
    runner.claim('x1', 'lean')
    runner.launch('x1', ['/bin/bash', '-c', 'sleep 10'], cwd='/tmp', exclusive='lean')
    blocked = runner.launch('x2', ['/bin/bash', '-c', 'true'], cwd='/tmp', exclusive='lean')
    assert blocked.state == NOT_STARTED and 'busy' in blocked.detail
    runner.cancel('x1')


# ------------------------------------------------------------------- ledger
def test_rtl_sha_ignores_cosmetics_not_semantics():
    a = 'module alu_a4 (input x); // c\n assign y = x;\nendmodule'
    b = 'module alu_zz (input x);\n\n  assign   y = x;\nendmodule  // other'
    assert rtl_sha(a) == rtl_sha(b)
    assert rtl_sha(a) != rtl_sha(a.replace('= x', '= ~x'))


def _led(tmp_path, rows):
    L = Ledger(tmp_path / 'l.jsonl')
    for i, (n, ps) in enumerate(rows):
        L.append(Candidate(block='b', cand=n, crit_ps=ps, proof=PROVEN,
                           control='FAILED_AS_REQUIRED', rtl_sha=rtl_sha(n), ts=i))
    return L


def test_plateau_fires_at_five(tmp_path):
    L = _led(tmp_path, [('base', 900.), ('a', 901.), ('b', 902.),
                        ('c', 903.), ('d', 904.), ('e', 905.)])
    assert L.should_stop('b')[0]


def test_improvement_resets_plateau(tmp_path):
    L = _led(tmp_path, [('base', 900.), ('a', 901.), ('b', 902.),
                        ('c', 903.), ('d', 904.), ('WIN', 700.), ('e', 701.)])
    assert not L.should_stop('b')[0] and L.plateau('b') == 1


def test_leaked_control_is_not_best(tmp_path):
    """A proof whose negative control also passed proves nothing."""
    L = Ledger(tmp_path / 'l.jsonl')
    L.append(Candidate(block='b', cand='base', crit_ps=900., rtl_sha='h0', ts=0))
    L.append(Candidate(block='b', cand='bad', crit_ps=100., proof=PROVEN,
                       control='LEAKED', rtl_sha='h1', ts=1))
    assert L.best('b').cand == 'base'


def test_ledger_resumes_from_disk(tmp_path):
    _led(tmp_path, [('base', 900.), ('a', 500.)])
    assert Ledger(tmp_path / 'l.jsonl').best('b').cand == 'a'


# ------------------------------------------------------------------- prover
def test_classify_distinguishes_gap_from_counterexample():
    """The distinction that cost three real runs to learn.  A normalizer gap is
    NOT a refutation; conflating them discards correct candidates."""
    gap = ('error: The prover found a potentially spurious counterexample:\n'
           '- It abstracted the following unsupported expressions as opaque variables:')
    cex = 'error: The prover found a counterexample, consider the following assignment:'
    assert classify(gap, 1) == NORMALIZER_GAP
    assert classify(cex, 1) == COUNTEREXAMPLE
    assert classify('wall=147.62 s rss=2703804 KB', 0) == PROVEN
    assert classify('error: (deterministic) timeout at `whnf`, maximum number of '
                    'heartbeats (400000) has been reached', 1) == TIMEOUT


def test_verdict_requires_control_to_fail():
    assert verdict(PROVEN, COUNTEREXAMPLE) == (PROVEN, 'FAILED_AS_REQUIRED')
    assert verdict(PROVEN, PROVEN) == (TOOL_ERROR, 'LEAKED')
    assert verdict(NORMALIZER_GAP, COUNTEREXAMPLE)[0] == NORMALIZER_GAP


# Includes a body, because the control picker counts how often each input is
# REFERENCED so it never builds a control out of dangling ports.
BASE_SRC = '''
structure cva6_alu_base_in where
  in_clk_i : BitVec 1
  in_imm_i : BitVec 64
  in_operand_a_i : BitVec 64
  in_operand_b_i : BitVec 64
  in_operation_i : BitVec 8
structure cva6_alu_base_out where
  out_branch_res_o : BitVec 1
  out_result_o : BitVec 64
def body := i.in_operand_a_i + i.in_operand_b_i + i.in_operand_a_i + i.in_operation_i
'''

# Same ports, but every 64-bit input is dangling -- no control is constructible.
DANGLING_SRC = BASE_SRC.replace(
    'def body := i.in_operand_a_i + i.in_operand_b_i + i.in_operand_a_i + i.in_operation_i',
    'def body := i.in_operation_i')


def test_control_never_built_from_dangling_ports():
    """The CVA6 ALU carries three dangling inputs, one of them 64-bit like the
    operands.  A control swapping unused ports passes trivially and would be
    reported as LEAKED, falsely condemning a correct candidate."""
    from hagent.workflow.retime.prover import pick_swap
    ins = [('in_clk_i', 1), ('in_imm_i', 64), ('in_operand_a_i', 64),
           ('in_operand_b_i', 64), ('in_operation_i', 8)]
    assert pick_swap(ins, BASE_SRC) == ('in_operand_a_i', 'in_operand_b_i')


def test_render_refuses_when_no_control_possible():
    """A proof we cannot check for vacuity must not be emitted at all."""
    with pytest.raises(ValueError, match='negative control'):
        render('cva6_alu', 'base', 'x', 0, DANGLING_SRC, DANGLING_SRC)


def test_render_k0_and_control_swaps_operands():
    proof, control = render('cva6_alu', 'base', 'a4', 0, BASE_SRC, BASE_SRC)
    assert 'bv_decide' in proof and 'out_result_o' in proof
    # the control must differ from the proof, or it tests nothing
    assert 'in_operand_a_i := i.in_operand_b_i' in control
    assert 'in_operand_a_i := i.in_operand_b_i' not in proof


def test_render_k1_control_asserts_k0_claim():
    proof, control = render('cva6_alu', 'base', 'p1', 1, BASE_SRC, BASE_SRC)
    assert 'flop_next' in proof and '_next' in proof
    assert 'MUST FAIL' in control and '_state' in control


def test_relative_root_is_resolved(tmp_path, monkeypatch):
    """systemd-run does not inherit cwd, so a relative root produced a unit that
    died instantly with `run.sh: No such file or directory` and no sentinel."""
    monkeypatch.chdir(tmp_path)
    r = DurableRunner('build/jobs')
    assert r.root.is_absolute()
    r.launch('rel', ['/bin/bash', '-c', 'exit 0'], cwd='/tmp')
    assert r.wait('rel', poll_s=1, timeout_s=90).ok()
