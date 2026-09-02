"""The prover node: emit a Lean proof for a candidate, run it, classify honestly.

Nothing off-the-shelf does this.  Four responsibilities:

1. **Pick the regime from a structural fact, not a judgement.**  `pass.lean`
   reports `N nodes, M flops, sequential=yes|no`.  `0 flops` means the emitted
   model is `_comb : in -> out` with no state parameter at all, so a latency
   change is not merely unproven but INEXPRESSIBLE, and plain equality is the
   right claim.  Flops present => latency-k refinement.

2. **Generate the proof from the emitted structures**, not from a hardcoded field
   list, so a new block needs no new prover code.

3. **Generate the negative control in the same run.**  A tactic script that
   proves the goal AND its deliberately-wrong twin proves nothing.  For k=0 the
   control swaps two equal-width inputs; for k>=1 it asserts the k=0 claim, which
   must fail or the register rank did not actually shift latency.

4. **Classify five ways, because the failures are not interchangeable.**  The
   distinction that matters most:

       "The prover found a counterexample"                  -> COUNTEREXAMPLE
       "potentially spurious counterexample ... abstracted"  -> NORMALIZER_GAP

   The second is NOT a refutation.  It means `bv_decide` met an idiom
   `Normalize.lean` does not cover and replaced it with an opaque variable.
   During the ALU study three separate runs died this way (`bool_to_bv1`, the
   MuxN `if toNat = k` lowering, and signed compares emitted as `Int`
   arithmetic).  An unattended loop that reads those as refutations throws away
   good candidates and mislearns.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Optional

from hagent.workflow.retime.durable import DurableRunner
from hagent.workflow.retime.regimes import output_regimes
from hagent.workflow.retime.ledger import (
    PROVEN, COUNTEREXAMPLE, NORMALIZER_GAP, TIMEOUT, TOOL_ERROR)

_STRUCT = r'structure\s+{top}_{kind}\s+where\s*\n((?:\s+\w+\s*:\s*BitVec\s+\d+\s*\n)+)'


def _fields(src: str, top: str, kind: str) -> list[tuple[str, int]]:
    m = re.search(_STRUCT.format(top=re.escape(top), kind=kind), src)
    if not m:
        return []
    return [(f, int(w)) for f, w in
            re.findall(r'(\w+)\s*:\s*BitVec\s+(\d+)', m.group(1))]


def _coercion(name: str, src_top: str, dst_top: str,
              fields: list[tuple[str, int]], swap: Optional[tuple[str, str]] = None) -> str:
    lines = []
    for f, _ in fields:
        rhs = f
        if swap and f == swap[0]:
            rhs = swap[1]
        elif swap and f == swap[1]:
            rhs = swap[0]
        lines.append(f'    {f} := i.{rhs}')
    body = '\n'.join(lines)
    return (f'@[reducible] def {name} (i : {src_top}_in) : {dst_top}_in :=\n'
            f'  {{\n{body} }}\n')


def pick_swap(ins: list[tuple[str, int]], model_src: str) -> Optional[tuple[str, str]]:
    """Choose two equal-width inputs to swap for the negative control, using ONLY
    inputs the model actually reads.

    This is not fussiness.  The CVA6 ALU's port list carries three dangling
    inputs -- `in_imm_i`, `in_trans_id_i`, `in_clk_i` all have ZERO references in
    the emitted model -- and `in_imm_i` is 64 bits, the same width as the two
    operands.  A naive "first equal-width pair" swaps `imm` with `operand_a`, and
    a pair of DANGLING inputs would produce a control that passes trivially,
    which the verdict logic would then report as LEAKED -- falsely condemning a
    correct candidate.  So rank by actual use and require both to be live."""
    used = {f: model_src.count(f'i.{f}') for f, _ in ins}
    bywidth: dict[int, list[str]] = {}
    for f, w in ins:
        if used.get(f, 0) > 0:
            bywidth.setdefault(w, []).append(f)
    best = None
    for w, fs in bywidth.items():
        if len(fs) < 2:
            continue
        fs = sorted(fs, key=lambda f: -used[f])
        score = min(used[fs[0]], used[fs[1]]) * w
        if best is None or score > best[0]:
            best = (score, (fs[0], fs[1]))
    return best[1] if best else None


def render(block_top: str, base: str, cand: str, k: int,
           base_src: str, cand_src: str) -> tuple[str, str]:
    """Return (proof_file, control_file) Lean sources.

    Raises if no meaningful negative control can be built -- a proof we cannot
    check for vacuity is not reported as a proof."""
    bt, ct = f'{block_top}_{base}', f'{block_top}_{cand}'
    ins = _fields(base_src, bt, 'in')
    outs = _fields(base_src, bt, 'out')
    if not ins or not outs:
        raise ValueError(f'could not parse {bt}_in/_out structures')

    # Control coercion: swap two equal-width inputs the model actually reads.
    swap = pick_swap(ins, base_src + cand_src)
    if k == 0 and swap is None:
        raise ValueError(
            f'{cand}: no two live equal-width inputs to build a negative control '
            f'from; refusing to emit an uncheckable proof')

    # PER-OUTPUT regime, read off the emitted model.  A pipelined block is
    # usually MIXED: candidate `p1` registers result_o but leaves branch_res_o
    # combinational on purpose.  Emitting one regime for the whole module would
    # either assert something false about the combinational output or fail to
    # state the true claim about the registered one.
    regimes = output_regimes(cand_src, ct)
    if not regimes:
        regimes = {f: (0 if k == 0 else 1) for f, _ in outs}

    head = (f'-- GENERATED by hagent retime prover. Do not edit.\n'
            f'import Normalize\nimport Refine\n'
            f'import {bt}_Lgraph\nimport {ct}_Lgraph\n\n'
            f'open AluNorm\nopen {bt}_Lgraph\nopen {ct}_Lgraph\n\n'
            f'set_option maxRecDepth 10000000\nset_option maxHeartbeats 0\n\n')

    def eq_thm(coe: str, f: str) -> str:
        return (f'theorem eq_{f} (i : {bt}_in){state_arg} :\n'
                f'    ({bt}_comb i).{f}\n'
                f'      = ({ct}_comb ({coe} i){state_use}).{f} := by\n'
                f'  show _ = _\n'
                f'  simp only [{bt}_comb, {ct}_comb]\n'
                f'  alu_norm\n  bv_decide\n')

    def ref_thm(coe: str, f: str) -> str:
        # Present i, then ANY later input, from ANY state.  Both quantifiers are
        # load-bearing: forall-state is what removes the reachability invariant
        # (available only because the rank is reset-free and always-enabled, so
        # flop_next collapses), and forall-later-input is what forces the rank to
        # be a complete cut.
        return (f'theorem refines_{f} (i j : {bt}_in) (s : {ct}_state) :\n'
                f'    ({ct}_comb ({coe} j) ({ct}_next ({coe} i) s)).{f}\n'
                f'      = ({bt}_comb i).{f} := by\n'
                f'  show _ = _\n'
                f'  simp only [{ct}_comb, {ct}_next, {bt}_comb, flop_next]\n'
                f'  alu_norm\n  bv_decide\n')

    has_state = any(v == 1 for v in regimes.values()) or k > 0
    state_arg = ' (s : ' + ct + '_state)' if has_state else ''
    state_use = ' s' if has_state else ''

    body = [f'namespace Equiv{cand.capitalize()}Pos\n', _coercion('toCand', bt, ct, ins, None)]
    for f, _ in outs:
        body.append(ref_thm('toCand', f) if regimes.get(f, k) else eq_thm('toCand', f))
    body.append(f'end Equiv{cand.capitalize()}Pos\n')
    proof = head + '\n'.join(body)

    # Control.  Per output: a k=0 output gets swapped live operands; a k=1 output
    # gets the k=0 claim, which MUST fail or the rank shifted no latency.
    cbody = [f'namespace Equiv{cand.capitalize()}Neg\n',
             _coercion('toCandSwap', bt, ct, ins, swap),
             _coercion('toCandK0', bt, ct, ins, None)]
    for f, _ in outs:
        if regimes.get(f, k):
            cbody.append(
                f'-- MUST FAIL: asserts the registered output matches on the SAME\n'
                f'-- cycle.  If it passes, the rank shifted nothing.\n'
                f'theorem k0_{f} (i : {bt}_in) (s : {ct}_state) :\n'
                f'    ({ct}_comb (toCandK0 i) s).{f} = ({bt}_comb i).{f} := by\n'
                f'  show _ = _\n'
                f'  simp only [{ct}_comb, {bt}_comb]\n'
                f'  alu_norm\n  bv_decide\n')
        else:
            cbody.append('-- MUST FAIL: operands swapped.\n' + eq_thm('toCandSwap', f))
    cbody.append(f'end Equiv{cand.capitalize()}Neg\n')
    control = head + '\n'.join(cbody)

    return proof, control


def classify(log: str, exit_code: Optional[int]) -> str:
    """Read a Lean run's output.  Order matters: the spurious-counterexample
    phrase contains the word 'counterexample', so it must be tested FIRST."""
    if exit_code is None:
        return TOOL_ERROR
    if 'potentially spurious counterexample' in log or 'abstracted the following' in log:
        return NORMALIZER_GAP
    if 'The prover found a counterexample' in log:
        return COUNTEREXAMPLE
    if 'maximum number of heartbeats' in log or 'deterministic) timeout' in log:
        return TIMEOUT
    if 'error:' in log:
        return TOOL_ERROR
    return PROVEN if exit_code == 0 else TOOL_ERROR


def verdict(proof_status: str, control_status: str) -> tuple[str, str]:
    """Combine the two runs.  A proof is only a result if its control FAILED --
    otherwise the tactic script proves anything and the 'proof' is vacuous."""
    if proof_status != PROVEN:
        return proof_status, ''
    if control_status in (COUNTEREXAMPLE, TIMEOUT, TOOL_ERROR, NORMALIZER_GAP):
        return PROVEN, 'FAILED_AS_REQUIRED'
    return TOOL_ERROR, 'LEAKED'
