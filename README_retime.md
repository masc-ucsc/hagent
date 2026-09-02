# `hagent.workflow.retime` — automated RTL retiming with machine-checked proofs

Proposes faster RTL for a hardware block, measures it, and **proves** each
candidate equivalent to the original — unattended, resumable, and with every
candidate logged whether it was proven or refuted.

Same-latency candidates are proven by plain equality; candidates that add a
pipeline stage are proven as a **latency-k refinement** (*feed input `i`, then
any later inputs, from any state — the output k cycles later is the reference's
answer for `i`*).

## Why three layers

| layer | owns | why not one of the others |
|---|---|---|
| `DurableRunner` (`durable.py`) | the multi-hour processes | LangGraph checkpoints *state*, but has no watchdog, no failure detection, no heartbeat. Our unit of work is a 4–6 h Lean job (CVA6 `pmp` took 6.2 h) running unattended |
| LangGraph (`graph.py`) | state machine, checkpoints, resume, ledger | knows the DAG; cannot supervise a subprocess |
| HAgent | `Step`, `LLM_wrap`, EDA tooling | hardware-native |

No node ever blocks on a long job: it launches a durable unit, polls once, and
routes back to itself if still running. LangGraph checkpoints between hops, so
killing the orchestrator mid-proof loses nothing.

## The trap this design exists to avoid

```
$ systemctl --user show a-unit-that-never-existed -p Result,ExecMainStatus
Result=success
ExecMainStatus=0
```

A unit that never ran is **indistinguishable from one that succeeded**. A poller
trusting systemd would mark an unproven candidate `PROVEN`. So the wrapped
command writes its own `status.json` sentinel, and `poll()` believes only that.
systemd supplies supervision; it does not supply verdicts.

## Honesty rules (the reason this can run unattended)

* Every proof ships with a **negative control** — swapped operands for k=0, the
  k=0 claim for k≥1. A proof whose control *also* passes is recorded as
  `TOOL_ERROR/LEAKED`, never as a win.
* `NORMALIZER_GAP` ≠ `COUNTEREXAMPLE`. `bv_decide` says *"potentially spurious
  counterexample … abstracted the following"* when it meets an idiom
  `Normalize.lean` does not cover. That is a coverage hole, not a refutation.
  Three real runs died this way (`bool_to_bv1`, the MuxN `if toNat = k`
  lowering, signed compares emitted as `Int` arithmetic).
* A job that vanishes is `LOST`, never `DONE`.

## Usage

```sh
uv run python -m hagent.workflow.retime.run \
    --block hagent/workflow/retime/blocks/cva6_alu.yaml \
    --candidates a1,a2,a3,a4,a5,p1
```

Re-run the same command to resume: the ledger dedupes on normalized-RTL hash and
the checkpointer restores the graph.

## Adding a block

A block is data — `blocks/<name>.yaml` plus a `scripts/mk_base.py` in the
benchmark repo. Nothing in this package is ALU-specific: the prover parses the
emitted `structure <top>_in/_out` to build its coercion and theorems.

## Stopping

Stop when **five distinct candidates fail to beat the incumbent** best
frequency. "Distinct" is by normalized-RTL hash; "fail to beat" means no
improvement over 1%, because two different RTLs tying to the exact picosecond
essentially never happens (the ALU's six candidates gave six distinct values).
A budget cap backstops a proposer emitting near-duplicates.

## Validated on the CVA6 ALU

Both candidates ran end to end through the loop, unattended, and reproduced the
hand-derived study exactly:

| candidate | regime | emitted | critical path | miter | proof |
|---|---|---|---|---|---|
| `a4` | k=0 both outputs | 10,178 nodes / 0 flops | **509.3687 ps** (1.963 GHz, 1.78x) | PROVEN | PROVEN, control failed as required |
| `p1` | mixed: `branch_res_o` k=0, `result_o` k=1 | 9,162 nodes / 26 flops | **285.6845 ps** (3.500 GHz, 3.17x) | PROVEN (delay-matched golden) | PROVEN, control failed as required |

Both critical-path numbers match the hand-derived study to the picosecond, and
both proofs were *generated* — from the emitted models, not written by hand.

`p1` is the interesting one: it is *mixed latency* by design, and the prover
derives that per-output from the emitted model rather than being told, producing
`eq_out_branch_res_o` + `refines_out_result_o` — the same shape as the
hand-written `Equiv_P1.lean`.

### The proposer, validated live

Given the ledger above, it proposed (289 s):

```
cand      : b1
transform : pipeline-rank   parent=p1   k=1
rationale : p1's measured critical path is the only remaining port-to-port
            combinational path: operand_a_i[23] -> 6-level comparator prefix
            tree -> sign-fix mux -> `less` -> opcode branch mux -> branch_res_o
            (285.7 ps), while the result path is already cut by the rank.  This
            moves branch resolution to the far side of the existing rank...
script    : 3936 chars, anchored on exact strings from rtl/alu_p1.sv
```

Three things that indicate it is using the ledger rather than pattern-matching:
it chose `p1` (the current best) as parent, not the baseline; it quoted the
*measured* startpoint/endpoint; and it identified that `branch_res_o` is now the
only uncut path — which is correct, and is exactly the tradeoff deliberately left
on the table when `p1` was written by hand.  Note the framework can prove such a
candidate correct while the *desirability* of a 1-cycle branch resolution remains
a human microarchitectural call; the ledger records it either way.

## Status

* `durable.py`, `ledger.py`, `prover.py`, `graph.py`, `run.py` — implemented,
  14 tests passing.
* Proposer is a fixed list (Phase 1), so orchestration is validated without an
  LLM in the loop. The LLM proposer reuses HAgent's `LLM_wrap`.
* Isabelle is a second prover behind the same interface; its normalizer does not
  exist yet.

### On reusing HAgent's `frequency_opt`

Audited at upstream `3f8005c`. `synth_sta.py` imports cleanly and is reusable.
`arch_agent.py` and `extract_critical.py` **do not import on upstream main** —
they reference `hagent.core.react`, `hagent.core.llm.*`,
`frequency_opt.config` and `frequency_opt.common_utils`, none of which exist in
the repo. They appear to be committed against a refactor that never landed. So
the proposer is written fresh against `hagent.core.llm_wrap`, and
`extract_critical` is unnecessary because `sta.sh` already reports the critical
path's startpoint and endpoint.
