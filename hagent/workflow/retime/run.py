"""CLI: run the retiming loop for one block, resumably.

    uv run python -m hagent.workflow.retime.run \
        --block hagent/workflow/retime/blocks/cva6_alu.yaml \
        --candidates a1,a2,a3,a4,a5,p1

Resume is the default and the point: re-running the same command with the same
`--thread` picks up from the last checkpoint.  Combined with the durable job
layer, that means killing this process during a 6-hour proof loses nothing --
on restart the graph finds the unit still running, or its sentinel on disk.
"""

from __future__ import annotations

import argparse
import sqlite3
import sys
from pathlib import Path

from langgraph.checkpoint.sqlite import SqliteSaver

from hagent.workflow.retime.durable import DurableRunner
from hagent.workflow.retime.graph import build, load_block
from hagent.workflow.retime.ledger import Ledger


def fixed_proposer(names):
    """Phase-1 proposer: a fixed list, so orchestration is validated WITHOUT any
    LLM in the loop.  Replaced by the LLM proposer once the spine is proven."""
    pending = list(names)

    def propose(state, ledger):
        block = state['blk']['block']
        done = {c.cand for c in ledger.latest(block)}
        while pending:
            n = pending.pop(0)
            if n not in done:
                # k is decided for real by the emitted flop count in `gate`;
                # this is only the initial guess for routing.
                return (n, 1 if n.startswith('p') else 0)
        return None

    return propose


def llm_proposer(blk, ledger):
    """LLM proposer: writes the generator script, then hands the name back to the
    graph, which emits/gates/measures/screens/proves it like any other."""
    from hagent.workflow.retime.proposer import Proposer
    prop = Proposer(blk, ledger)

    def propose(state, led):
        got = prop.propose()
        if not got:
            return None
        prop.materialize(got)
        # Stash provenance where select() picks it up, so the ledger records the
        # reasoning alongside the result.  `state` is the live graph state dict.
        state.setdefault('meta', {})[got['cand']] = {
            'rationale': got['rationale'], 'transform': got['transform'],
            'parent': got['parent']}
        return (got['cand'], got['latency'])

    return propose


def main(argv=None) -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument('--block', required=True)
    ap.add_argument('--candidates', default='',
                    help='comma-separated fixed list (Phase 1). Empty => LLM proposer.')
    ap.add_argument('--thread', default=None, help='resume key (default: block name)')
    ap.add_argument('--state-dir', default='build/retime')
    ap.add_argument('--max-steps', type=int, default=2000)
    a = ap.parse_args(argv)

    blk = load_block(a.block)
    sd = Path(a.state_dir) / blk['block']
    sd.mkdir(parents=True, exist_ok=True)

    ledger = Ledger(sd / 'ledger.jsonl')
    run = DurableRunner(sd / 'jobs')

    if a.candidates:
        propose = fixed_proposer([c for c in a.candidates.split(',') if c])
    else:
        propose = llm_proposer(blk, ledger)

    # SqliteSaver is NOT a context manager in this version -- `with SqliteSaver(conn)`
    # raises TypeError.  Construct it directly.
    conn = sqlite3.connect(str(sd / 'checkpoints.sqlite'), check_same_thread=False)
    cp = SqliteSaver(conn)
    app = build(blk, ledger, run, propose).compile(checkpointer=cp)
    cfg = {'configurable': {'thread_id': a.thread or blk['block']},
           'recursion_limit': a.max_steps}
    final, shown = None, 0
    for ev in app.stream({'blk': blk, 'queue': [], 'phase': 'select', 'trace': []},
                         cfg, stream_mode='values'):
        final = ev
        # Print only NEW trace lines: the long steps self-loop while polling and
        # return no trace entry, so printing "the last line" each event repeats it.
        tr = ev.get('trace', [])
        for line in tr[shown:]:
            print(line, flush=True)
        shown = len(tr)

    print('\n' + ledger.summary(blk['block']))
    stop, why = ledger.should_stop(blk['block'])
    print(f'\nstop={stop}: {why}')
    if final and final.get('stop_reason'):
        print(f'reason: {final["stop_reason"]}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
