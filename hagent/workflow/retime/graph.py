"""The LangGraph loop: propose -> emit -> gate -> measure -> screen -> prove -> record.

Division of labour, deliberately:

  LangGraph  owns the state machine, the checkpoints, and the accumulated ledger.
  DurableRunner owns the PROCESSES, because LangGraph checkpoints state but has
  no watchdog, no failure detection and no heartbeat -- and our unit of work is a
  multi-hour Lean job running unattended.

So no node ever blocks on a long job.  A long step launches a durable unit,
polls once, and if it is still running routes BACK TO ITSELF after a short sleep.
LangGraph checkpoints between those hops, so killing the orchestrator at any
point and restarting resumes with the unit either still running or its sentinel
already on disk -- never re-spending a 6-hour proof.
"""

from __future__ import annotations

import time
from pathlib import Path
from typing import Annotated, Any, Optional, TypedDict

import yaml
from langgraph.graph import END, START, StateGraph

from hagent.workflow.retime import nodes as N
from hagent.workflow.retime import prover as P
from hagent.workflow.retime.durable import DONE, LOST, NOT_STARTED, RUNNING, DurableRunner
from hagent.workflow.retime.ledger import Candidate, Ledger, NOT_ATTEMPTED, PROVEN

POLL_S = 20.0


class RetimeState(TypedDict, total=False):
    blk: dict
    queue: list          # candidate names still to try
    cand: Optional[str]
    k: int
    rec: dict            # accumulated Candidate fields for the current candidate
    job: Optional[str]
    phase: str
    stop_reason: str
    trace: list
    meta: dict           # proposer provenance: rationale, transform, parent


def build(blk: dict, ledger: Ledger, run: DurableRunner, propose_fn=None):
    """`propose_fn(state, ledger) -> (name, k) | None` is the pluggable proposer.
    Phase 1 passes a hardcoded list so orchestration is validated separately from
    LLM behaviour: if the loop cannot replay a known-good sequence, no amount of
    proposer quality helps."""

    def _log(s: RetimeState, msg: str) -> list:
        return list(s.get('trace', [])) + [f'{time.strftime("%H:%M:%S")} {msg}']

    # ------------------------------------------------------------- select
    def select(s: RetimeState) -> dict:
        stop, why = ledger.should_stop(blk['block'])
        if stop:
            return {'cand': None, 'stop_reason': why, 'trace': _log(s, f'STOP {why}')}
        nxt = propose_fn(s, ledger) if propose_fn else None
        if not nxt:
            return {'cand': None, 'stop_reason': 'proposer exhausted',
                    'trace': _log(s, 'STOP proposer exhausted')}
        name, k = nxt
        # The proposer's rationale / transform tag / parent are part of the
        # record: a ledger that says WHAT was tried but not WHY cannot stop the
        # proposer repeating an idea in different words.
        meta = (s.get('meta') or {}).get(name, {})
        rec = {'block': blk['block'], 'cand': name, 'latency_k': k}
        for f in ('rationale', 'transform', 'parent'):
            if meta.get(f):
                rec[f] = meta[f]
        return {'cand': name, 'k': k, 'job': None, 'phase': 'emit', 'rec': rec,
                'trace': _log(s, f'--- candidate {name} (k={k}) {meta.get("transform","")}')}

    # --------------------------------------------------------------- emit
    def emit(s: RetimeState) -> dict:
        cand = s['cand']
        ok, info = N.emit(blk, cand)
        rec = {**s['rec'], **info}
        if not ok:
            return {'rec': rec, 'phase': 'record', 'trace': _log(s, f'emit FAILED {info}')}

        # Never re-explore: reject a duplicate BEFORE spending a synthesis run.
        src = Path(blk['bench_blk']) / 'rtl' / f'{blk["block"]}_{cand}.sv'
        if src.is_file():
            from hagent.workflow.retime.ledger import rtl_sha
            dup = ledger.is_duplicate(blk['block'], src.read_text())
            rec['rtl_sha'] = rtl_sha(src.read_text())
            if dup and dup != cand:
                rec['gates'] = f'FAIL:duplicate of {dup}'
                return {'rec': rec, 'phase': 'record',
                        'trace': _log(s, f'duplicate of {dup} -- skipped')}
        return {'rec': rec, 'phase': 'gate',
                'trace': _log(s, f'emitted {info.get("nodes")} nodes / {info.get("flops")} flops')}

    # --------------------------------------------------------------- gate
    def gate(s: RetimeState) -> dict:
        rec = dict(s['rec'])
        flops = rec.get('flops') or 0
        # A pipelined candidate declares its rank count; a mismatch is a
        # soundness problem, not a warning (pass.lean ignores pipe_min/pipe_max).
        ok, why = N.gate(blk, s['cand'], flops, rec.get('expect_flops'))
        rec['gates'] = why
        # The regime is decided by the emitted flop count, not by intent.
        k = 0 if flops == 0 else max(1, s.get('k', 1))
        return {'rec': rec, 'k': k, 'phase': 'measure' if ok else 'record',
                'trace': _log(s, f'gate {why}')}

    # ------------------------------------------------ long steps (launch/poll)
    def _long(s: RetimeState, launch, reap, nxt_phase: str, label: str) -> dict:
        job = s.get('job') or launch()
        st = run.poll(job)
        if st.state == RUNNING:
            time.sleep(POLL_S)
            return {'job': job, 'phase': s['phase']}          # self-loop, checkpointed
        if st.state == NOT_STARTED:
            time.sleep(POLL_S)
            return {'job': None, 'phase': s['phase'],
                    'trace': _log(s, f'{label} waiting for exclusive slot')}
        if st.state == LOST:
            rec = {**s['rec'], 'gates': f'FAIL:{label} job lost'}
            return {'rec': rec, 'job': None, 'phase': 'record',
                    'trace': _log(s, f'{label} LOST: {st.detail}')}
        rec = {**s['rec'], **reap(st)}
        return {'rec': rec, 'job': None, 'phase': nxt_phase,
                'trace': _log(s, f'{label} done exit={st.exit_code}')}

    def measure(s: RetimeState) -> dict:
        return _long(s, lambda: N.measure_launch(run, blk, s['cand']),
                     lambda st: N.measure_reap(blk, s['cand']), 'screen', 'sta')

    def screen(s: RetimeState) -> dict:
        return _long(s, lambda: N.screen_launch(run, blk, s['cand'], s['k']),
                     lambda st: {'miter': N.screen_reap(run, f'{blk["block"]}-{s["cand"]}-lec')},
                     'prove', 'lec')

    # -------------------------------------------------------------- prove
    def prove(s: RetimeState) -> dict:
        cand, k = s['cand'], s['k']
        bench, common = Path(blk['bench_blk']), Path(blk['common'])
        base = blk.get('baseline', 'base')
        gendir = bench / 'lean' / 'gen'
        gendir.mkdir(parents=True, exist_ok=True)

        if not s.get('job'):
            bsrc = (bench / 'work' / base / 'lean' / f'{blk["top_prefix"]}_{base}_Lgraph.lean')
            csrc = (bench / 'work' / cand / 'lean' / f'{blk["top_prefix"]}_{cand}_Lgraph.lean')
            if not (bsrc.is_file() and csrc.is_file()):
                return {'rec': {**s['rec'], 'proof': 'TOOL_ERROR'}, 'phase': 'record',
                        'trace': _log(s, 'prove: missing emitted model')}
            # FULL text, not a slice.  Two analyses need the whole file:
            # pick_swap() counts input references (to avoid building a control
            # from dangling ports), and output_regimes() parses the record at the
            # END of _comb -- which for p1 sits at ~line 9224 of a 2.3 MB file, so
            # any truncation silently reverts it to a single module-wide regime.
            proof, control = P.render(blk['top_prefix'], base, cand, k,
                                      bsrc.read_text(), csrc.read_text())
            (gendir / f'Equiv_{cand}_gen.lean').write_text(proof)
            (gendir / f'Equiv_{cand}_ctl.lean').write_text(control)

        # Proof and control both run; the control MUST fail for the proof to count.
        jobs = {}
        for tag, f in (('pos', f'Equiv_{cand}_gen.lean'), ('neg', f'Equiv_{cand}_ctl.lean')):
            j = f'{blk["block"]}-{cand}-lean-{tag}'
            run.claim(j, 'lean')
            run.launch(j, [str(common / 'leanrun.sh'), 'check', str(gendir / f)],
                       cwd=str(bench), env={'BENCH_BLK': str(bench),
                                            'TOP_PREFIX': blk['top_prefix']},
                       exclusive='lean')
            jobs[tag] = run.poll(j)

        if any(v.state in (RUNNING, NOT_STARTED) for v in jobs.values()):
            time.sleep(POLL_S)
            return {'job': 'pending', 'phase': 'prove'}

        out = {}
        for tag in ('pos', 'neg'):
            j = f'{blk["block"]}-{cand}-lean-{tag}'
            log = run.jobdir(j) / 'job.log'
            out[tag] = P.classify(log.read_text() if log.is_file() else '',
                                  jobs[tag].exit_code)
        status, control = P.verdict(out['pos'], out['neg'])
        poslog = run.jobdir(f'{blk["block"]}-{cand}-lean-pos') / 'job.log'
        rec = {**s['rec'], 'proof': status, 'control': control,
               'axioms': P.axioms(poslog.read_text() if poslog.is_file() else ''),
               'proof_wall_s': jobs['pos'].wall_s, 'proof_rss_kb': jobs['pos'].peak_rss_kb}
        return {'rec': rec, 'job': None, 'phase': 'record',
                'trace': _log(s, f'prove {status} control={control or out["neg"]}')}

    # ------------------------------------------------------------- record
    def record(s: RetimeState) -> dict:
        rec = dict(s['rec'])
        rec.setdefault('proof', NOT_ATTEMPTED)
        c = Candidate(**{k: v for k, v in rec.items() if k in Candidate.__annotations__})
        ledger.append(c)
        return {'cand': None, 'job': None, 'phase': 'select',
                'trace': _log(s, f'recorded {c.cand}: {c.crit_ps} ps {c.proof}')}

    # -------------------------------------------------------------- wiring
    g = StateGraph(RetimeState)
    for name, fn in (('select', select), ('emit', emit), ('gate', gate),
                     ('measure', measure), ('screen', screen), ('prove', prove),
                     ('record', record)):
        g.add_node(name, fn)
    g.add_edge(START, 'select')
    g.add_conditional_edges('select', lambda s: END if not s.get('cand') else 'emit',
                            {END: END, 'emit': 'emit'})
    g.add_conditional_edges('emit', lambda s: s['phase'], {'gate': 'gate', 'record': 'record'})
    g.add_conditional_edges('gate', lambda s: s['phase'],
                            {'measure': 'measure', 'record': 'record'})
    # Long steps route back to themselves while their durable unit runs.
    g.add_conditional_edges('measure', lambda s: s['phase'],
                            {'measure': 'measure', 'screen': 'screen', 'record': 'record'})
    g.add_conditional_edges('screen', lambda s: s['phase'],
                            {'screen': 'screen', 'prove': 'prove', 'record': 'record'})
    g.add_conditional_edges('prove', lambda s: s['phase'],
                            {'prove': 'prove', 'record': 'record'})
    g.add_edge('record', 'select')
    return g


def load_block(path: str | Path) -> dict:
    return yaml.safe_load(Path(path).read_text())
