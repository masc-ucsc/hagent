"""Graph node bodies: emit, gate, measure, screen, prove.

Each wraps a script that is ALREADY the validated implementation from the CVA6
ALU study (`retimed-benchmark/cva6/lean_pass/`), rather than reimplementing the
EDA logic here.  Those scripts encode two traps that silently produce meaningless
numbers if dropped, so they are reused verbatim, not rewritten:

  * ABC needs `-constr`, or it never buffers: 1544 ps of the ALU's 1779 ps was
    un-buffered net charging on 0.33x cells driving 204 loads.  With it: 907 ps.
  * The `-D` target must be swept, or the report is the target, not the design.

Long steps (measure/screen/prove) do not run inline.  They are launched as
durable units and polled across checkpoints, so the graph survives its own death.
"""

from __future__ import annotations

import json
import os
import re
import subprocess
from pathlib import Path
from typing import Optional

from hagent.workflow.retime.durable import DurableRunner, DONE, RUNNING, LOST, NOT_STARTED
from hagent.workflow.retime import ledger as L


def _env(blk: dict) -> dict:
    e = dict(os.environ)
    e['BENCH_BLK'] = blk['bench_blk']
    e['TOP_PREFIX'] = blk['top_prefix']
    return e


# ------------------------------------------------------------------ emit
def emit(blk: dict, cand: str) -> tuple[bool, dict]:
    """Generate the candidate's RTL and run it through lhd: Lean model + flat
    Verilog from the SAME Lgraph.  That shared origin is the methodological
    point -- the timing number and the proof then describe the same design."""
    bench = Path(blk['bench_blk'])
    mk = bench / 'scripts' / f'mk_{cand}.py'
    if mk.is_file():
        r = subprocess.run(['python3', str(mk)], cwd=bench, capture_output=True, text=True)
        if r.returncode != 0:
            return False, {'gates': f'FAIL:generator {r.stderr.strip()[:200]}'}

    r = subprocess.run([str(bench / 'scripts' / 'gen_candidate.sh'), cand],
                       cwd=bench, env=_env(blk), capture_output=True, text=True)
    if r.returncode != 0:
        return False, {'gates': f'FAIL:emit {(r.stderr or r.stdout).strip()[:200]}'}

    # pass.lean's own summary line is the authoritative structural fact, and it
    # is what decides the proof regime -- combinational equality vs latency-k
    # refinement.  Never inferred from the RTL text.
    m = re.search(r'\((\d+) nodes, (\d+) flops', r.stdout)
    if not m:
        return False, {'gates': 'FAIL:no pass.lean summary line'}
    return True, {'nodes': int(m.group(1)), 'flops': int(m.group(2))}


# ------------------------------------------------------------------ gate
def gate(blk: dict, cand: str, flops: int, expect_flops: Optional[int]) -> tuple[bool, str]:
    """Seconds-cheap static screens, run before anything expensive.  These have
    already caught real defects three times in this project."""
    bench, common = Path(blk['bench_blk']), Path(blk['common'])
    gen = list((bench / 'work' / cand / 'lean').glob('*_Lgraph.lean'))
    if not gen:
        return False, 'FAIL:no emitted model'

    r = subprocess.run(['python3', str(common / 'bv_ready.py'), str(gen[0])],
                       capture_output=True, text=True)
    if r.returncode != 0:
        bad = [l.strip() for l in r.stdout.splitlines() if 'MISSING' in l]
        return False, f'FAIL:bv_ready {bad[:3]}'

    # A pipelined candidate must have exactly the ranks it claims.  pass.lean
    # never reads pipe_min/pipe_max, so a ranged-depth Flop would be silently
    # modelled as ONE cycle -- a soundness hole, not a cosmetic one.
    if expect_flops is not None and flops != expect_flops:
        return False, f'FAIL:flop count {flops} != expected {expect_flops}'

    if flops:
        # Complete-cut check: stage 2 must read only registered signals, or the
        # "for ALL later inputs" refinement is simply false.
        txt = gen[0].read_text()
        body = txt[txt.find('_comb'):txt.find('_next')] if '_next' in txt else ''
        if re.search(r'\bi\.in_(operand|operation)', body):
            return False, 'FAIL:incomplete cut (comb reads raw inputs)'
    return True, 'PASS'


# --------------------------------------------------------------- measure
def measure_launch(run: DurableRunner, blk: dict, cand: str) -> str:
    job = f'{blk["block"]}-{cand}-sta'
    targets = [str(t) for t in blk.get('sta_targets', [800, 600, 450, 300])]
    run.claim(job, 'synth')
    run.launch(job, [str(Path(blk['common']) / 'sta_sweep.sh'), cand, *targets],
               cwd=blk['bench_blk'], env={'BENCH_BLK': blk['bench_blk'],
                                          'TOP_PREFIX': blk['top_prefix']},
               exclusive='synth')
    return job


def measure_reap(blk: dict, cand: str) -> dict:
    """Best point over the swept targets -- the saturated value, not the target."""
    sta = Path(blk['bench_blk']) / 'results' / 'sta'
    pts = []
    for p in sta.glob(f'{cand}_d[0-9]*/timing.json'):
        try:
            pts.append(json.loads(p.read_text()))
        except (json.JSONDecodeError, OSError):
            pass
    pts = [p for p in pts if p.get('critical_path_ps')]
    if not pts:
        return {}
    b = min(pts, key=lambda d: d['critical_path_ps'])
    return {'crit_ps': b['critical_path_ps'], 'fmax_ghz': b.get('fmax_ghz'),
            'area_um2': b.get('area_um2'), 'startpoint': b.get('startpoint') or '',
            'endpoint': b.get('endpoint') or ''}


# ---------------------------------------------------------------- screen
def screen_launch(run: DurableRunner, blk: dict, cand: str, k: int) -> str:
    """k=0 -> combinational miter, which for a 0-flop design is a COMPLETE
    decision procedure, not a screen.  k>=1 -> delay-matched golden, because a
    cycle-accurate miter would correctly refuse a latency change."""
    job = f'{blk["block"]}-{cand}-lec'
    script = 'lec_screen.sh' if k == 0 else 'lec_pipe.sh'
    run.claim(job, 'lec')
    run.launch(job, [str(Path(blk['common']) / script), cand, blk.get('baseline', 'base')],
               cwd=blk['bench_blk'], env={'BENCH_BLK': blk['bench_blk'],
                                          'TOP_PREFIX': blk['top_prefix']},
               exclusive='lec')
    return job


def screen_reap(run: DurableRunner, job: str) -> str:
    log = run.jobdir(job) / 'job.log'
    txt = log.read_text() if log.is_file() else ''
    if 'PROVEN' in txt:
        return 'PROVEN'
    if 'REFUTED' in txt:
        return 'REFUTED'
    return 'ERROR'
