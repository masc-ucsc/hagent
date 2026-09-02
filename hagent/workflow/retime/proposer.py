"""The proposer agent: given the ledger, emit ONE new candidate generator.

Written fresh rather than reused.  HAgent's `arch_agent.py` is the right idea and
its prompt is a useful reference, but it does not import on upstream main -- it
needs `hagent.core.react`, `hagent.core.llm.*`, `frequency_opt.config` and
`frequency_opt.common_utils`, none of which exist in the repo.  This module uses
the parts of HAgent that DO work: `LLM_wrap` and `Step`.

Two things distinguish it from a generic "make this faster" agent:

1. **It is shown the whole ledger, including the failures.**  That is what makes
   the search converge instead of circling, and the negative results are the more
   informative half -- on the ALU, reassociation candidates were null or worse
   while structural ones gave 1.78x.  An agent shown only successes would
   re-propose the failures forever.

2. **It emits a generator script, not RTL.**  Same pattern as the hand-written
   `mk_a3.py`/`mk_a4.py`: assert every anchor string, then replace.  A proposal
   whose anchors have drifted fails loudly at generation time instead of silently
   producing a design that is not what the rationale claims.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Optional

from hagent.core.llm_wrap import LLM_wrap
from hagent.workflow.retime.ledger import Ledger

_BLOCKS = {
    'cand': r'===\s*CAND:\s*(\S+)\s*===',
    'transform': r'===\s*TRANSFORM:\s*(\S+)\s*===',
    'parent': r'===\s*PARENT:\s*(\S+)\s*===',
    'latency': r'===\s*LATENCY:\s*(\d+)\s*===',
}


def parse(text: str) -> Optional[dict]:
    """Parse the block format.  Returns None if any required block is missing --
    the caller retries rather than guessing, because a half-parsed proposal
    produces a candidate whose recorded rationale does not match its RTL."""
    out = {}
    for key, rx in _BLOCKS.items():
        m = re.search(rx, text)
        if not m:
            return None
        out[key] = m.group(1)
    rat = re.search(r'===\s*RATIONALE\s*===\s*\n(.*?)\n===\s*END RATIONALE\s*===',
                    text, re.DOTALL)
    scr = re.search(r'===\s*SCRIPT\s*===\s*\n(.*?)\n===\s*END SCRIPT\s*===',
                    text, re.DOTALL)
    if not scr:
        return None
    out['rationale'] = (rat.group(1).strip() if rat else '')
    script = scr.group(1).strip()
    # Strip a markdown fence if the model added one.
    script = re.sub(r'^```(?:python)?\s*\n', '', script)
    script = re.sub(r'\n```\s*$', '', script)
    out['script'] = script
    out['latency'] = int(out['latency'])
    return out


def _fmt_ledger(led: Ledger, block: str) -> str:
    rows = sorted((r for r in led.latest(block)), key=lambda r: r.crit_ps or 9e9)
    if not rows:
        return '  (empty -- this is the first proposal)'
    out = []
    for r in rows:
        ps = f'{r.crit_ps:.1f} ps' if r.crit_ps else 'not measured'
        verdict = r.proof if r.proof != 'NOT_ATTEMPTED' else (r.miter or r.gates or '-')
        out.append(f'  {r.cand:<10} {ps:>12}  k={r.latency_k}  {verdict:<16} '
                   f'{r.transform or "-"}  :: {(r.rationale or "")[:100]}')
    return '\n'.join(out)


class Proposer:
    """Turns the ledger into one new candidate generator script.

    Note on latency: a reasoning model given a few hundred lines of RTL can take
    many minutes per call, and litellm's default request timeout will cut it off
    mid-flight.  `timeout_s` is passed through explicitly so an unattended loop
    fails with a clear reason instead of hanging, and so the caller can trade
    thinking depth against wall time via `effort`."""

    def __init__(self, blk: dict, led: Ledger, conf: Optional[str] = None,
                 log: str = 'retime_proposer.log'):
        self.blk = blk
        self.led = led
        conf = conf or str(Path(__file__).parent / 'proposer_prompts.yaml')
        # Model is overridable without editing the prompt file, so a run can be
        # pointed at whichever provider actually has working credentials.
        import os
        over = {}
        if os.environ.get('RETIME_PROPOSER_MODEL'):
            over = {'retime_proposer': {'llm': {'model': os.environ['RETIME_PROPOSER_MODEL']}}}
        # Latency controls, overridable per run without editing the prompt file.
        llm_over = over.setdefault('retime_proposer', {}).setdefault('llm', {})
        if os.environ.get('RETIME_PROPOSER_TIMEOUT'):
            llm_over['timeout'] = int(os.environ['RETIME_PROPOSER_TIMEOUT'])
        if os.environ.get('RETIME_PROPOSER_EFFORT'):
            llm_over['reasoning_effort'] = os.environ['RETIME_PROPOSER_EFFORT']
        self.llm = LLM_wrap(name='retime_proposer', conf_file=conf, log_file=log,
                            overwrite_conf=over)
        self.last_reason = ''

    def propose(self, tries: int = 3) -> Optional[dict]:
        blk, led = self.blk, self.led
        block = blk['block']
        best = led.best(block)
        parent = best.cand if best else blk.get('baseline', 'base')
        rtl = Path(blk['bench_blk']) / 'rtl' / f'{block}_{parent}.sv'
        if not rtl.is_file():
            return None

        tax = '\n'.join(f'  - {t["id"]} ({t["kind"]}): {t["note"].strip()}'
                        for t in blk.get('transform_taxonomy', []))
        # Names taken in the ledger AND on disk -- see taken_names().
        seen = {c.cand for c in led.latest(block)} | self.taken_names()
        pd = {
            'block': block, 'top_prefix': blk['top_prefix'],
            'taxonomy': tax or '  (none given)',
            'best_cand': parent,
            'best_ps': f'{best.crit_ps:.1f}' if best and best.crit_ps else '?',
            'best_ghz': f'{1000 / best.crit_ps:.3f}' if best and best.crit_ps else '?',
            'startpoint': (best.startpoint if best else '') or '?',
            'endpoint': (best.endpoint if best else '') or '?',
            'ledger': _fmt_ledger(led, block),
            'parent': parent, 'parent_rtl': rtl.read_text(),
        }

        self.last_reason = ''
        for _ in range(tries):
            resp = self.llm.inference(pd, 'propose', n=1)
            if not resp:
                # LLM_wrap returns [] for BOTH a real API error and a response
                # that hit max_tokens with no visible content -- and in the
                # latter case last_error is EMPTY, so an unattended loop that
                # only checks last_error sees a silent nothing.  Measured: at
                # max_tokens=6000, Opus 5's adaptive thinking consumed the whole
                # budget and returned finish_reason=length with zero content.
                self.last_reason = (f'no response (llm error: {self.llm.last_error})'
                                    if self.llm.last_error
                                    else 'empty response -- likely max_tokens exhausted '
                                         'by thinking; raise llm.max_tokens')
                continue
            got = parse(resp[0])
            if not got:
                self.last_reason = 'response did not match the required block format'
                continue                      # malformed -> retry, never guess
            self.last_reason = ''
            if got['cand'] in seen:
                # Already explored.  Tell it so on the retry rather than
                # silently dropping the proposal.
                pd['ledger'] += (f'\n  !! the name {got["cand"]} is already taken '
                                 f'(ledger or on disk). Choose a different one.')
                continue
            return got
        return None

    def taken_names(self) -> set[str]:
        """Candidate names already claimed ON DISK, not just in the ledger.

        The ledger is per-thread and per-block; the benchmark repo may already
        contain hand-written generators and RTL from earlier work.  A live run
        proposed the name `a5`, which was absent from that run's ledger but
        present on disk, and materialize() OVERWROTE a hand-written generator.
        Recovered from git, but nothing should depend on the file happening to
        be tracked."""
        bench = Path(self.blk['bench_blk'])
        names = set()
        for p in (bench / 'scripts').glob('mk_*.py'):
            names.add(p.stem[3:])
        for p in (bench / 'rtl').glob(f'{self.blk["block"]}_*.sv'):
            names.add(p.stem.split('_', 1)[1])
        return names

    def materialize(self, got: dict) -> Path:
        """Write the generator script where the emit node expects it.

        Refuses to overwrite: a generator on disk is either prior work or a
        previous candidate, and clobbering it silently loses both the artifact
        and the audit trail."""
        p = Path(self.blk['bench_blk']) / 'scripts' / f'mk_{got["cand"]}.py'
        if p.exists():
            raise FileExistsError(
                f'{p} already exists; refusing to overwrite an existing generator')
        p.write_text(got['script'] + '\n')
        return p
