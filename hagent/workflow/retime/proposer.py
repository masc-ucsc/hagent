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
    def __init__(self, blk: dict, led: Ledger, conf: Optional[str] = None,
                 log: str = 'retime_proposer.log'):
        self.blk = blk
        self.led = led
        conf = conf or str(Path(__file__).parent / 'proposer_prompts.yaml')
        self.llm = LLM_wrap(name='retime_proposer', conf_file=conf, log_file=log)

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
        seen = {c.cand for c in led.latest(block)}
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

        for _ in range(tries):
            resp = self.llm.inference(pd, 'propose', n=1)
            if not resp:
                continue
            got = parse(resp[0])
            if not got:
                continue                      # malformed -> retry, never guess
            if got['cand'] in seen:
                # Already explored.  Tell it so on the retry rather than
                # silently dropping the proposal.
                pd['ledger'] += f'\n  !! you just proposed {got["cand"]}, which exists. Propose something else.'
                continue
            return got
        return None

    def materialize(self, got: dict) -> Path:
        """Write the generator script where the emit node expects it."""
        p = Path(self.blk['bench_blk']) / 'scripts' / f'mk_{got["cand"]}.py'
        p.write_text(got['script'] + '\n')
        return p
