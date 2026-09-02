"""Append-only candidate ledger: the loop's memory and its stopping rule.

Three jobs, all of which the ALU study did by hand:

1. **Never re-explore.**  A proposal whose normalized-RTL hash is already present
   is rejected before a synthesis run is spent.  This is what makes an unattended
   proposer converge instead of circling.

2. **Keep the failures.**  A refuted or slower candidate is as valuable as a
   proven one -- it is the evidence that stops the proposer re-proposing it, and
   it is the record a reader needs to believe the search was real.  Nothing is
   ever pruned.  The ALU study's most useful single result was a NEGATIVE one
   (reassociation in RTL does not survive ABC), which a proven-only log would
   have thrown away.

3. **Decide when a block is done.**  Stop when five DISTINCT candidates have each
   failed to beat the incumbent best frequency.

On the stopping rule: "five candidates that share the same frequency" is
implemented with a tolerance rather than an exact tie, because two different RTLs
landing on the identical picosecond is vanishingly unlikely -- the ALU's six
candidates produced six distinct values (906.9 / 897.2 / 915.8 / 849.2 / 542.9 /
509.4 ps).  Read literally, an exact-tie rule would never fire.  So a candidate
"fails to beat" the incumbent when it does not improve it by more than
`improve_tol` (default 1%), the counter resets on any real improvement, and it
fires at five.
"""

from __future__ import annotations

import hashlib
import json
import re
import time
from dataclasses import dataclass, field, asdict
from pathlib import Path
from typing import Any, Iterable, Optional

# Proof outcomes.  NORMALIZER_GAP is deliberately NOT a refutation: bv_decide
# reports "potentially spurious counterexample" with abstracted terms when it
# meets an idiom the normalizer does not cover, and an unattended loop that
# conflates that with COUNTEREXAMPLE discards good candidates.  That distinction
# cost three runs to learn during the ALU study.
PROVEN = 'PROVEN'
COUNTEREXAMPLE = 'COUNTEREXAMPLE'
NORMALIZER_GAP = 'NORMALIZER_GAP'
TIMEOUT = 'TIMEOUT'
TOOL_ERROR = 'TOOL_ERROR'
NOT_ATTEMPTED = 'NOT_ATTEMPTED'


def rtl_sha(src: str) -> str:
    """Hash RTL modulo cosmetics, so a renamed or re-commented duplicate is still
    recognized as one.  Comments, blank lines and runs of whitespace are dropped,
    and the module name is normalized -- every candidate is the same module under
    a different name, so leaving it in would make every duplicate look novel."""
    s = re.sub(r'//[^\n]*', '', src)
    s = re.sub(r'/\*.*?\*/', '', s, flags=re.DOTALL)
    s = re.sub(r'\bmodule\s+\w+', 'module M', s, count=1)
    s = re.sub(r'\s+', ' ', s).strip()
    return hashlib.sha256(s.encode()).hexdigest()[:16]


@dataclass
class Candidate:
    block: str
    cand: str
    parent: Optional[str] = None
    rationale: str = ''
    rtl_sha: str = ''
    transform: str = ''            # taxonomy tag, e.g. 'prefix-adder'
    # emission
    nodes: Optional[int] = None
    flops: Optional[int] = None
    gates: str = ''                # PASS | FAIL:<reason>
    # measurement
    crit_ps: Optional[float] = None
    fmax_ghz: Optional[float] = None
    area_um2: Optional[float] = None
    startpoint: str = ''
    endpoint: str = ''
    # equivalence
    miter: str = ''                # PROVEN | REFUTED | ERROR
    latency_k: int = 0
    # proof
    proof: str = NOT_ATTEMPTED
    proof_wall_s: Optional[float] = None
    proof_rss_kb: Optional[int] = None
    control: str = ''              # FAILED_AS_REQUIRED | LEAKED | ''
    counterexample: str = ''
    axioms: list = field(default_factory=list)
    ts: float = field(default_factory=time.time)

    def accepted(self) -> bool:
        """A candidate counts as a result only if it is BOTH proven and its
        negative control failed.  A proof whose control also passes proves
        nothing, and must never be recorded as a win."""
        return self.proof == PROVEN and self.control == 'FAILED_AS_REQUIRED'


class Ledger:
    def __init__(self, path: str | Path, improve_tol: float = 0.01,
                 plateau_limit: int = 5, max_candidates: int = 60):
        self.path = Path(path)
        self.path.parent.mkdir(parents=True, exist_ok=True)
        self.improve_tol = improve_tol
        self.plateau_limit = plateau_limit
        self.max_candidates = max_candidates
        self.rows: list[Candidate] = []
        self._load()

    def _load(self) -> None:
        if not self.path.is_file():
            return
        for line in self.path.read_text().splitlines():
            line = line.strip()
            if not line:
                continue
            try:
                d = json.loads(line)
            except json.JSONDecodeError:
                continue          # a torn final line from a crash is not fatal
            self.rows.append(Candidate(**{k: v for k, v in d.items()
                                          if k in Candidate.__annotations__}))

    # ------------------------------------------------------------ write
    def append(self, c: Candidate) -> None:
        """Append and fsync.  Unattended runs die at arbitrary points; a ledger
        entry that is still in a buffer when the machine reboots is a candidate
        that will be re-explored."""
        self.rows.append(c)
        with self.path.open('a') as f:
            f.write(json.dumps(asdict(c), sort_keys=True) + '\n')
            f.flush()
            import os
            os.fsync(f.fileno())

    def update(self, c: Candidate) -> None:
        """Ledger is append-only: a revised record is a new line, and readers
        take the last one per (block, cand).  Keeps the audit trail intact."""
        self.append(c)

    # ------------------------------------------------------------- read
    def latest(self, block: Optional[str] = None) -> list[Candidate]:
        out: dict[str, Candidate] = {}
        for r in self.rows:
            if block and r.block != block:
                continue
            out[r.cand] = r
        return list(out.values())

    def seen_sha(self, block: str) -> set[str]:
        return {r.rtl_sha for r in self.latest(block) if r.rtl_sha}

    def is_duplicate(self, block: str, src: str) -> Optional[str]:
        """Return the name of an existing candidate with the same RTL, if any."""
        h = rtl_sha(src)
        for r in self.latest(block):
            if r.rtl_sha == h:
                return r.cand
        return None

    def best(self, block: str) -> Optional[Candidate]:
        """Fastest candidate that is actually usable: measured, and either the
        baseline or accepted (proven with a failing control)."""
        ok = [r for r in self.latest(block)
              if r.crit_ps and (r.cand == 'base' or r.accepted())]
        return min(ok, key=lambda r: r.crit_ps) if ok else None

    # ------------------------------------------------- stopping condition
    def plateau(self, block: str) -> int:
        """How many distinct candidates in a row have failed to beat the
        incumbent.  Walks in submission order, tracking the incumbent as it
        goes, so the count means what it says."""
        rows = sorted((r for r in self.latest(block) if r.crit_ps), key=lambda r: r.ts)
        best_ps, streak, seen = None, 0, set()
        for r in rows:
            if r.rtl_sha in seen:
                continue          # duplicates are not evidence of exhaustion
            seen.add(r.rtl_sha)
            if best_ps is None:
                best_ps = r.crit_ps
                continue
            if r.crit_ps < best_ps * (1.0 - self.improve_tol):
                best_ps, streak = r.crit_ps, 0
            else:
                streak += 1
        return streak

    def should_stop(self, block: str) -> tuple[bool, str]:
        n = len(self.latest(block))
        if n >= self.max_candidates:
            return True, f'budget cap: {n} candidates'
        p = self.plateau(block)
        if p >= self.plateau_limit:
            b = self.best(block)
            return True, (f'{p} distinct candidates failed to beat '
                          f'{b.crit_ps:.1f} ps' if b else f'plateau {p}')
        return False, f'plateau {p}/{self.plateau_limit}, {n} candidates'

    # --------------------------------------------------------- reporting
    def summary(self, block: str) -> str:
        rows = sorted((r for r in self.latest(block) if r.crit_ps),
                      key=lambda r: r.crit_ps)
        base = next((r for r in rows if r.cand == 'base'), None)
        out = [f'{"cand":<10}{"k":<3}{"ps":>10}{"GHz":>8}{"vs base":>9}  '
               f'{"miter":<9}{"proof":<16}transform']
        for r in rows:
            spd = f'{base.crit_ps / r.crit_ps:.3f}x' if base and r.crit_ps else '-'
            out.append(f'{r.cand:<10}{r.latency_k:<3}{r.crit_ps:>10.1f}'
                       f'{1000 / r.crit_ps:>8.3f}{spd:>9}  '
                       f'{r.miter or "-":<9}{r.proof:<16}{r.transform}')
        return '\n'.join(out)
