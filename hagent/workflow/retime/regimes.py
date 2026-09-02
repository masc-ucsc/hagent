"""Per-output latency analysis of an emitted model.

A pipelined block is usually MIXED latency, not uniformly delayed.  The CVA6 ALU
candidate `p1` registers `result_o` but deliberately leaves `branch_res_o`
combinational, because a one-cycle branch resolution is a real microarchitectural
cost.  So "is this candidate k=0 or k=1?" is the wrong question -- each OUTPUT
has its own regime, and a prover that assumes one regime for the whole module
either proves a false statement about the combinational output or fails to prove
the true one about the registered output.

The regime is read off the emitted model by dataflow, not guessed:

    def <top>_comb (i : ...) (s : ...) : <top>_out :=
      let n_123 : BitVec 64 := ... i.in_operand_a_i ...
      let n_456 : BitVec 1  := ... s.st_q_less ...
      { out_x := ... n_123 ..., out_y := ... n_456 ... }

An output whose transitive cone touches any `i.in_*` is COMBINATIONAL in this
cycle (k=0).  One that reads only `s.*` is fed entirely from registers, so its
value belongs to an earlier input (k>=1).  This is the same structural-fact-not-
judgement rule used for the module-level flop count.
"""

from __future__ import annotations

import re
from typing import Optional

_LET = re.compile(r'^\s*let\s+(n_\d+)\s*:[^:=]*:=\s*(.*)$')
_REC = re.compile(r'^\s*\{\s*(out_.*)\}\s*$')
_REF = re.compile(r'\bn_\d+\b')


def _comb_body(src: str, top: str) -> Optional[list[str]]:
    m = re.search(rf'^def {re.escape(top)}_comb\b.*$', src, re.M)
    if not m:
        return None
    rest = src[m.end():]
    stop = re.search(rf'^def {re.escape(top)}_(next|step)\b', rest, re.M)
    return (rest[:stop.start()] if stop else rest).splitlines()


def output_regimes(src: str, top: str) -> dict[str, int]:
    """Map each output field to 0 (combinational this cycle) or 1 (registered).

    Returns {} if the model has no state at all -- then every output is k=0 by
    construction and there is nothing to analyse."""
    lines = _comb_body(src, top)
    if lines is None:
        return {}

    defs: dict[str, str] = {}
    record = None
    for ln in lines:
        m = _LET.match(ln)
        if m:
            defs[m.group(1)] = m.group(2)
            continue
        r = _REC.match(ln)
        if r:
            record = r.group(1)
    if record is None:
        return {}

    # Split the record on top-level commas: `out_x := e1, out_y := e2`
    fields: dict[str, str] = {}
    depth = 0
    cur = ''
    for ch in record:
        if ch in '([{':
            depth += 1
        elif ch in ')]}':
            depth -= 1
        if ch == ',' and depth == 0:
            fields.setdefault(*_split_assign(cur))
            cur = ''
        else:
            cur += ch
    if cur.strip():
        fields.setdefault(*_split_assign(cur))

    out = {}
    for f, expr in fields.items():
        out[f] = 0 if _touches_input(expr, defs) else 1
    return out


def _split_assign(s: str) -> tuple[str, str]:
    if ':=' in s:
        k, v = s.split(':=', 1)
        return k.strip(), v.strip()
    return s.strip(), ''


def _touches_input(expr: str, defs: dict[str, str]) -> bool:
    """Transitive: does this expression's cone reference any `i.in_*`?"""
    seen: set[str] = set()
    stack = [expr]
    while stack:
        e = stack.pop()
        if 'i.in_' in e:
            return True
        for n in _REF.findall(e):
            if n not in seen:
                seen.add(n)
                if n in defs:
                    stack.append(defs[n])
    return False
