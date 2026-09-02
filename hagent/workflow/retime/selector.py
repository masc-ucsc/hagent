"""The block-selector agent: decide which block to retime next.

Reads livehd's own coverage record rather than guessing.  `pass/lean/
CVA6_COVERAGE_PLAN.md` already maintains a live table of which blocks have been
proven equal to their certificate, with node/flop/width/wall numbers -- that is
exactly the prerequisite list, because a block whose fast model has never been
proven against its certificate has no anchored reference to retime against.

Ranking is by expected payoff, using the finding that fell out of the coverage
data: **proof cost tracks WIDTH, not node count.**  `pmp` (5,344 nodes, 434 b)
took 6.2 h while `compressed_decoder` (1,946 nodes, 33 b) took 3 minutes -- about
0.32 s/node at 127 bits versus 9.1 s/node at 513 bits.  So a wide block is both
the most promising (long carry/compare chains to shorten) and the most expensive
to prove, and the selector reports both rather than optimizing one blindly.
"""

from __future__ import annotations

import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Optional


@dataclass
class BlockInfo:
    name: str
    nodes: Optional[int] = None
    flops: Optional[int] = None
    max_width: Optional[int] = None
    proven: bool = False
    have_descriptor: bool = False
    note: str = ''

    @property
    def combinational(self) -> bool:
        return self.flops == 0

    def score(self) -> float:
        """Expected payoff.  Width dominates: it is where the serial chains are,
        and every transformation that actually paid on the ALU (prefix adder,
        prefix comparator) shortens one.  Combinational blocks are preferred
        because their equivalence is a plain equality that a miter decides
        completely, whereas a block with real reset-bearing flops needs a
        simulation relation the prover does not yet generate."""
        if not self.proven:
            return -1.0                      # no anchored reference; not eligible
        w = self.max_width or 32
        s = float(w)
        if self.combinational:
            s *= 1.5
        if self.have_descriptor:
            s *= 1.2                         # cheap to start
        return s


_ROW = re.compile(r'^\|\s*`([a-z0-9_]+)`\s*\|\s*([\d,]+)\s*\|\s*(\d+)\s*\|\s*(\d+)?')


def parse_coverage(md: str) -> list[BlockInfo]:
    """Parse the 'Proven' table of CVA6_COVERAGE_PLAN.md."""
    out = []
    for line in md.splitlines():
        m = _ROW.match(line.strip())
        if not m:
            continue
        name, nodes, flops, w = m.groups()
        out.append(BlockInfo(name=name, nodes=int(nodes.replace(',', '')),
                             flops=int(flops), max_width=int(w) if w else None,
                             proven=True))
    return out


def recent_changes(livehd: Path, since: str = '30 days ago') -> list[str]:
    """Blocks touched by recent livehd commits -- a newly-proven block is a
    newly-eligible one, so the loop should notice without being told."""
    try:
        r = subprocess.run(
            ['git', 'log', f'--since={since}', '--oneline', '--',
             'pass/lean/', 'scripts/cva6_module_wrappers/'],
            cwd=livehd, capture_output=True, text=True, timeout=60)
        return [l for l in r.stdout.splitlines() if l.strip()]
    except (subprocess.SubprocessError, OSError):
        return []


def select(livehd_root: str | Path, blocks_dir: str | Path,
           done: Optional[set] = None) -> tuple[Optional[BlockInfo], list[BlockInfo]]:
    """Return (next block, full ranked list)."""
    livehd = Path(livehd_root)
    plan = livehd / 'pass' / 'lean' / 'CVA6_COVERAGE_PLAN.md'
    infos = parse_coverage(plan.read_text()) if plan.is_file() else []

    have = {p.stem.split('_', 1)[-1] for p in Path(blocks_dir).glob('*.yaml')}
    for b in infos:
        short = b.name.replace('cva6_', '').replace('_gate', '').replace('_export', '')
        b.have_descriptor = short in have or b.name in have
        if b.max_width is None:
            b.note = 'width unknown; cost estimate unreliable'

    ranked = sorted(infos, key=lambda b: b.score(), reverse=True)
    done = done or set()
    nxt = next((b for b in ranked
                if b.score() > 0 and b.name not in done), None)
    return nxt, ranked


def report(livehd_root: str | Path, blocks_dir: str | Path,
           done: Optional[set] = None) -> str:
    nxt, ranked = select(livehd_root, blocks_dir, done)
    lines = [f'{"block":<32}{"nodes":>7}{"flops":>7}{"width":>7}{"score":>8}  descriptor']
    for b in ranked:
        lines.append(f'{b.name:<32}{b.nodes or 0:>7}{b.flops if b.flops is not None else -1:>7}'
                     f'{b.max_width or 0:>7}{b.score():>8.0f}  '
                     f'{"yes" if b.have_descriptor else "-"}'
                     f'{"  " + b.note if b.note else ""}')
    lines.append(f'\nnext: {nxt.name if nxt else "(none eligible)"}')
    return '\n'.join(lines)
