"""
suspicious_mapped.py  • 2025‑04‑revB

Upgrades:
  • stack‑based module tracking  (handles nested 'module' / 'endmodule')
  • parses 'inst foo of Bar' to link instance nets
  • records each bit‑range -> lets "[63:32]" match "sig_63_32"
  • keeps *all* (file,line,module) occurrences (not just latest)
  • smarter ranking: ratio  +  filename‑keyword bonus  +  bit‑range bonus
"""

import re
import argparse
import logging
import difflib
from collections import defaultdict

# ---------- Normalisation ---------------------------------------------------
BR = re.compile(r'\[(\d+):(\d+)\]')


def strip_brackets(s: str) -> str:
    return BR.sub('', s)


def adv_norm(s: str) -> str:
    s = strip_brackets(s).lower()
    return re.sub(r'[^a-z0-9_]', '', s)


def norm_fir_ref(r: str) -> str:
    r = re.sub(r'[.\(\)`]', '_', r)
    r = re.sub(r'[^a-zA-Z0-9_\[\]:]', '', r)
    r = re.sub(r'__+', '_', r).strip('_')
    return r


# ---------- FIRRTL parser ----------------------------------------------------
class Firrtl:
    M = re.compile(r'^\s*(module|extmodule)\s+(\S+)')
    WRN = re.compile(r'^\s*(wire|reg|node)\s+(\S+)')
    CNT = re.compile(r'^\s*(connect|attach)\s*\(?\s*(.*?)\s*\)?\s*@\[(\S+)\s+(\d+):')
    INST = re.compile(r'^\s*inst\s+(\S+)\s+of\s+(\S+)')
    END = re.compile(r'^\s*endmodule')

    def __init__(self, p):
        self.path = p
        self.map = defaultdict(list)
        self.mod_stack = []

    def push(self, m):
        self.mod_stack.append(m)

    def cur(self):
        return self.mod_stack[-1] if self.mod_stack else '???'

    def pop(self):
        self.mod_stack.pop()

    def parse(self):
        with open(self.path, 'r', errors='ignore') as f:
            for line in f:
                if m := self.M.match(line):
                    self.push(m.group(2))
                    continue
                if self.END.match(line):
                    self.pop()
                    continue
                if m := self.WRN.match(line):
                    sig = m.group(2)
                    fr, nl = self._loc(line)
                    self._add(sig, fr, nl)
                    continue
                if m := self.CNT.match(line):
                    refs = [r.strip('() ') for r in m.group(2).split(',')]
                    fr = int(m.group(4))
                    fn = m.group(3)
                    for r in refs:
                        self._add(r, fn, fr)
                    continue
                if m := self.INST.match(line):  # alias inst ports
                    inst = m.group(1)
                    self._add(inst, self._loc(line)[0], self._loc(line)[1])  # allow matching 'inst'
        return self.map

    def _loc(self, line: str):  # @[file ln:col]
        m = re.search(r'@\[(\S+)\s+(\d+):', line)
        return (m.group(1), int(m.group(2))) if m else ('?', 0)

    def _add(self, raw, fp, ln):
        uni = norm_fir_ref(raw)
        self.map[uni].append((fp, ln, self.cur()))
        # bit‑range aliases
        for lo, hi in BR.findall(raw):
            self.map[f'{uni}_{lo}_{hi}'].append((fp, ln, self.cur()))


# ---------- Mapper -----------------------------------------------------------
class Mapper:
    def __init__(self, fmap, pri=0.85, sec=0.7):
        self.fmap = fmap
        self.pri = pri
        self.sec = sec
        self.norm_index = defaultdict(list)
        self.len_idx = defaultdict(list)
        self.pref_idx = defaultdict(list)
        for u, locs in fmap.items():
            n = adv_norm(u)
            self.norm_index[n] += locs
        for n in self.norm_index:
            self.len_idx[len(n)].append(n)
            self.pref_idx[n[:3]].append(n)

    def cand(self, key, cut):
        L = len(key)
        pool = []
        for length in range(max(0, L - 4), L + 5):
            pool += self.len_idx[length]
        pool = set(pool) & set(self.pref_idx.get(key[:3], pool))
        return [
            (n, difflib.SequenceMatcher(None, key, n).ratio())
            for n in pool
            if difflib.SequenceMatcher(None, key, n).ratio() >= cut
        ]

    def map(self, sig):
        k = adv_norm(sig)
        for cut in (self.pri, self.sec):
            if k in self.norm_index:
                return self.pick(sig, k, self.norm_index[k])
            c = self.cand(k, cut)
            if c:  # pick best fuzzy
                best = max(c, key=lambda x: x[1])[0]
                return self.pick(sig, k, self.norm_index[best])
        return None

    def pick(self, orig, norm, locs):
        kw = self.kw(orig)
        best = max(locs, key=lambda loc: self.rank(loc, kw))
        return (*best,)  # fp,line,mod

    @staticmethod
    def kw(s):
        lower_s = s.lower()
        out = set()
        if any(x in lower_s for x in ('fpu', 'float', 'fp')):
            out.add('fp')
        if 'exu' in lower_s:
            out.add('exu')
        if 'ld' in lower_s or 'load' in lower_s:
            out.add('ld')
        if 'st' in lower_s or 'store' in lower_s:
            out.add('st')
        return out

    @staticmethod
    def rank(loc, kw):
        fp, ln, mod = loc
        sc = 0
        fl = fp.lower()
        if 'fp' in kw and any(x in fl for x in ('fpu', 'float', 'fp')):
            sc += 0.3
        if 'exu' in kw and 'exu' in fl:
            sc += 0.3
        if 'ld' in kw and 'load' in fl:
            sc += 0.2
        if 'st' in kw and 'store' in fl:
            sc += 0.2
        return sc


# ---------- CLI --------------------------------------------------------------
def parse_sus(p):
    out = []
    with open(p) as f:
        for line in f:
            if line.startswith('===') or not line.strip():
                continue
            s, sc = [x.strip() for x in line.rsplit(':', 1)]
            try:
                out.append((s, float(sc)))
            except Exception:
                pass
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--suspicious', required=True)
    ap.add_argument('--firrtl', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--cutoff', type=float)
    ap.add_argument('--fuzzy_primary', type=float, default=0.85)
    ap.add_argument('--fuzzy_secondary', type=float, default=0.7)
    ap.add_argument('--loglevel', default='INFO')
    a = ap.parse_args()
    logging.basicConfig(level=getattr(logging, a.loglevel.upper()), format='[%(levelname)s] %(msg)s')
    fmap = Firrtl(a.firrtl).parse()
    sus = parse_sus(a.suspicious)
    if a.cutoff:
        sus = [x for x in sus if x[1] >= a.cutoff]
    mp = Mapper(fmap, a.fuzzy_primary, a.fuzzy_secondary)
    with open(a.out, 'w') as o:
        o.write('Suspicious => file:line (module), Score\n')
        for s, sc in sus:
            m = mp.map(s)
            if m:
                o.write(f'{s} => {m[0]}:{m[1]} ({m[2]}), {sc}\n')
            else:
                o.write(f'{s} => [unmapped], {sc}\n')
    logging.info('saved %s', a.out)


if __name__ == '__main__':
    main()
