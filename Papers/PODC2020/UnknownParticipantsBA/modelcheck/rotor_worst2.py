# Worst-case first good iteration of the rotor (no termination), symmetric search.
# Usage: python3 -I rotor_worst2.py <g> <f> <horizon>
import sys, itertools
from functools import lru_cache
def solve(g, f, H):
    total = g + f; best = (-1, None)
    for fpos in itertools.combinations(range(total), f):
        faulty = set(fpos); flist = sorted(faulty)
        corr = [i for i in range(total) if i not in faulty]
        @lru_cache(maxsize=None)
        def sel(Cf, r):
            C = sorted(corr + list(Cf)); return C[r % len(C)]
        @lru_cache(maxsize=None)
        def worst(r, state):
            if r >= H: return H
            present = frozenset().union(*state)
            newc = [p for p in flist if p not in present]
            subsets = [frozenset(c) for k in range(len(newc)+1) for c in itertools.combinations(newc, k)]
            res = -1
            for choice in itertools.combinations_with_replacement(range(len(subsets)), g):
                ns = tuple(sorted((present | subsets[c] for c in choice), key=lambda x: sorted(x)))
                # NOTE: pending ids (present in some) are added to all: present | ...
                sels = [sel(s, r) for s in ns]
                if len(set(sels)) == 1 and sels[0] not in faulty: v = r
                else: v = worst(r + 1, ns)
                if v > res: res = v
                if res >= H: return H
            return res
        # careful: at round r nodes must hold all ids present at round r-1 (relay) -> state passed = C at r-1.
        w = worst(0, tuple(frozenset() for _ in range(g)))
        if w > best[0]: best = (w, fpos)
    return best
g, f, H = map(int, sys.argv[1:4]); print(g, f, solve(g, f, H))
