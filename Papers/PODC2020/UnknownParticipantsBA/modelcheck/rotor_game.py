# Abstract adversary game for the rotor-coordinator candidate sets (see ../differencies.md).
# Usage: python3 -I rotor_game.py lemma4 <g> <f> <horizon>   |   python3 -I rotor_game.py worst <g> <f> <horizon>
# Abstract adversary game for the rotor-coordinator C-dynamics.
# correct nodes 0..g-1, faulty ids: positions in sorted order (interleaving).
# Each correct node's C = all correct ids + subset of faulty ids.
# Constraints: monotone; relay: if p in some C at round r then p in every C at round r+1.
# Selection at round r: sorted(C)[r % |C|].
# Good round: all selections equal and correct.
# Q1: worst-case first good round (no termination).
# Q2: is there a run where some node reselects (terminates) at round rt with no good round <= rt ?
import sys, itertools
from functools import lru_cache

def solve(g, f, H):
    best = (-1, None)
    lemma4cex = None
    # orders: assign to each faulty id a "slot" among sorted list; build id lists
    total = g + f
    for fpos in itertools.combinations(range(total), f):
        ids = list(range(total))
        faulty = set(fpos)  # ids which are faulty (labels = position)
        flist = sorted(faulty)
        def sel(Cf, r):
            C = sorted([i for i in ids if i not in faulty] + list(Cf))
            return C[r % len(C)]
        # state: tuple of frozensets (per node), sorted for symmetry -> but selections history per node matter for Q2.
        # Q1: memo DFS maximizing first good round
        @lru_cache(maxsize=None)
        def worst(r, state):
            # state: sorted tuple of frozensets; returns max first good round >= r (H if none up to H)
            if r >= H: return H
            # choose additions this round: pending ids (in some but not all) must be added to all
            present = set().union(*state)
            pending = {p for p in present if any(p not in s for s in state)}
            newc = [p for p in flist if p not in present]
            res = -1
            # each new id: subset of nodes adding it (mask)
            for masks in itertools.product(range(1 << g), repeat=len(newc)):
                ns = []
                for i, s in enumerate(state):
                    s2 = set(s) | pending
                    for p, m in zip(newc, masks):
                        if m >> i & 1: s2.add(p)
                    ns.append(frozenset(s2))
                sels = [sel(s, r) for s in ns]
                good = len(set(sels)) == 1 and sels[0] not in faulty
                if good:
                    v = r
                else:
                    v = worst(r + 1, tuple(sorted(ns, key=lambda x: sorted(x))))
                res = max(res, v)
                if res >= H: return H
            return res
        # initial: before round 0, C empty; at round 0 all correct ids added; faulty additions at round 0 free.
        init = tuple(frozenset() for _ in range(g))
        # round 0: no pending
        w = worst(0, init)
        if w > best[0]:
            best = (w, fpos)
    return best

def lemma4(g, f, H):
    # search for: node 0 terminates (reselects) at round rt, with no good round in [0, rt].
    total = g + f
    for fpos in itertools.combinations(range(total), f):
        faulty = set(fpos); flist = sorted(faulty)
        corr = [i for i in range(total) if i not in faulty]
        def sel(Cf, r):
            C = sorted(corr + list(Cf)); return C[r % len(C)]
        sys.setrecursionlimit(10000)
        def dfs(r, state, hist0, trace):
            if r >= H: return None
            present = set().union(*state)
            pending = {p for p in present if any(p not in s for s in state)}
            newc = [p for p in flist if p not in present]
            for masks in itertools.product(range(1 << g), repeat=len(newc)):
                ns = []
                for i, s in enumerate(state):
                    s2 = set(s) | pending
                    for p, m in zip(newc, masks):
                        if m >> i & 1: s2.add(p)
                    ns.append(frozenset(s2))
                sels = [sel(s, r) for s in ns]
                good = len(set(sels)) == 1 and sels[0] not in faulty
                if good: continue
                tr = trace + [(r, [sorted(s) for s in ns], sels)]
                if sels[0] in hist0:
                    return (fpos, tr)
                out = dfs(r + 1, tuple(ns), hist0 | {sels[0]}, tr)
                if out: return out
            return None
        out = dfs(0, tuple(frozenset() for _ in range(g)), frozenset(), [])
        if out: return out
    return None

if __name__ == '__main__':
    mode = sys.argv[1]
    g, f, H = map(int, sys.argv[2:5])
    if mode == 'worst':
        print(g, f, solve(g, f, H))
    else:
        print(g, f, lemma4(g, f, H))
