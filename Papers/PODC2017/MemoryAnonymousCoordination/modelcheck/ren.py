"""Explicit-state model checker for Fig. 3 (renaming) of Taubenfeld PODC'17.

Over-approximation of memory anonymity: each collect reads the unread registers in any order
(adversary picks the next register).  Line 9 / line 15 "arbitrary index": all choices.
Safety: returned names distinct and adaptive (name <= #started processes).
"""
import sys
from collections import deque

N = int(sys.argv[1]) if len(sys.argv) > 1 else 3
M = 2 * N - 1
FIXED_ORDER = len(sys.argv) > 2 and sys.argv[2] == 'fixed'
MAXSTATES = int(sys.argv[3]) if len(sys.argv) > 3 else 5_000_000
IDS = list(range(1, N + 1))
EMPTY = (0, 0, 0, ())

# local state: (pc, pref, rnd, hist, view, out)
# pc: 'S' not started, 'R' collecting, ('W',k) write pending at physical k with tuple, 'D' done
# view: tuple of M entries or None (unread)

def init():
    regs = tuple([EMPTY] * M)
    locs = tuple(('S', 0, 1, (), None, 0) for _ in IDS)
    return (regs, locs)

def after_collect(i, pref, rnd, hist, view):
    """Local computation after a complete collect (lines 5-15). Returns list of
    (kind, data): ('ret', v) or ('write', k, tuple, pref, rnd, hist)."""
    res = []
    for e in view:
        for (a, v) in e[3]:
            if a == i:
                return [('ret', v)]  # line 5-6 (any such v; take the first)
    mytemp = max(e[2] for e in view)
    cands = []
    if mytemp > rnd:
        for k in range(M):
            if view[k][2] == mytemp:
                cands.append((view[k][1], view[k][3], view[k][2]))
    else:
        cands.append((pref, hist, rnd))
    out = []
    for (p, h, r) in set(cands):
        cnt = {}
        for e in view:
            if e[2] == r and e[1] != 0:
                cnt[e[1]] = cnt.get(e[1], 0) + 1
        for v, c in cnt.items():
            if c >= N:
                p = v
        tup = (i, p, r, h)
        ks = [k for k in range(M) if view[k] != tup]
        if not ks:
            out.append(('nowrite', tup, p, r, h))
        for k in ks:
            out.append(('write', k, tup, p, r, h))
    return out

def finish_inner(i, p, r, h, view, tup):
    """until check (line 17) with view; returns new local state."""
    if all(e == tup for e in view):
        if p == i:
            return ('D', p, r, h, None, r)
        h2 = tuple(sorted(set(h) | {(p, r)}))
        r2 = r + 1
        if r2 == N:
            return ('D', p, r2, h2, None, N)
        return ('R', i, r2, h2, tuple([None] * M), 0)  # line 2: mypref := i, start collect
    return ('R', p, r, h, tuple([None] * M), 0)

def succ(state):
    regs, locs = state
    for idx, i in enumerate(IDS):
        pc, pref, rnd, hist, view, out = locs[idx]
        if pc == 'D':
            continue
        if pc == 'S':
            nl = ('R', i, 1, (), tuple([None] * M), 0)
            yield (idx, (regs, locs[:idx] + (nl,) + locs[idx + 1:]))
            continue
        if pc == 'R':
            unread = [k for k in range(M) if view[k] is None]
            if FIXED_ORDER:
                unread = unread[:1]
            for k in unread:
                v2 = view[:k] + (regs[k],) + view[k + 1:]
                if all(e is not None for e in v2):
                    for act in after_collect(i, pref, rnd, hist, v2):
                        if act[0] == 'ret':
                            nl = ('D', pref, rnd, hist, None, act[1])
                        elif act[0] == 'nowrite':
                            _, tup, p, r, h = act
                            nl = finish_inner(i, p, r, h, v2, tup)
                        else:
                            _, kk, tup, p, r, h = act
                            nl = (('W', kk, tup, v2), p, r, h, v2, 0)
                        yield (idx, (regs, locs[:idx] + (nl,) + locs[idx + 1:]))
                else:
                    nl = ('R', pref, rnd, hist, v2, 0)
                    yield (idx, (regs, locs[:idx] + (nl,) + locs[idx + 1:]))
            continue
        # write pending
        _, kk, tup, v2 = pc
        regs2 = regs[:kk] + (tup,) + regs[kk + 1:]
        nl = finish_inner(i, pref, rnd, hist, v2, tup)
        yield (idx, (regs2, locs[:idx] + (nl,) + locs[idx + 1:]))

def bad(state):
    regs, locs = state
    started = sum(1 for l in locs if l[0] != 'S')
    outs = [l[5] for l in locs if l[0] == 'D']
    if len(set(outs)) != len(outs):
        return 'duplicate names %s' % outs
    for o in outs:
        if not (1 <= o <= started):
            return 'name %d with %d participants' % (o, started)
    return None

def main():
    s0 = init()
    parent = {s0: None}
    q = deque([s0])
    while q:
        s = q.popleft()
        b = bad(s)
        if b:
            print('VIOLATION', b)
            tr = []
            while s is not None:
                tr.append(s)
                s = parent[s]
            for st in reversed(tr):
                print(st)
            return
        for (idx, t) in succ(s):
            if t not in parent:
                parent[t] = s
                q.append(t)
                if len(parent) > MAXSTATES:
                    print('state limit', len(parent))
                    return
    print('no violation; states', len(parent))

main()
