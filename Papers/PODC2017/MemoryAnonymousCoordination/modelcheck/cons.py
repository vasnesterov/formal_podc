"""Model checker for Fig. 2 (obstruction-free consensus) of Taubenfeld PODC'17.
Usage: cons.py N inputs(comma) [any|fixed] [skip|write]
any   = each collect reads unread registers in any order (over-approximation), fixed = order 0..M-1.
skip  = when the view is all (i,pref), no write (line 6 has no index); write = write anywhere."""
import sys
from collections import deque

N = int(sys.argv[1])
M = 2 * N - 1
INPUTS = [int(x) for x in sys.argv[2].split(',')]
ANY = sys.argv[3] == 'any'
WRITE_ALWAYS = sys.argv[4] == 'write'
IDS = list(range(1, len(INPUTS) + 1))
EMPTY = (0, 0)

def succ(state):
    regs, locs = state
    for idx, i in enumerate(IDS):
        pc, pref, view, out = locs[idx]
        def mk(nl, nr=regs):
            return (nr, locs[:idx] + (nl,) + locs[idx + 1:])
        if pc == 'D':
            continue
        if pc == 'S':
            yield mk(('R', INPUTS[idx], tuple([None] * M), None))
            continue
        if pc == 'R':
            unread = [k for k in range(M) if view[k] is None]
            if not ANY:
                unread = unread[:1]
            for k in unread:
                v2 = view[:k] + (regs[k],) + view[k + 1:]
                if any(e is None for e in v2):
                    yield mk(('R', pref, v2, None))
                    continue
                p = pref
                cnt = {}
                for e in v2:
                    if e[1] != 0:
                        cnt[e[1]] = cnt.get(e[1], 0) + 1
                for v, c in cnt.items():
                    if c >= N:
                        p = v
                tup = (i, p)
                ks = [kk for kk in range(M) if v2[kk] != tup]
                done = not ks
                if done and not WRITE_ALWAYS:
                    yield mk(('D', p, None, p))
                    continue
                if done:
                    ks = list(range(M))
                for kk in ks:
                    yield mk((('W', kk, done), p, None, None))
            continue
        _, kk, done = pc
        nr = regs[:kk] + ((i, pref),) + regs[kk + 1:]
        if done:
            yield mk(('D', pref, None, pref), nr)
        else:
            yield mk(('R', pref, tuple([None] * M), None), nr)

def bad(state):
    regs, locs = state
    outs = set(l[3] for l in locs if l[0] == 'D')
    if len(outs) > 1:
        return 'disagreement %s' % outs
    started = set(INPUTS[k] for k, l in enumerate(locs) if l[0] != 'S')
    if not outs <= started:
        return 'validity'
    return None

s0 = (tuple([EMPTY] * M), tuple(('S', 0, None, None) for _ in IDS))
parent = {s0: None}
q = deque([s0])
while q:
    s = q.popleft()
    b = bad(s)
    if b:
        print('VIOLATION', b)
        tr = []
        while s is not None:
            tr.append(s); s = parent[s]
        for st in reversed(tr):
            print(st)
        sys.exit()
    for t in succ(s):
        if t not in parent:
            parent[t] = s
            q.append(t)
            if len(parent) > 6_000_000:
                print('state limit'); sys.exit()
print('no violation; states', len(parent))
