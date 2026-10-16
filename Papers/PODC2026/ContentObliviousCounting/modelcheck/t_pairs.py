import itertools, sys
sys.path.insert(0, sys.argv[1])
from core import *
from algs import *
LEADER_ACTIVE = sys.argv[2] == '1'
def proc(kind, leader, active, b):
    if kind == 'OR':
        return (yield from compute_or(leader, bool(b)))
    m = 0 if kind == 'CCW' else 1
    if active: return (yield from ccw_bit_sending(leader, b, m))
    yield from ccw_bit_relay(leader, m); return 'relay'
def seq(k1, k2, leader, active, b1, b2):
    r1 = yield from proc(k1, leader, active, b1)
    r2 = yield from proc(k2, leader, active, b2)
    return (r1, r2)
def expect(kind, A, act, b, v):
    if kind == 'OR': return any(bool(b.get(w)) for w in A)
    if not act[v]: return 'relay'
    k = A.index(v)
    w = A[(k + 1) % len(A)] if kind == 'CCW' else A[(k - 1) % len(A)]
    return b[w]
for k1 in ['OR', 'CW', 'CCW']:
  for k2 in ['OR', 'CW', 'CCW']:
    bad = 0; tot = 0; skipped = 0
    for n in range(1, 4):
      for act in itertools.product([False, True], repeat=n):
        if LEADER_ACTIVE and not act[0]: continue
        A = [v for v in range(n) if act[v]]
        if not A: continue
        for bits in itertools.product([None, 0, 1], repeat=2 * len(A)):
            b1 = {v: bits[2 * k] for k, v in enumerate(A)}; b2 = {v: bits[2 * k + 1] for k, v in enumerate(A)}
            procs = [Proc(lambda v=v: seq(k1, k2, v == 0, act[v], b1.get(v), b2.get(v))) for v in range(n)]
            try:
                seen, finals, mx = explore(procs, max_states=1500000)
            except RuntimeError:
                skipped += 1; continue
            tot += 1
            for c, info in finals:
                ok = all(i[0] == 'done' for i in info) and quiescent(c, info)
                ok = ok and all(info[v][2] == (expect(k1, A, act, b1, v), expect(k2, A, act, b2, v)) for v in range(n))
                if not ok: bad += 1
    print(k1, k2, 'cases', tot, 'bad', bad, 'skipped', skipped, flush=True)
