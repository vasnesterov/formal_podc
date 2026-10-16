import itertools, sys
sys.path.insert(0, sys.argv[1])
from core import *
from algs import *
def two_rounds(leader, active, b1, b2):
    if active:
        r1 = yield from ccw_bit_sending(leader, b1, 0)
        r2 = yield from ccw_bit_sending(leader, b2, 0)
        return (r1, r2)
    yield from ccw_bit_relay(leader, 0)
    yield from ccw_bit_relay(leader, 0)
    return 'relay'
bad = 0
for n in range(2, 5):
    for act in itertools.product([False, True], repeat=n - 1):
        active = (False,) + act
        A = [v for v in range(n) if active[v]]
        if not A: continue
        for bits in itertools.product([None, 0, 1], repeat=2 * len(A)):
            b1 = {v: bits[2 * k] for k, v in enumerate(A)}; b2 = {v: bits[2 * k + 1] for k, v in enumerate(A)}
            procs = [Proc(lambda v=v: two_rounds(v == 0, active[v], b1.get(v), b2.get(v))) for v in range(n)]
            seen, finals, mx = explore(procs)
            for c, info in finals:
                ok = all(i[0] == 'done' for i in info) and quiescent(c, info)
                if ok:
                    for k, v in enumerate(A):
                        w = A[(k + 1) % len(A)]
                        if info[v][2] != (b1[w], b2[w]): ok = False
                if not ok:
                    bad += 1
                    if bad <= 3: print('FAIL', n, active, b1, b2, 'hist', c, [i[0] for i in info], [i[2] for i in info])
print('bad finals', bad)
