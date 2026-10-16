import itertools, sys
sys.path.insert(0, sys.argv[1])
from core import *
from algs import *
M1, M2 = int(sys.argv[2]), int(sys.argv[3])
def two_rounds(leader, active, b1, b2):
    if active:
        r1 = yield from ccw_bit_sending(leader, b1, M1)
        r2 = yield from ccw_bit_sending(leader, b2, M2)
        return (r1, r2)
    yield from ccw_bit_relay(leader, M1)
    yield from ccw_bit_relay(leader, M2)
    return 'relay'
bad = 0; tot = 0
for n in range(2, 4):
    for act in itertools.product([False, True], repeat=n - 1):
        active = (False,) + act
        A = [v for v in range(n) if active[v]]
        if not A: continue
        for bits in itertools.product([None, 0, 1], repeat=2 * len(A)):
            b1 = {v: bits[2 * k] for k, v in enumerate(A)}; b2 = {v: bits[2 * k + 1] for k, v in enumerate(A)}
            procs = [Proc(lambda v=v: two_rounds(v == 0, active[v], b1.get(v), b2.get(v))) for v in range(n)]
            seen, finals, mx = explore(procs, max_states=500000)
            tot += 1
            for c, info in finals:
                ok = all(i[0] == 'done' for i in info) and quiescent(c, info)
                if ok:
                    for k, v in enumerate(A):
                        w1 = A[(k + 1) % len(A)] if M1 == 0 else A[(k - 1) % len(A)]
                        w2 = A[(k + 1) % len(A)] if M2 == 0 else A[(k - 1) % len(A)]
                        if info[v][2] != (b1[w1], b2[w2]): ok = False
                if not ok:
                    bad += 1
                    if bad <= 2: print('FAIL', n, active, b1, b2, 'hist', c, [i[0] for i in info], [i[2] for i in info])
print('M1', M1, 'M2', M2, 'cases', tot, 'bad finals', bad)
