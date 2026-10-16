import itertools, sys
sys.path.insert(0, sys.argv[1])
from core import *
from algs import *
NMAX = int(sys.argv[2])
for m in (0, 1):
  for n in range(1, NMAX + 1):
    cnt = 0; mxall = 0; worst = 0
    for act in itertools.product([False, True], repeat=n - 1):
        active = (True,) + act
        A = [v for v in range(n) if active[v]]
        for bits in itertools.product([None, 0, 1], repeat=len(A)):
            bit = dict(zip(A, bits))
            procs = [Proc((lambda v=v: ccw_bit_sending(v == 0, bit[v], m)) if active[v]
                          else (lambda v=v: ccw_bit_relay(v == 0, m))) for v in range(n)]
            seen, finals, mx = explore(procs)
            mxall = max(mxall, mx)
            for c, info in finals:
                assert all(i[0] == 'done' for i in info), (n, active, bit, c, info)
                assert quiescent(c, info), (n, active, bit)
                for k, v in enumerate(A):
                    # CCW (m=0): receive from cw active neighbour; CW (m=1): from ccw neighbour
                    w = A[(k + 1) % len(A)] if m == 0 else A[(k - 1) % len(A)]
                    assert info[v][2] == bit[w], (m, n, active, bit, v, info[v][2])
            cnt += 1
            worst = max(worst, len(seen))
    print('m', m, 'n', n, 'ok', cnt, 'maxsent', mxall, '6n', 6 * n, 'maxstates', worst, flush=True)
