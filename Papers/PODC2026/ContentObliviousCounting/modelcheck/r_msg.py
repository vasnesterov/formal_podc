import itertools, sys, random
sys.path.insert(0, sys.argv[1])
from core import *
from algs import *
NMAX = int(sys.argv[2]); LMAX = int(sys.argv[3]); RUNS = int(sys.argv[4])
rng = random.Random(7)
for n in range(1, NMAX + 1):
    for r in range(RUNS):
        active = [True] + [rng.random() < 0.6 for _ in range(n - 1)]
        A = [v for v in range(n) if active[v]]
        rm = lambda: tuple(rng.randint(0, 1) for _ in range(rng.randint(0, LMAX)))
        mcw = {v: rm() for v in A}; mccw = {v: rm() for v in A}
        L = max([len(x) for x in mcw.values()] + [len(x) for x in mccw.values()])
        procs = [Proc((lambda v=v: msg_exchange(v == 0, mcw[v], mccw[v])) if active[v]
                      else (lambda v=v: msg_relay(v == 0))) for v in range(n)]
        bias = [[rng.random() ** 3 + 1e-3, rng.random() ** 3 + 1e-3] for _ in range(n)]
        c, info, mx = random_run(procs, rng, bias if r % 2 else None)
        assert mx <= 15 * n * L + 3 * n, (n, active, mx)
        assert all(i[0] == 'done' for i in info), (n, active, mcw, mccw, c)
        assert quiescent(c, info)
        for k, v in enumerate(A):
            cw = A[(k + 1) % len(A)]; ccw = A[(k - 1) % len(A)]
            assert info[v][2] == (mccw[cw], mcw[ccw]), (n, active, v, info[v][2])
    print('n', n, 'ok', flush=True)
