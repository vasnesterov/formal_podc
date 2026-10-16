import itertools, sys, random
sys.path.insert(0, sys.argv[1])
from core import *
from algs import *
NMAX = int(sys.argv[2]); LMAX = int(sys.argv[3]); SAMPLES = int(sys.argv[4])
msgs = [()] + [tuple(b) for l in range(1, LMAX + 1) for b in itertools.product([0, 1], repeat=l)]
random.seed(1)
for n in range(1, NMAX + 1):
    cases = []
    for act in itertools.product([False, True], repeat=n - 1):
        active = (True,) + act
        A = [v for v in range(n) if active[v]]
        allm = list(itertools.product(msgs, repeat=2 * len(A)))
        if len(allm) > SAMPLES: allm = random.sample(allm, SAMPLES)
        for ms in allm:
            cases.append((active, A, ms))
    worst = 0; maxratio = 0
    for active, A, ms in cases:
        mcw = {v: ms[2 * k] for k, v in enumerate(A)}
        mccw = {v: ms[2 * k + 1] for k, v in enumerate(A)}
        L = max(len(x) for x in ms)
        procs = [Proc((lambda v=v: msg_exchange(v == 0, mcw[v], mccw[v])) if active[v]
                      else (lambda v=v: msg_relay(v == 0))) for v in range(n)]
        seen, finals, mx = explore(procs, max_states=3_000_000)
        worst = max(worst, len(seen))
        assert mx <= 15 * n * L + 3 * n, (n, active, ms, mx)
        for c, info in finals:
            assert all(i[0] == 'done' for i in info), (n, active, ms)
            assert quiescent(c, info)
            for k, v in enumerate(A):
                cw = A[(k + 1) % len(A)]; ccw = A[(k - 1) % len(A)]
                assert info[v][2] == (mccw[cw], mcw[ccw]), (n, active, ms, v, info[v][2])
    print('n', n, 'cases', len(cases), 'ok; max states', worst, flush=True)
