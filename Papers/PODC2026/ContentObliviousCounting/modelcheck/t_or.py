import itertools, sys
sys.path.insert(0, sys.argv[1])
from core import *
from algs import *
for n in range(1, 7):
    for bs in itertools.product([False, True], repeat=n):
        procs = [Proc((lambda v=v: compute_or(v == 0, bs[v]))) for v in range(n)]
        seen, finals, mx = explore(procs)
        for c, info in finals:
            assert all(i[0] == 'done' for i in info), (n, bs, info)
            assert quiescent(c, info)
            assert all(i[2] == any(bs) for i in info), (n, bs, [i[2] for i in info])
            assert sum(sum(i[1]) for i in info) == 3 * n
        assert mx == 3 * n
        assert len(finals) == 1
    print('n', n, 'ok', len(seen))
