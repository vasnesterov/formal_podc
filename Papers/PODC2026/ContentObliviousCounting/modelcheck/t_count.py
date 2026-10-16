import itertools, sys, random
sys.path.insert(0, sys.argv[1])
from core import *
from algs import *
NMAX = int(sys.argv[2]); EXH = int(sys.argv[3])
def decode(bits):
    return sum(b << k for k, b in enumerate(bits))
def analyse(n, c, info):
    assert all(i[0] == 'done' for i in info), (n, info)
    assert quiescent(c, info)
    outs = []
    lead = [v for v in range(n) if info[v][2][0] == 'L']
    assert len(lead) == 1
    i = info[lead[0]][2][1]
    for v in range(n):
        kind, phase, x, bits, g = info[v][2]
        assert phase == i, (n, v, phase, i)
        count = decode(bits)
        N = i * (i - 1) // 2 + count + 1
        assert N == n, (n, N)
        mp = getattr(g, 'myPhase', None)
        k = 0 if kind == 'L' else x - 1
        if mp is None: dpaper = None
        elif mp < i: dpaper = mp * (mp + 1) // 2 - k - 1
        else: dpaper = N - k - 1
        if mp is None: dfix = 0
        elif mp < i: dfix = mp * (mp + 1) // 2 - k
        else: dfix = N - k - 1
        assert dfix == v, (n, v, mp, k, dfix)
        outs.append((v, mp, k, dpaper))
    return i, outs
for n in range(1, NMAX + 1):
    procs = [Proc((lambda v=v: counting(v == 0))) for v in range(n)]
    if n <= EXH:
        seen, finals, mx = explore(procs)
        res = {analyse(n, c, info)[1].__repr__() for c, info in finals}
        assert len(res) == 1
        i, outs = analyse(n, *finals[0][:2])
        print('n', n, 'states', len(seen), 'finals', len(finals), 'maxsent', mx, 'phases', i,
              'paper d - true:', [ (o[3] - o[0] if o[3] is not None else None) for o in outs], flush=True)
    else:
        rng = random.Random(n)
        mxx = 0
        for r in range(200):
            c, info, mx = random_run(procs, rng)
            mxx = max(mxx, mx)
            i, outs = analyse(n, c, info)
        print('n', n, 'random ok maxsent', mxx, 'n^1.5', round(n ** 1.5), 'phases', i,
              'paper d - true:', [ (o[3] - o[0] if o[3] is not None else None) for o in outs][:16], flush=True)
