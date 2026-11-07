import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import random
from sim import *
import alg23
rng = random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 1)
bad = 0; maxph = {}
for trial in range(int(sys.argv[2]) if len(sys.argv)>2 else 3000):
    k = rng.randint(2, 12); c = rng.randint(1, 4); n = c*k
    if rng.random() < 0.5:
        # periodic
        divs = [l for l in range(1, k+1) if k % l == 0]
        l = rng.choice(divs); N = n//l; K = k//l
        if K > N: continue
        base = sorted(rng.sample(range(N), K))
        homes = sorted(b + j*N for j in range(l) for b in base)
    else:
        homes = sorted(rng.sample(range(n), k))
    alg23.STATS.clear()
    s = Sim(n, homes, alg23.alg23(k))
    w = [rng.choice([1, 1, 10, 100, 1000, 10**6, 10**9]) for _ in range(k)]
    ok = s.run(rng=rng, weights=w)
    u = s.uniform()
    ph = max(alg23.STATS.values())
    import math
    if ph > math.ceil(math.log2(k)):
        maxph.setdefault(k, (ph, homes, n))
    if not ok or not u[0] or not all(x == 'halt' for x in s.status):
        bad += 1; print("BAD", n, k, homes, w, ok, u, s.status)
        if bad > 5: break
print("bad", bad, "subphase>ceil(log k):", maxph)
