import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sys, random, itertools
from sim import *
from alg1 import alg1
rng = random.Random(1)
bad = 0
for trial in range(3000):
    n = rng.randint(2, 14); k = rng.randint(2, n)
    homes = sorted(rng.sample(range(n), k))
    s = Sim(n, homes, alg1(k))
    w = [rng.choice([1, 1, 10, 100]) for _ in range(k)]
    ok = s.run(rng=rng, weights=w)
    u = s.uniform()
    if not ok or not u[0] or not all(x == 'halt' for x in s.status):
        bad += 1; print(n, k, homes, ok, u, s.status); 
        if bad > 5: break
print("bad", bad)
