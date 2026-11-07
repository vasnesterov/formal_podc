import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import random
from sim import *
import alg456
def est(D, i):
    k = len(D)
    w = [D[(i + j) % k] for j in range(4 * k)]
    for q in range(1, k + 1):
        if all(w[x] == w[x + q] == w[x + 2*q] == w[x + 3*q] for x in range(q)):
            return q
rng = random.Random(int(sys.argv[1])); maxn = int(sys.argv[2])
best = None
for it in range(int(sys.argv[3])):
    k = rng.randint(5, 11)
    D = [rng.choice([1, 1, 1, 1, 2, 3, 4, 6, 9]) for _ in range(k)]
    n = sum(D)
    if n > maxn or min_period(D) != k: continue
    es = [est(D, i) for i in range(k)]
    if all(e == k for e in es): continue
    homes = [0]
    for d in D[:-1]: homes.append(homes[-1] + d)
    for trial in range(6):
        w = [rng.choice([1, 10, 1000, 10**6]) for _ in range(k)]
        for i in range(k):
            if es[i] < k: w[i] = 10**7
        s = Sim(n, homes, alg456.alg456(False))
        ok = s.run(rng=rng, weights=w, limit=200000)
        u = s.uniform()
        if ok and not u[0]:
            if best is None or n < best[0]:
                best = (n, k, D, w, s.steps); print(best, flush=True)
            break
print("best", best)
