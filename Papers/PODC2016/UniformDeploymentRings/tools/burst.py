import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import random
from sim import *
import alg456, alg23
from alg1 import alg1
def est(D, i):
    k = len(D)
    w = [D[(i + j) % k] for j in range(8 * k)]
    for q in range(1, 2 * k + 1):
        if all(w[x] == w[x + q] == w[x + 2*q] == w[x + 3*q] for x in range(q)):
            return q
def run_burst(s, rng, limit=10**6):
    while s.steps < limit:
        en = [a for a in range(s.k) if s.enabled(a)]
        if not en: return True
        a = rng.choice(en)
        L = rng.choice([1, 1, 3, 10, 50, 1000])
        for _ in range(L):
            if not s.step(a): break
    return False
which = sys.argv[1]; seed = int(sys.argv[2]); N = int(sys.argv[3])
rng = random.Random(seed); bad = 0; tot = 0
for it in range(N):
    k = rng.randint(2, 12)
    mode = rng.random()
    if mode < 0.4:
        D = [rng.choice([1, 1, 1, 2, 3, 5]) for _ in range(k)]
    elif mode < 0.7:
        l = rng.choice([d for d in range(1, k+1) if k % d == 0]); K = k // l
        B = [rng.choice([1, 1, 2, 3]) for _ in range(K)]; D = B * l
    else:
        pat = rng.choice([[1],[1,2],[1,1,2],[2,1,1,3]]); D = pat * rng.randint(3, 6) + [rng.randint(1, 9)]
        k = len(D)
    if which == '23' or which == '1':
        # need n = c k for 23
        if which == '23' and sum(D) % k: continue
    homes = [0]
    for d in D[:-1]: homes.append(homes[-1] + d)
    n = sum(D)
    prog = {'1': lambda: alg1(k), '23': lambda: alg23.alg23(k), '456l': lambda: alg456.alg456(False), '456c': lambda: alg456.alg456(True)}[which]()
    s = Sim(n, homes, prog); tot += 1
    ok = run_burst(s, rng)
    u = s.uniform()
    if not ok or not u[0]:
        bad += 1; print("BAD", D, n, k, ok, u, s.status)
        if bad > 3: break
print(which, "rings", tot, "bad", bad)
