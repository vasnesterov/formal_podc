import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import random
from sim import *
import alg456
D = eval(sys.argv[1]); h = int(sys.argv[2]); cyc = sys.argv[3] == 'c'
n = sum(D); k = len(D); homes = [0]
for d in D[:-1]: homes.append(homes[-1] + d)
rng = random.Random(1); bad = 0
for trial in range(300):
    w = [rng.choice([1, 10, 100, 10**4]) for _ in range(k)]
    w[h] = 10**7
    s = Sim(n, homes, alg456.alg456(cyc))
    ok = s.run(rng=rng, weights=w, limit=10**6)
    u = s.uniform()
    if not ok or not u[0]:
        bad += 1
        if bad < 3: print("BAD", w, ok, u, s.status, s.moves)
print("bad", bad, "of 300")
