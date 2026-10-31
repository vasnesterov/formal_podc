import random, sys
sys.path.insert(0,'.')
from mc import tsgraph
from c1 import run
rng = random.Random(int(sys.argv[1]))
for trial in range(int(sys.argv[2])):
    R = rng.randint(3, 6); nreg = rng.randint(3, 7)
    X = [set() for _ in range(R)]
    for x in range(nreg):
        sz = rng.randint(2, min(3, R))
        for v in rng.sample(range(R), sz): X[v].add('abcdefghij'[x])
    if any(not s for s in X): continue
    Es = [tsgraph(X, i) for i in range(R)]
    seen = {}
    for _ in range(int(sys.argv[3])):
        r = run(X, Es, 2, rng, rng.choice([0.1,0.3,0.6]), seen)
        if r:
            print('VIOLATION', X); print(r[0]); print(' A', r[1][0]); print('   ', r[1][1]); print(' B', r[2][0]); print('   ', r[2][1]); sys.exit()
print('none')
