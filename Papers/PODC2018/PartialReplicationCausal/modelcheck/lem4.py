"""Check Lemma 4 (restricted to e_ki in E_j) at every issue event in random runs."""
import random, sys
sys.path.insert(0,'.')
from mc import tsgraph

def run(X, Es, maxw, rng, hold_p):
    R = len(X)
    regs_of = [sorted(X[i]) for i in range(R)]
    tau = [dict((e, 0) for e in Es[i]) for i in range(R)]
    applied = [set() for _ in range(R)]; past = [set() for _ in range(R)]
    ups = []; inflight = []; held = []; pending = [[] for _ in range(R)]
    writes = [0] * R; viol = []
    while True:
        ready = []
        for i in range(R):
            for uid in pending[i]:
                k, T, x, deps = ups[uid]
                ok = tau[i][(k, i)] == T[(k, i)] - 1 and all(
                    tau[i][e] >= T[e] for e in Es[i] & Es[k] if e[1] == i and e[0] != k)
                if ok: ready.append((i, uid))
        canw = [(i, x) for i in range(R) if writes[i] < maxw for x in regs_of[i]]
        opts = []
        if canw: opts.append('w')
        if inflight: opts.append('d')
        if ready: opts.append('a')
        if not opts:
            if held: inflight.extend(held); held.clear(); continue
            break
        c = rng.choice(opts)
        if c == 'w':
            j, x = rng.choice(canw); writes[j] += 1
            for e in Es[j]:
                if e[0] == j and x in X[e[1]]: tau[j][e] += 1
            uid = len(ups); deps = set(past[j]); T = dict(tau[j])
            # Lemma 4 check: u from j to i; u' in deps from k to i
            for i in range(R):
                if i == j or x not in X[i]: continue
                for d in deps:
                    k, T2, x2, _ = ups[d]
                    if k == i or k == j or x2 not in X[i]: continue
                    if (k, i) in Es[j]:
                        if T[(k, i)] < T2[(k, i)]: viol.append(('restricted', j, i, k))
                    else:
                        viol.append(('untracked', j, i, k))
            ups.append((j, T, x, deps))
            applied[j].add(uid); past[j] |= deps | {uid}
            for k in range(R):
                if k != j and x in X[k]:
                    (held if rng.random() < hold_p else inflight).append((k, uid))
        elif c == 'd':
            dest, uid = inflight.pop(rng.randrange(len(inflight))); pending[dest].append(uid)
        else:
            i, uid = rng.choice(ready)
            k, T, x, deps = ups[uid]
            for e in Es[i] & Es[k]: tau[i][e] = max(tau[i][e], T[e])
            applied[i].add(uid); past[i] |= deps | {uid}; pending[i].remove(uid)
    return viol

seed=int(sys.argv[1]); N=int(sys.argv[2]); runs=int(sys.argv[3])
rng=random.Random(seed); stats={'restricted':0,'untracked':0}
for trial in range(N):
    R = rng.randint(4, 7); nreg = rng.randint(3, 8)
    X = [set() for _ in range(R)]
    for x in range(nreg):
        sz = rng.randint(2, min(3, R))
        for v in rng.sample(range(R), sz): X[v].add('abcdefghij'[x])
    if any(not s for s in X): continue
    Es = [tsgraph(X, i) for i in range(R)]
    for _ in range(runs):
        v = run(X, Es, 2, rng, rng.choice([0.1,0.3,0.6]))
        for t in v:
            if stats[t[0]] == 0: print(t, X)
            stats[t[0]] += 1
print(stats)
