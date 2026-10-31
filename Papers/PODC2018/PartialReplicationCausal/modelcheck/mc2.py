import random, sys
sys.path.insert(0, sys.argv[1] if len(sys.argv) > 1 else '.')
from mc import tsgraph, share_edges

def run(X, Es, maxw, rng, hold_p=0.3, wprob=0.5):
    R = len(X)
    regs_of = [sorted(X[i]) for i in range(R)]
    tau = [dict((e, 0) for e in Es[i]) for i in range(R)]
    applied = [set() for _ in range(R)]; past = [set() for _ in range(R)]
    ups = []; inflight = []; held = []; pending = [[] for _ in range(R)]
    writes = [0] * R
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
            if held:
                inflight.extend(held); held.clear(); continue
            break
        c = rng.choice(opts)
        if c == 'w':
            i, x = rng.choice(canw); writes[i] += 1
            for e in Es[i]:
                if e[0] == i and x in X[e[1]]: tau[i][e] += 1
            uid = len(ups); deps = set(past[i])
            ups.append((i, dict(tau[i]), x, deps))
            applied[i].add(uid); past[i] |= deps | {uid}
            for k in range(R):
                if k != i and x in X[k]:
                    (held if rng.random() < hold_p else inflight).append((k, uid))
        elif c == 'd':
            dest, uid = inflight.pop(rng.randrange(len(inflight))); pending[dest].append(uid)
        else:
            i, uid = rng.choice(ready)
            k, T, x, deps = ups[uid]
            for d in deps:
                if ups[d][2] in X[i] and d not in applied[i]:
                    return 'UNSAFE'
            for e in Es[i] & Es[k]: tau[i][e] = max(tau[i][e], T[e])
            applied[i].add(uid); past[i] |= deps | {uid}; pending[i].remove(uid)
    for uid, (k, T, x, deps) in enumerate(ups):
        for i in range(R):
            if x in X[i] and uid not in applied[i]: return 'STUCK'
    return None

def check(X, Es, runs, maxw, rng):
    for _ in range(runs):
        r = run(X, Es, maxw, rng, hold_p=rng.choice([0.1, 0.3, 0.6]))
        if r: return r
    return None

if __name__ == '__main__':
    mode = sys.argv[2]; seed = int(sys.argv[3]); N = int(sys.argv[4])
    rng = random.Random(seed)
    for trial in range(N):
        R = rng.randint(3, 7); nreg = rng.randint(2, 8)
        X = [set() for _ in range(R)]
        for x in range(nreg):
            sz = rng.randint(2, min(3, R))
            for v in rng.sample(range(R), sz): X[v].add('abcdefghij'[x])
        if any(not s for s in X): continue
        Es = [tsgraph(X, i) for i in range(R)]
        if mode == 'full':
            r = check(X, Es, 40, 3, rng)
            if r: print('FOUND', r, X); break
        else:  # remove each non-incident edge and see if it breaks
            for i in range(R):
                for e in sorted(Es[i]):
                    if i in e: continue
                    Es2 = list(Es); Es2[i] = Es[i] - {e}
                    r = check(X, Es2, 150, 3, rng)
                    if not r: print('NOT-NEEDED?', i, e, X)
    print('done')
