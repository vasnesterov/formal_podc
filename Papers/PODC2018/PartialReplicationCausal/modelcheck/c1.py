"""Search for violations of Constraint 1 by the paper's algorithm: same causal past (set of update
identities (issuer, seq, reg)) at a replica, different timestamp."""
import random, sys
sys.path.insert(0,'.')
from mc import tsgraph

def run(X, Es, maxw, rng, hold_p, seen):
    R = len(X)
    regs_of = [sorted(X[i]) for i in range(R)]
    tau = [dict((e, 0) for e in Es[i]) for i in range(R)]
    applied = [set() for _ in range(R)]; past = [set() for _ in range(R)]
    ups = []; ident = []; inflight = []; held = []; pending = [[] for _ in range(R)]
    writes = [0] * R
    def record(i, trace):
        key = (i, frozenset(ident[u] for u in past[i]))
        val = tuple(sorted(tau[i].items()))
        if key in seen and seen[key][0] != val:
            return (key, seen[key], (val, list(trace)))
        seen.setdefault(key, (val, list(trace)))
        return None
    trace = []
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
            return None
        c = rng.choice(opts)
        if c == 'w':
            j, x = rng.choice(canw); writes[j] += 1
            for e in Es[j]:
                if e[0] == j and x in X[e[1]]: tau[j][e] += 1
            uid = len(ups); deps = set(past[j])
            ups.append((j, dict(tau[j]), x, deps)); ident.append((j, writes[j], x))
            applied[j].add(uid); past[j] |= deps | {uid}
            trace.append(('w', j, x))
            for k in range(R):
                if k != j and x in X[k]:
                    (held if rng.random() < hold_p else inflight).append((k, uid))
            r = record(j, trace)
            if r: return r
        elif c == 'd':
            dest, uid = inflight.pop(rng.randrange(len(inflight))); pending[dest].append(uid)
        else:
            i, uid = rng.choice(ready)
            k, T, x, deps = ups[uid]
            for e in Es[i] & Es[k]: tau[i][e] = max(tau[i][e], T[e])
            applied[i].add(uid); past[i] |= deps | {uid}; pending[i].remove(uid)
            trace.append(('a', i, ident[uid]))
            r = record(i, trace)
            if r: return r

if __name__ == '__main__':
    X = [set('feb'), set('ea'), set('ag'), set('gb'), set('fag')]
    Es = [tsgraph(X, i) for i in range(5)]
    rng = random.Random(1)
    seen = {}
    for _ in range(20000):
        r = run(X, Es, 2, rng, rng.choice([0.1,0.3,0.6]), seen)
        if r:
            print('VIOLATION', r[0]); print(' A', r[1][0]); print('   ', r[1][1]); print(' B', r[2][0]); print('   ', r[2][1]); break
    else: print('none')
