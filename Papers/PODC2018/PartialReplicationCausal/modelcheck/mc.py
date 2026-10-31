"""Model checker for the Xiang-Vaidya edge-indexed timestamp algorithm (Sec 3.2).

Replicas 0..R-1, X[i] = set of registers.  Computes timestamp graphs E_i per Def 6/7,
then explores executions (random or exhaustive DFS) checking safety (Def 5) and
a liveness-style state check (deadlock freedom: if all deps of a pending update are
applied, the predicate must hold).
"""
import itertools, random, sys

def share_edges(X):
    R = len(X)
    return {(a, b) for a in range(R) for b in range(R) if a != b and X[a] & X[b]}

def simple_paths(adj, src, dst, avoid):
    """all simple paths src..dst (as lists) avoiding vertices in avoid (src,dst not in avoid)."""
    out = []
    def go(v, path, seen):
        if v == dst:
            out.append(list(path)); return
        for w in adj[v]:
            if w not in seen and w not in avoid:
                seen.add(w); path.append(w); go(w, path, seen); path.pop(); seen.remove(w)
    go(src, [src], {src})
    return out

def loops(X, i, j, k):
    """All simple loops (i, l1..ls=k, j=r1..rt, i) with s,t>=1 in share graph."""
    R = len(X); E = share_edges(X)
    adj = {a: [b for b in range(R) if (a, b) in E] for a in range(R)}
    if (j, k) not in E: return
    # path i -> ... -> k (l1..ls), then edge k-j, then path j -> ... -> i (r1..rt, i)
    for lp in simple_paths(adj, i, k, {j}):
        ls = lp[1:]  # l1..ls
        if len(ls) < 1: continue
        for rp in simple_paths(adj, j, i, set(lp) - {i}):
            rs = rp[:-1]  # r1..rt
            if len(rs) < 1: continue
            yield ls, rs

def is_loop(X, i, j, k, ls, rs):
    U = lambda S: set().union(*[X[v] for v in S]) if S else set()
    s, t = len(ls), len(rs)
    r = rs + [i]  # r[0]=r1 ... r[t]=r_{t+1}=i
    if not (X[j] & X[k]) - U(ls[:s-1]): return False
    if not (X[j] & X[r[1]]) - U(ls[:s-1]): return False
    for q in range(1, t):  # q index 2..t -> r[q], r[q+1]
        if not (X[r[q]] & X[r[q+1]]) - U(ls): return False
    return True

def tsgraph(X, i):
    R = len(X); E = share_edges(X)
    Ei = {(a, b) for (a, b) in E if a == i or b == i}
    for (j, k) in E:
        if j == i or k == i: continue
        for ls, rs in loops(X, i, j, k):
            if is_loop(X, i, j, k, ls, rs):
                Ei.add((j, k)); break
    return Ei

class State:
    pass

def run_random(X, Es, maxw, rng, regs_of):
    R = len(X)
    tau = [dict((e, 0) for e in Es[i]) for i in range(R)]
    applied = [set() for _ in range(R)]  # update ids applied
    past = [set() for _ in range(R)]  # causal past = applied ∪ deps of applied
    ups = []  # (issuer, T, reg, deps)
    inflight = []  # (dest, uid)
    pending = [[] for _ in range(R)]
    writes = [0] * R
    trace = []
    while True:
        acts = []
        for i in range(R):
            if writes[i] < maxw:
                for x in regs_of[i]:
                    acts.append(('w', i, x))
        for m in range(len(inflight)):
            acts.append(('d', m))
        for i in range(R):
            for uid in pending[i]:
                k, T, x, deps = ups[uid]
                ok = tau[i][(k, i)] == T[(k, i)] - 1 and all(
                    tau[i][e] >= T[e] for e in Es[i] & Es[k] if e[1] == i and e[0] != k)
                if ok: acts.append(('a', i, uid))
        if not acts: break
        a = rng.choice(acts)
        trace.append(a)
        if a[0] == 'w':
            _, i, x = a
            writes[i] += 1
            for e in Es[i]:
                if e[0] == i and x in X[e[1]]: tau[i][e] += 1
            uid = len(ups)
            deps = set(past[i])
            ups.append((i, dict(tau[i]), x, deps))
            applied[i].add(uid); past[i] |= deps | {uid}
            for k in range(R):
                if k != i and x in X[k]: inflight.append((k, uid))
        elif a[0] == 'd':
            dest, uid = inflight.pop(a[1]); pending[dest].append(uid)
        else:
            _, i, uid = a
            k, T, x, deps = ups[uid]
            # safety check
            for d in deps:
                if ups[d][2] in X[i] and d not in applied[i]:
                    return ('UNSAFE', i, uid, d, trace, ups)
            for e in Es[i] & Es[k]:
                tau[i][e] = max(tau[i][e], T[e])
            applied[i].add(uid); past[i] |= deps | {uid}
            pending[i].remove(uid)
    # termination: every update applied everywhere relevant
    for uid, (k, T, x, deps) in enumerate(ups):
        for i in range(R):
            if x in X[i] and uid not in applied[i]:
                return ('STUCK', i, uid, trace, ups)
    return None

def check(X, runs, maxw, seed=0):
    R = len(X)
    Es = [tsgraph(X, i) for i in range(R)]
    rng = random.Random(seed)
    regs_of = [sorted(X[i]) for i in range(R)]
    for _ in range(runs):
        r = run_random(X, Es, maxw, rng, regs_of)
        if r: return r, Es
    return None, Es

if __name__ == '__main__':
    X = [set('ayw'), set('bxy'), set('cxz'), set('dyzw')]
    for i in range(4):
        print(i + 1, sorted((a + 1, b + 1) for a, b in tsgraph(X, i)))
    print(check(X, 200, 2)[0])
