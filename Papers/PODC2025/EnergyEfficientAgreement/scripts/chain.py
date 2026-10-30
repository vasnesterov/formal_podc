# Restricted adversary search ("thin chains" + pre-crashing one committee) for Algorithm 3 (arXiv v1),
# with the paper's JoinCommittees, for larger n. Single input-1 player.
import sys, math
sys.setrecursionlimit(100000)
def ceil_sqrt(n):
    s = math.isqrt(n); return s if s*s == n else s+1
def T0_of(n, f):
    T = 0
    while T*T*n < (f+1)**2: T += 1
    return T
def committees(n, a, b):
    C = [set() for _ in range(a+2)]
    for i in range(1, a*b+1): C[-(-i//b)].add(i % n)
    return C
def search(n, f):
    s = ceil_sqrt(n); T0 = T0_of(n, f); C = committees(n, f, s)
    def go(r, crashed, holders, T, X, trace):
        # holders: dict p -> True (Y=1 or X=1), alive only
        if len(crashed) > f: return None
        if r == f+1:
            H = [p for p in holders if p not in crashed]
            if H and len(crashed) + len(H) <= f and n - len(crashed) - len(H) >= 2:
                return trace + [('final', H)]
            return None
        senders = [p for p in range(n) if p not in crashed and T.get(p, 0) > 0]
        if r == 1: senders = [X]
        if not senders: return None
        pool = [q for q in C[r] if q not in crashed]
        opts = []
        # option A: no crash, all alive members of C_r receive
        if all(q in holders for q in pool): opts.append((set(), pool))
        # option B: crash all senders, deliver to one fresh member (or none)
        fresh = [q for q in pool if q not in senders]
        for x in fresh: opts.append((set(senders), [x]))
        for K, R in opts:
            if len(crashed | K) > f: continue
            T2 = dict(T)
            if r == 1: T2[X] = T0
            else:
                for p in senders: T2[p] -= 1
            h2 = set(holders)
            for q in R:
                if q in K: continue
                if q not in h2 or (q == X and r == 1):
                    h2.add(q); T2[q] = T0
            c2 = crashed | K
            res = go(r+1, c2, h2, T2, X, trace + [(r, sorted(K), sorted(R))])
            if res: return res
        return None
    for X in range(n):
        for pre in [None] + list(range(1, f+1)):
            crashed = set(C[pre]) - {X} if pre else set()
            res = go(1, crashed, {X}, {}, X, [('precrash', sorted(crashed))])
            if res: return (X, res)
    return None
for n in [int(a) for a in sys.argv[1:]]:
    for f in range(n-2, 0, -1):
        res = search(n, f)
        if res: print(f"n={n} f={f}: counterexample", res, flush=True)
        else: print(f"n={n} f={f}: none found (restricted)", flush=True)
