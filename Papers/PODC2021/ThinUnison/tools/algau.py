"""Explicit-state checks of AlgAU (Emek-Keren PODC'21) on small graphs.

Turn = (level, faulty).  Levels: 1 <= |l| <= k.  Usage: python3 algau.py
Checks (exhaustively over all configurations and all activation sets):
  * local invariants (Obs 2.1, 2.3, 2.5) on every transition,
  * Lemma 2.10 (good is closed),
  * no fair cycle avoiding good configurations (SCC check, every node activated inside).
"""
import itertools, sys
sys.setrecursionlimit(1000000)

def mk(k):
    def fwd(l):
        return 1 if l == -1 else (-k if l == k else l + 1)
    def inw(l):
        return l - 1 if l > 0 else l + 1
    def adj(a, b):
        return a == b or a == fwd(b) or b == fwd(a)
    def outward(l, m):  # m in Psi^>(l)
        return (l > 0 and m > l) or (l < 0 and m < l)
    def farout(l, m):
        return (l > 0 and m >= l + 2) or (l < 0 and m <= l - 2)
    def delta(st, sig):
        l, f = st
        lv = {s[0] for s in sig}
        if not f:
            prot = all(adj(l, m) for m in lv)
            good = prot and not any(s[1] for s in sig)
            if good and lv <= {l, fwd(l)}:
                return (fwd(l), False)
            if abs(l) >= 2 and (not prot or (inw(l), True) in sig):
                return (l, True)
            return st
        else:
            if not any(outward(l, m) for m in lv):
                return (inw(l), False)
            return st
    states = [(l, False) for l in range(-k, k + 1) if l != 0] + \
             [(l, True) for l in range(-k, k + 1) if abs(l) >= 2]
    return dict(fwd=fwd, inw=inw, adj=adj, farout=farout, delta=delta, states=states)

def check(n, edges, D, k=None):
    k = k or 3 * D + 2
    A = mk(k)
    nb = [[v] for v in range(n)]
    for (a, b) in edges:
        nb[a].append(b); nb[b].append(a)
    S = A['states']; idx = {s: i for i, s in enumerate(S)}
    def good(C):
        for v in range(n):
            for u in nb[v]:
                if not A['adj'](C[v][0], C[u][0]) or C[u][1]:
                    return False
        return True
    subsets = [frozenset(s) for r in range(1, n + 1) for s in itertools.combinations(range(n), r)]
    configs = list(itertools.product(S, repeat=n))
    cid = {c: i for i, c in enumerate(configs)}
    succ = [[] for _ in configs]
    bad = 0
    for i, C in enumerate(configs):
        sig = [{C[u] for u in nb[v]} for v in range(n)]
        nxt = [A['delta'](C[v], sig[v]) for v in range(n)]
        g = good(C)
        for As in subsets:
            C2 = tuple(nxt[v] if v in As else C[v] for v in range(n))
            # Obs 2.1
            for (a, b) in edges:
                la, lb = C[a][0], C[b][0]
                if A['adj'](la, lb) and {la, lb} != {-k, k}:
                    assert A['adj'](C2[a][0], C2[b][0]), ("Obs2.1", C, As, C2)
                if not A['adj'](la, lb):
                    lo, hi = (a, b) if la < lb else (b, a)
                    assert C[lo][0] <= C2[lo][0] < C2[hi][0] <= C[hi][0], ("Obs2.5", C, As, C2)
            # Obs 2.3
            for v in range(n):
                op = not any(A['farout'](C[v][0], C[u][0]) for u in nb[v])
                op2 = not any(A['farout'](C2[v][0], C2[u][0]) for u in nb[v])
                if op: assert op2, ("Obs2.3", C, As, C2)
            if g: assert good(C2), ("L2.10", C, As, C2)
            succ[i].append((cid[C2], As))
    # SCC (iterative Tarjan) over non-good configs
    N = len(configs)
    isgood = [good(c) for c in configs]
    index = [-1] * N; low = [0] * N; onst = [False] * N; st = []; comp = [-1] * N
    cnt = 0; nc = 0
    for s0 in range(N):
        if index[s0] != -1 or isgood[s0]: continue
        stack = [(s0, 0)]
        index[s0] = low[s0] = cnt; cnt += 1; st.append(s0); onst[s0] = True
        while stack:
            v, pi = stack[-1]
            ss = [w for (w, _) in succ[v] if not isgood[w]]
            if pi < len(ss):
                stack[-1] = (v, pi + 1)
                w = ss[pi]
                if index[w] == -1:
                    index[w] = low[w] = cnt; cnt += 1; st.append(w); onst[w] = True
                    stack.append((w, 0))
                elif onst[w]:
                    low[v] = min(low[v], index[w])
            else:
                stack.pop()
                if stack: low[stack[-1][0]] = min(low[stack[-1][0]], low[v])
                if low[v] == index[v]:
                    while True:
                        w = st.pop(); onst[w] = False; comp[w] = nc
                        if w == v: break
                    nc += 1
    # fair cycle: SCC where every node is activated on some internal edge
    act = [set() for _ in range(nc)]
    for v in range(N):
        if isgood[v]: continue
        for (w, As) in succ[v]:
            if not isgood[w] and comp[w] == comp[v]:
                act[comp[v]] |= As
    fair_bad = [c for c in range(nc) if len(act[c]) == n]
    print(f"n={n} edges={edges} D={D} k={k}: configs={N}, nongood SCCs={nc}, fair bad SCCs={len(fair_bad)}")
    if fair_bad:
        c = fair_bad[0]
        print("  example:", [configs[v] for v in range(N) if comp[v] == c][:5])

if __name__ == '__main__':
    check(2, [(0, 1)], 1)
    check(3, [(0, 1), (1, 2), (0, 2)], 1)
    check(3, [(0, 1), (1, 2)], 2)
