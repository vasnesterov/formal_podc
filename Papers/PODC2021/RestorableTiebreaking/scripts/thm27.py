# Numerical check of the lower-bound construction of Theorem 27 (Appendix B), single source.
import heapq, math, sys
from fractions import Fraction

def build(f, d, G, counter):
    """Build G_f(d); returns (root, leaves(list in order), labels dict leaf->list of edges or None)."""
    def new():
        counter[0] += 1; G.setdefault(counter[0], set()); return counter[0]
    def edge(a, b):
        G[a].add(b); G[b].add(a)
    if f == 1:
        U = [new() for _ in range(d)]
        for i in range(d - 1): edge(U[i], U[i + 1])
        leaves, labels = [], {}
        for i in range(d):  # Q_i has length d-i (paper: d-i+1 with 1-indexing)
            prev = U[i]
            for _ in range(d - i):
                v = new(); edge(prev, v); prev = v
            leaves.append(prev)
            labels[prev] = [(U[i], U[i + 1])] if i < d - 1 else None
        return U[0], leaves, labels
    r = int(round(math.sqrt(d))); assert r * r == d
    U = [new() for _ in range(d)]
    for i in range(d - 1): edge(U[i], U[i + 1])
    leaves, labels = [], {}
    for j in range(d):
        root, lv, lb = build(f - 1, r, G, counter)
        prev = U[j]
        for _ in range(d - j - 1):
            v = new(); edge(prev, v); prev = v
        edge(prev, root)  # path of length d-j
        for z in lv:
            leaves.append(z)
            labels[z] = None if (j == d - 1 or lb[z] is None) else [(U[j], U[j + 1])] + lb[z]
    return U[0], leaves, labels

def run(f, d, chi):
    G, counter = {}, [0]
    s, leaves, labels = build(f, d, G, counter)
    # u_d^f: last vertex of P_f = vertex at distance d-1 from s along path; recompute: it's s + d - 1 ids
    ud = s + d - 1
    X = []
    for _ in range(chi):
        counter[0] += 1; x = counter[0]; G[x] = set(); X.append(x)
        G[x].add(ud); G[ud].add(x)
        for z in leaves: G[x].add(z); G[z].add(x)
    n = len(G); lam = len(leaves)
    pos = {z: k for k, z in enumerate(leaves)}
    def w(a, b):
        if a in pos and b in X: return Fraction(1) + Fraction(lam - pos[a], n ** 4)
        if b in pos and a in X: return Fraction(1) + Fraction(lam - pos[b], n ** 4)
        return Fraction(1)
    covered = set(); bad = 0
    for z in leaves:
        F = labels[z]
        if F is None: continue
        Fs = set(frozenset(e) for e in F)
        assert len(F) == f
        dist = {s: Fraction(0)}; par = {s: [None]}; pq = [(Fraction(0), s)]
        done = set()
        while pq:
            dv, v = heapq.heappop(pq)
            if v in done: continue
            done.add(v)
            for u in G[v]:
                if frozenset((u, v)) in Fs: continue
                nd = dv + w(v, u)
                if u not in dist or nd < dist[u]:
                    dist[u] = nd; par[u] = [v]; heapq.heappush(pq, (nd, u))
                elif nd == dist[u]:
                    par[u].append(v)
        for x in X:
            if len(par[x]) != 1: bad += 1
            elif par[x][0] == z: covered.add((z, x))
            else: bad += 1
    print(f"f={f} d={d} chi={chi} n={n} leaves={lam} B={lam*chi} covered={len(covered)} bad={bad} "
          f"n^(2-1/2^f)={n**(2-1/2**f):.0f}")

for f, d, chi in [(1, 4, 20), (1, 6, 40), (2, 4, 40), (2, 9, 100), (3, 16, 100)]:
    run(f, d, chi)
