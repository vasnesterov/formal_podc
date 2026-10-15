"""Tiny explicit-state model checker for population protocols (labelled agents).
weak fairness: an execution fails "eventually always good" iff some reachable SCC contains a bad
config and, for every unordered pair {a,b}, an internal edge labelled by that pair.
global fairness: fails iff some reachable bottom SCC contains a bad config."""
import sys
from itertools import permutations
sys.setrecursionlimit(1000000)

def explore(init, delta, n, limit=2_000_000):
    idx = {init: 0}; confs = [init]; edges = []  # edges[i] = list of (j, (a,b))
    stack = [0]
    while stack:
        i = stack.pop()
        c = confs[i]; out = []
        for a in range(n):
            for b in range(n):
                if a == b: continue
                p, q = delta(c[a], c[b])
                if p == c[a] and q == c[b]:
                    out.append((i, (min(a,b), max(a,b)))); continue
                d = list(c); d[a] = p; d[b] = q; d = tuple(d)
                j = idx.get(d)
                if j is None:
                    j = len(confs); idx[d] = j; confs.append(d); stack.append(j)
                    if len(confs) > limit: raise Exception("too many configs")
                out.append((j, (min(a,b), max(a,b))))
        while len(edges) <= i: edges.append(None)
        edges[i] = out
    return confs, edges

def sccs(N, edges):
    # iterative Tarjan
    index = [None]*N; low = [0]*N; onst = [False]*N; st = []; comp = [None]*N; res = []
    cnt = 0
    for s in range(N):
        if index[s] is not None: continue
        work = [(s, 0)]
        index[s] = low[s] = cnt; cnt += 1; st.append(s); onst[s] = True
        while work:
            v, pi = work[-1]
            es = edges[v]
            if pi < len(es):
                work[-1] = (v, pi+1)
                w = es[pi][0]
                if index[w] is None:
                    index[w] = low[w] = cnt; cnt += 1; st.append(w); onst[w] = True
                    work.append((w, 0))
                elif onst[w]:
                    low[v] = min(low[v], index[w])
            else:
                work.pop()
                if work:
                    u = work[-1][0]; low[u] = min(low[u], low[v])
                if low[v] == index[v]:
                    cid = len(res); members = []
                    while True:
                        w = st.pop(); onst[w] = False; comp[w] = cid; members.append(w)
                        if w == v: break
                    res.append(members)
    return comp, res

def check(init, delta, n, bad, fairness="weak", limit=2_000_000):
    confs, edges = explore(init, delta, n, limit)
    comp, comps = sccs(len(confs), edges)
    allpairs = {(a,b) for a in range(n) for b in range(a+1,n)}
    for cid, mem in enumerate(comps):
        if fairness == "weak":
            pairs = set()
            for v in mem:
                for (w, pr) in edges[v]:
                    if comp[w] == cid: pairs.add(pr)
            ok = pairs >= allpairs
        else:
            ok = all(comp[w] == cid for v in mem for (w, _) in edges[v])
        if ok:
            badm = [confs[v] for v in mem if bad(confs[v])]
            if badm:
                return False, badm[0], len(confs), confs, edges
    return True, None, len(confs), confs, edges

def path_to(confs, edges, target):
    from collections import deque
    prev = {0: None}; dq = deque([0])
    tgt = confs.index(target)
    while dq:
        v = dq.popleft()
        if v == tgt: break
        for (w, pr) in edges[v]:
            if w not in prev: prev[w] = (v, pr); dq.append(w)
    path = []; v = tgt
    while prev[v] is not None:
        u, pr = prev[v]; path.append((pr, confs[v])); v = u
    return list(reversed(path))
