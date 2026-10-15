import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
"""ordered-pair weak fairness checker"""
import sys
sys.setrecursionlimit(1000000)
from mc import sccs
def explore_o(init, delta, n, limit=3_000_000):
    idx = {init: 0}; confs = [init]; edges = []
    stack = [0]
    while stack:
        i = stack.pop()
        c = confs[i]; out = []
        for a in range(n):
            for b in range(n):
                if a == b: continue
                p, q = delta(c[a], c[b])
                if p == c[a] and q == c[b]:
                    out.append((i, (a,b))); continue
                d = list(c); d[a] = p; d[b] = q; d = tuple(d)
                j = idx.get(d)
                if j is None:
                    j = len(confs); idx[d] = j; confs.append(d); stack.append(j)
                    if len(confs) > limit: raise Exception("too many configs")
                out.append((j, (a,b)))
        while len(edges) <= i: edges.append(None)
        edges[i] = out
    return confs, edges
def check2(init, delta, n, bad, fairness="ordered", limit=3_000_000):
    confs, edges = explore_o(init, delta, n, limit)
    comp, comps = sccs(len(confs), edges)
    if fairness == "ordered":
        allpairs = {(a,b) for a in range(n) for b in range(n) if a!=b}
        norm = lambda pr: pr
    else:
        allpairs = {(a,b) for a in range(n) for b in range(a+1,n)}
        norm = lambda pr: (min(pr), max(pr))
    for cid, mem in enumerate(comps):
        pairs = set()
        for v in mem:
            for (w, pr) in edges[v]:
                if comp[w] == cid: pairs.add(norm(pr))
        if pairs >= allpairs:
            badm = [confs[v] for v in mem if bad(confs[v])]
            if badm:
                return False, badm[0], len(confs), confs, edges
    return True, None, len(confs), confs, edges
