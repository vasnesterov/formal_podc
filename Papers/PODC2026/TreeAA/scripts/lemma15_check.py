# Exhaustive check of the intermediate claim in the proof of Lemma 15 (see differencies.md, item 2).
# Enumerates all labelled trees on the 8 maximal cliques of the block graph "path x0..x6 + pendants a,b at x3"
# (Pruefer sequences), keeps the clique trees (running intersection property, adjacent cliques intersect),
# and prints minimum-diameter clique trees with a longest path having 3 equal consecutive separators.
# Run: python3 -I lemma15_check.py  (about 10 s)
import itertools, sys
from collections import deque
# block graph: path x0..x6 (vertices 0..6) plus pendants a=7, b=8 at x3
cliques = [frozenset({i-1,i}) for i in range(1,7)] + [frozenset({3,7}), frozenset({3,8})]
names = ['e%d'%i for i in range(1,7)] + ['x3a','x3b']
k = len(cliques)
def prufer_to_edges(seq, n):
    degree = [1]*n
    for x in seq: degree[x]+=1
    edges=[]
    for x in seq:
        for j in range(n):
            if degree[j]==1:
                edges.append((j,x)); degree[j]-=1; degree[x]-=1; break
    u,v=[j for j in range(n) if degree[j]==1]
    edges.append((u,v)); return edges
def bfs(adj, s, n):
    d=[-1]*n; d[s]=0; q=deque([s]); par=[-1]*n
    while q:
        x=q.popleft()
        for y in adj[x]:
            if d[y]<0: d[y]=d[x]+1; par[y]=x; q.append(y)
    return d, par
def path(par, s, t):
    p=[t]
    while p[-1]!=s: p.append(par[p[-1]])
    return p[::-1]
results=[]
mind=10**9
for seq in itertools.product(range(k), repeat=k-2):
    E=prufer_to_edges(seq,k)
    adj=[[] for _ in range(k)]
    for u,v in E: adj[u].append(v); adj[v].append(u)
    # RIP: for each pair, intersection subset of every clique on path
    ok=True
    allpar=[]; alld=[]
    for s in range(k):
        d,par=bfs(adj,s,k); alld.append(d); allpar.append(par)
    for s in range(k):
        for t in range(s+1,k):
            inter=cliques[s]&cliques[t]
            if not inter: continue
            for c in path(allpar[s],s,t):
                if not inter<=cliques[c]: ok=False;break
            if not ok: break
        if not ok: break
    if not ok: continue
    # adjacent cliques must intersect
    if any(not (cliques[u]&cliques[v]) for u,v in E): continue
    diam=max(max(d) for d in alld)
    results.append((E,diam,alld,allpar))
    mind=min(mind,diam)
print("clique trees:",len(results),"min diameter:",mind)
# among min-diameter trees, find a longest path with 3 consecutive equal separators
found=0
for E,diam,alld,allpar in results:
    if diam!=mind: continue
    for s in range(k):
        for t in range(k):
            if alld[s][t]==diam:
                P=path(allpar[s],s,t)
                seps=[next(iter(cliques[P[i]]&cliques[P[i+1]])) for i in range(len(P)-1)]
                for i in range(len(seps)-2):
                    if seps[i]==seps[i+1]==seps[i+2]:
                        if found<2: print("min-diam tree", [(names[u],names[v]) for u,v in E], "longest path", [names[c] for c in P], "seps", seps)
                        found+=1
                        break
print("violations found:",found)
