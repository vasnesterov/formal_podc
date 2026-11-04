import itertools, sys
from collections import deque
def run(n, edges, D, K):
    # edges: list of (a,b) initial a->b
    nb={u:set() for u in range(n)}; inn={u:set() for u in range(n)}; out={u:set() for u in range(n)}
    for a,b in edges: nb[a].add(b); nb[b].add(a); out[a].add(b); inn[b].add(a)
    E=[frozenset(e) for e in edges]
    # orientation: frozenset of arcs
    init=frozenset(edges)
    def sink(arcs,u): return all((v,u) in arcs for v in nb[u])
    def flip(arcs,u,X):
        a=set(arcs)
        for v in X:
            if (v,u) in a: a.remove((v,u)); a.add((u,v))
        return frozenset(a)
    # OneStepPR
    s0=(init, tuple(frozenset() for _ in range(n)))
    seen={s0}; q=deque([s0])
    while q:
        arcs,lst=q.popleft()
        for u in range(n):
            if u==D or not sink(arcs,u): continue
            rev = (nb[u]-lst[u]) if lst[u]!=nb[u] else nb[u]
            l=list(lst)
            for v in rev: l[v]=l[v]|{u}
            l[u]=frozenset()
            st=(flip(arcs,u,rev),tuple(l))
            if st not in seen and len(seen)<200000: seen.add(st); q.append(st)
    S=seen
    t0=(init,(0,)*n)
    T={t0}; q=deque([t0])
    while q:
        arcs,c=q.popleft()
        for u in range(n):
            if u==D or not sink(arcs,u) or c[u]>=K: continue
            X = inn[u] if c[u]%2==0 else out[u]
            cc=list(c); cc[u]+=1
            st=(flip(arcs,u,X),tuple(cc))
            if st not in T: T.add(st); q.append(st)
    # acyclicity check
    def acyc(arcs):
        adj={u:[b for (a,b) in arcs if a==u] for u in range(n)}
        col=[0]*n
        def dfs(u):
            col[u]=1
            for v in adj[u]:
                if col[v]==1: return False
                if col[v]==0 and not dfs(v): return False
            col[u]=2; return True
        return all(col[u] or dfs(u) for u in range(n))
    assert all(acyc(a) for a,_ in S); assert all(acyc(a) for a,_ in T)
    byarcs={}
    for t in T: byarcs.setdefault(t[0],[]).append(t)
    bad=0
    for (arcs,lst) in S:
        for (_,c) in byarcs.get(arcs,[]):
            if not all((lst[u]<=out[u]) if c[u]%2==0 else (lst[u]<=inn[u]) for u in range(n)): continue
            for w in range(n):
                if w==D or not sink(arcs,w): continue
                rev=(nb[w]-lst[w]) if lst[w]!=nb[w] else nb[w]
                target=flip(arcs,w,rev)
                # paper sequence
                X = inn[w] if c[w]%2==0 else out[w]
                a1=flip(arcs,w,X)
                if lst[w]!=nb[w]: res=a1
                else:
                    X2 = out[w] if c[w]%2==0 else inn[w]
                    res=flip(a1,w,X2) if sink(a1,w) else None
                if res!=target:
                    bad+=1
                    if bad<=3: print("paper seq fails", n, edges, D, "lists",lst,"counts",c,"w",w)
    return len(S),len(T),bad
def connected(n,edges):
    adj={u:set() for u in range(n)}
    for a,b in edges: adj[a].add(b); adj[b].add(a)
    st=[0]; s={0}
    while st:
        u=st.pop()
        for v in adj[u]:
            if v not in s: s.add(v); st.append(v)
    return len(s)==n
N=int(sys.argv[1]); K=int(sys.argv[2]); conn=sys.argv[3]=='c'
pairs=list(itertools.combinations(range(N),2))
tot=0
for m in range(len(pairs)+1):
  for es in itertools.combinations(pairs,m):
    edges=list(es)  # oriented low->high: topological order identity
    if conn and not connected(N,edges): continue
    for D in range(N):
        a,b,bad=run(N,edges,D,K)
        tot+=bad; globals().setdefault("cnt",[0]); cnt[0]+=1
print("total bad",tot,"runs",cnt[0])
