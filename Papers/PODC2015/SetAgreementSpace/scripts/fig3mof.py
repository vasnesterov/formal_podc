# Model checker for Figure 3 (orig or fixed): agreement over all reachable configs, and
# m-obstruction-freedom: no reachable cycle using only steps of a set P (|P|<=m) of undecided processes
# in which every process of P steps (fair livelock).
import sys, itertools
sys.setrecursionlimit(1000000)
n,k,m = map(int, sys.argv[1:4]); fixed = sys.argv[4]=='fix'
inputs = tuple(map(int, sys.argv[5].split(','))) if len(sys.argv)>5 else tuple(range(n))
r = n+2*m-k
def first_dup(s):
    for j1 in range(r):
        for j2 in range(j1+1,r):
            if s[j1] is not None and s[j1]==s[j2]: return j1
    return None
def step(c, p):
    A,ps=c; pc,pref,i,out = ps[p]
    A=list(A); ps=list(ps)
    if pc==0:
        A[i]=(pref,p); ps[p]=(1,pref,i,out)
    else:
        s=A; d=first_dup(s)
        if len(set(s))<=m and all(x is not None for x in s):
            ps[p]=(2,pref,i,s[d][0])
        elif all(s[j] not in (None,(pref,p)) for j in range(r) if j!=i) and d is not None and (not fixed or s[d][0]!=pref):
            ps[p]=(0,s[d][0],i,out)
        else:
            ps[p]=(0,pref,(i+1)%r,out)
    return (tuple(A),tuple(ps))
init=(tuple([None]*r), tuple((0,inputs[p],0,None) for p in range(n)))
seen={init}; stack=[init]; order=[]
while stack:
    c=stack.pop(); order.append(c)
    outs={x[3] for x in c[1] if x[0]==2}
    assert all(o in inputs for o in outs)
    if len(outs)>k: print("AGREEMENT VIOLATION",c); sys.exit()
    for p in range(n):
        if c[1][p][0]!=2:
            d=step(c,p)
            if d not in seen: seen.add(d); stack.append(d)
print("reachable",len(seen),"agreement ok")
# fair livelock check: for each P subset size<=m, Tarjan SCC on graph of P-steps of undecided procs
def scc_check(P):
    idx={}; low={}; on=set(); st=[]; counter=[0]; found=[None]
    def succ(c): return [(p,step(c,p)) for p in P if c[1][p][0]!=2]
    for root in seen:
        if root in idx: continue
        # iterative tarjan
        work=[(root,iter(succ(root)))]; idx[root]=low[root]=counter[0]; counter[0]+=1; st.append(root); on.add(root)
        while work:
            v,it=work[-1]
            adv=False
            for p,w in it:
                if w not in idx:
                    idx[w]=low[w]=counter[0]; counter[0]+=1; st.append(w); on.add(w)
                    work.append((w,iter(succ(w)))); adv=True; break
                elif w in on: low[v]=min(low[v],idx[w])
            if adv: continue
            work.pop()
            if work: low[work[-1][0]]=min(low[work[-1][0]],low[v])
            if low[v]==idx[v]:
                comp=set()
                while True:
                    w=st.pop(); on.discard(w); comp.add(w)
                    if w==v: break
                steppers=set()
                for x in comp:
                    for p,y in succ(x):
                        if y in comp: steppers.add(p)
                if steppers and all(x[1][p][0]!=2 for x in comp for p in steppers):
                    # any nonempty set of processes stepping forever in comp, all undecided -> livelock
                    return (steppers, next(iter(comp)))
    return None
for sz in range(1,m+1):
    for P in itertools.combinations(range(n),sz):
        res=scc_check(P)
        if res: print("LIVELOCK P=",P,"steppers",res[0],"at",res[1]); sys.exit()
print("m-OF ok")
