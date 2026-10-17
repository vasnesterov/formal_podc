# Exhaustive model checker for Algorithms 1 and 2 on C_n (local immediate snapshot model).
import sys, itertools, os
SEQ=os.environ.get('SEQ')=='1'

def mex(s):
    i=0
    while i in s: i+=1
    return i

def step1(X, st, nbrs):
    a,b = st
    if (a,b) not in [c for (_,c) in nbrs]: return ('ret',(a,b))
    return ('st',(mex({c[0] for (x,c) in nbrs if x > X}), mex({c[1] for (x,c) in nbrs if x < X})))

def step2(X, st, nbrs):
    a,b = st
    C=set()
    for (_,c) in nbrs: C |= {c[0],c[1]}
    if a not in C: return ('ret',a)
    if b not in C: return ('ret',b)
    Cp=set()
    for (x,c) in nbrs:
        if x > X: Cp |= {c[0],c[1]}
    return ('st',(mex(Cp),mex(C)))

def build(n, Xs, step):
    nb=[((i-1)%n,(i+1)%n) for i in range(n)]
    init=tuple(((0,0),None,None) for _ in range(n))
    succ={init:None}; stack=[init]
    while stack:
        s=stack.pop()
        working=[i for i in range(n) if s[i][2] is None]
        out=[]
        for k in (range(1,len(working)+1) if not SEQ else [1]):
            for S in itertools.combinations(working,k):
                regs=[s[i][1] for i in range(n)]
                for i in S: regs[i]=s[i][0]
                new=list(s)
                for i in S:
                    nv=[(Xs[j],regs[j]) for j in nb[i] if regs[j] is not None]
                    kind,v=step(Xs[i],s[i][0],nv)
                    new[i]=(s[i][0],regs[i],v) if kind=='ret' else (v,regs[i],None)
                t=tuple(new); out.append((S,t))
                if t not in succ: succ[t]=None; stack.append(t)
        succ[s]=out
    return init,succ

def tarjan(succ):
    index={}; low={}; onst=set(); st=[]; comp={}; c=0; idx=0
    for root in succ:
        if root in index: continue
        work=[(root,0)]
        while work:
            v,i=work[-1]
            if i==0:
                index[v]=low[v]=idx; idx+=1; st.append(v); onst.add(v)
            edges=succ[v]
            if i<len(edges):
                work[-1]=(v,i+1)
                w=edges[i][1]
                if w not in index: work.append((w,0))
                elif w in onst: low[v]=min(low[v],index[w])
            else:
                work.pop()
                if work:
                    u=work[-1][0]; low[u]=min(low[u],low[v])
                if low[v]==index[v]:
                    while True:
                        w=st.pop(); onst.discard(w); comp[w]=c
                        if w==v: break
                    c+=1
    return comp  # components numbered in reverse topological order (sinks first)

def analyse(n,Xs,step):
    init,succ=build(n,Xs,step)
    comp=tarjan(succ)
    # check outputs: proper colouring among returned
    bad=None
    outs=set()
    for s in succ:
        for i in range(n):
            if s[i][2] is not None:
                outs.add(s[i][2])
                j=(i+1)%n
                if s[j][2] is not None and s[j][2]==s[i][2]: bad=s
    # longest weighted path per process; cycles with positive weight -> inf
    order=sorted(succ, key=lambda s: comp[s])  # sinks first
    res=[]
    for p in range(n):
        val={}
        inf=False
        for s in order:
            best=0
            for (S,t) in succ[s]:
                wgt=1 if (p in S and s[p][2] is None) else 0
                if comp[t]==comp[s]:
                    if wgt: inf=True
                    continue
                best=max(best,wgt+val[t])
            val[s]=best
        # within-SCC zero-weight edges: need fixpoint
        changed=not inf
        while changed:
            changed=False
            for s in order:
                for (S,t) in succ[s]:
                    wgt=1 if (p in S and s[p][2] is None) else 0
                    if wgt+val[t]>val[s]: val[s]=wgt+val[t]; changed=True
        res.append(float('inf') if inf else val[init])
    return len(succ), bad, outs, res

def mono_dist(Xs,n,p):
    # monotone distances: walk in each direction while monotone
    ds=[]
    for d in (1,-1):
        k=0; i=p
        # determine direction of monotonicity
        while True:
            j=(i+d)%n
            if k>n: break
            if k==0: up = Xs[j]>Xs[i]
            if (Xs[j]>Xs[i])!=up: break
            k+=1; i=j
        ds.append((k,up))
    return ds

if __name__=='__main__':
    alg=sys.argv[1]; n=int(sys.argv[2])
    step={'1':step1,'2':step2}[alg]
    seen=set()
    for perm in itertools.permutations(range(n)):
        # inputs only matter up to edge orientations; canonical by orientation pattern + rotation/reflection
        pat=tuple(perm[i]<perm[(i+1)%n] for i in range(n))
        if pat in seen: continue
        cands=[]
        for r in range(n):
            cands.append(pat[r:]+pat[:r])
        for c in list(cands): cands.append(tuple(not x for x in reversed(c)))
        for c in cands: seen.add(c)
        size,bad,outs,res=analyse(n,perm,step)
        print(perm, 'states',size,'bad',bad is not None,'outs',sorted(outs),'maxact',res, flush=True)
