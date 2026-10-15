import sys, itertools
from collections import deque
sys.setrecursionlimit(1000000)
# state: (bc, br, kr, kc, t)
def W(k,i,j): return k if i==j else (j-i)%k

def cases(k, variant):
    # each case: function (X,Y) -> (X',Y') (possibly unchanged)
    def r2(X,Y):
        (j,jr,ir,i,t1),(l,lr,ir2,i2,t2)=X,Y
        if t1 and t2 and i==i2 and jr<=lr: return X,(l,lr,ir,i,0)
        return X,Y
    def r3(X,Y):
        (j,jr,ir,i,t1),(l,lr,ur,u,t2)=X,Y
        if t1 and t2 and ir==ur and i<u: return X,(l,lr,(ur+1)%k,u,1)
        return X,Y
    def r4a(X,Y):
        (i,ir,jr,j,t1),(u,ur,jr2,j2,t2)=X,Y
        if t1 and not t2 and j==j2: return X,(u,ur,jr,j,0)
        return X,Y
    def r4b(X,Y):
        (i,ir,jr,j,t1),(j2,jr2,ur,u,t2)=X,Y
        if t1 and j2==j: return X,(j,jr,ur,u,t2)
        return X,Y
    def r5(X,Y):
        (i,ir,jr,j,t1),(u,ur,vr,v,t2)=X,Y
        if min(W(k,ir,vr),W(k,ur,jr)) < min(W(k,ir,jr),W(k,ur,vr)):
            return (i,ir,vr,v,t2),(u,ur,jr,j,t1)
        return X,Y
    def r6a(X,Y):
        (i,ir,ir2,i2,t1),(l,lr,ir3,i3,t2)=X,Y
        if i==i2 and ir==ir2 and not t1 and t2 and ir3==ir and i3==i:
            return (i,ir,ir,i,1),(l,lr,ir,i,0)
        return X,Y
    def r6b(X,Y):
        (j,jr,ir,i,t1),(l,lr,ir2,i2,t2)=X,Y
        if not t1 and t2 and i==i2 and ir==ir2 and j!=i and l!=i and jr<lr:
            return (j,jr,ir,i,1),(l,lr,ir,i,0)
        return X,Y
    def r7a(X,Y):
        (i,ir,ir2,i2,t1),(u,ur,zr,v,t2)=X,Y
        if t1 and t2 and i==i2 and ir==ir2 and zr==0 and v!=i and ir!=0:
            return (i,0,0,i,1),(u,ur,ir,v,1)
        return X,Y
    def r7b(X,Y):
        (i,ir,jr,j,t1),(i2,ir2,lr,l,t2)=X,Y
        if t1 and t2 and i==i2 and ir==ir2 and j!=i and l!=i and (variant.get('r7nz') is None or (jr!=0 and lr!=0)):
            return (i,ir,lr,j,1),(i,ir,jr,l,1)
        return X,Y
    return [r2,r3,r4a,r4b,r5,r6a,r6b,r7a,r7b]

def make_delta(k, variant):
    cs = cases(k, variant)
    orient = variant.get('orient','both')
    def norm(s):
        if variant.get('selfsync') and s[4] and s[0]==s[3]: return (s[0],s[2],s[2],s[3],s[4])
        return s
    def d(a,b):
        p,q=d0(a,b); return norm(p),norm(q)
    def d0(a,b):
        if orient=='both':
            for c in cs:
                X,Y=c(a,b)
                if (X,Y)!=(a,b): return X,Y
                Y,X=c(b,a)
                if (X,Y)!=(a,b): return X,Y
            return a,b
        elif orient=='init':
            for c in cs:
                X,Y=c(a,b)
                if (X,Y)!=(a,b): return X,Y
            return a,b
        elif orient=='bothlater':  # all cases (a,b) first then (b,a)
            for c in cs:
                X,Y=c(a,b)
                if (X,Y)!=(a,b): return X,Y
            for c in cs:
                Y,X=c(b,a)
                if (X,Y)!=(a,b): return X,Y
            return a,b
    return d

def rank_of(x):
    k=len(x); return [sum(1 for l in range(k) if x[l]>x[i]) for i in range(k)]

def check(x, variant, limit=5_000_000, verbose=False):
    k=len(x); d=make_delta(k,variant); r=rank_of(x)
    init=tuple(sorted((i,i,i,i,1) for i in range(k) for _ in range(x[i])))
    n=len(init)
    idx={init:0}; confs=[init]; edges=[]
    cache={}
    stack=[0]
    while stack:
        v=stack.pop(); c=confs[v]; out=set()
        distinct=sorted(set(c))
        for ai,a in enumerate(distinct):
            for b in distinct:
                if a==b and c.count(a)<2: continue
                key=(a,b)
                if key in cache: p,q=cache[key]
                else: p,q=d(a,b); cache[key]=(p,q)
                if (p,q)==(a,b): continue
                l=list(c); l.remove(a); l.remove(b); l.append(p); l.append(q); nc=tuple(sorted(l))
                if nc==c: continue
                j=idx.get(nc)
                if j is None:
                    j=len(confs); idx[nc]=j; confs.append(nc); stack.append(j)
                    if len(confs)>limit: raise Exception('limit')
                out.add(j)
        while len(edges)<=v: edges.append(None)
        edges[v]=list(out)
    N=len(confs)
    # tarjan iterative
    index=[None]*N; low=[0]*N; onst=[False]*N; st=[]; comp=[None]*N; comps=[]; cnt=0
    for s in range(N):
        if index[s] is not None: continue
        work=[(s,0)]; index[s]=low[s]=cnt; cnt+=1; st.append(s); onst[s]=True
        while work:
            v,pi=work[-1]; es=edges[v]
            if pi<len(es):
                work[-1]=(v,pi+1); w=es[pi]
                if index[w] is None:
                    index[w]=low[w]=cnt; cnt+=1; st.append(w); onst[w]=True; work.append((w,0))
                elif onst[w]: low[v]=min(low[v],index[w])
            else:
                work.pop()
                if work: u=work[-1][0]; low[u]=min(low[u],low[v])
                if low[v]==index[v]:
                    cid=len(comps); mem=[]
                    while True:
                        w=st.pop(); onst[w]=False; comp[w]=cid; mem.append(w)
                        if w==v: break
                    comps.append(mem)
    bad=lambda c: any(s[1]!=r[s[0]] for s in c)
    res=[]
    nbottom=0
    for cid,mem in enumerate(comps):
        if all(comp[w]==cid for v in mem for w in edges[v]):
            nbottom+=1
            bm=[confs[v] for v in mem if bad(confs[v])]
            if bm: res.append((len(mem),bm[0]))
    return N, nbottom, res, confs, edges

if __name__=='__main__':
    pass

def path_to(confs, edges, target):
    prev={0:None}; dq=deque([0]); tgt=confs.index(target)
    while dq:
        v=dq.popleft()
        if v==tgt: break
        for w in edges[v]:
            if w not in prev: prev[w]=v; dq.append(w)
    p=[]; v=tgt
    while v is not None: p.append(confs[v]); v=prev[v]
    return list(reversed(p))
def fmt(s):
    return '<%d,%d|%d,%d>%s'%(s[0],s[1],s[2],s[3],'*' if s[4] else '')
