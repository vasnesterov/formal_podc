import sys, itertools, random
INF=10**9
def mex(s):
    i=0
    while i in s: i+=1
    return i
def blen(z): return z.bit_length()
def f(x,y):
    i=min(blen(x),blen(y))
    k=0
    while k<i:
        if (x>>k)&1 != (y>>k)&1: i=k; break
        k+=1
    return 2*i+((x>>i)&1)
def step3(st, nbrs):
    # st=(X,r,a,b); nbrs list of registers (X,r,a,b) or None (bottom); two entries
    X,r,a,b=st
    aw=[u for u in nbrs if u is not None]
    C=set()
    for u in aw: C|={u[2],u[3]}
    if a not in C: return ('ret',a)
    if b not in C: return ('ret',b)
    Cp=set()
    for u in aw:
        if u[0]>X: Cp|={u[2],u[3]}
    na=mex(Cp); nb=mex(C); nX=X; nr=r
    rs=[(-1 if u is None else u[1]) for u in nbrs]
    if r<INF and r<=min(rs):
        Xs=[u[0] for u in nbrs]  # all awake here since r>=0 > -1
        lo,hi=min(Xs),max(Xs)
        if lo<X<hi:
            nr=r+1
            Y=f(X,lo)
            if Y<lo: nX=Y
        else:
            nr=INF
            if X<lo: nX=min(X,mex({f(Xs[0],X),f(Xs[1],X)}))
    return ('st',(nX,nr,na,nb))
def succs(n,s,seq=False):
    working=[i for i in range(n) if s[i][2] is None]
    for k in ([1] if seq else range(1,len(working)+1)):
        for S in itertools.combinations(working,k):
            regs=[s[i][1] for i in range(n)]
            for i in S: regs[i]=s[i][0]
            new=list(s)
            for i in S:
                kind,v=step3(s[i][0],[regs[(i-1)%n],regs[(i+1)%n]])
                new[i]=(s[i][0],regs[i],v) if kind=='ret' else (v,regs[i],None)
            yield S,tuple(new)
def check45(n,s):
    for p in range(n):
        q=(p+1)%n
        rp,rq=s[p][1],s[q][1]
        if rp is not None and rq is not None and rp[0]==rq[0]: return 'reg'
        # stronger: X_p(t) not in {X_q(t), Xhat_q(t)}
        if s[p][0][0]==s[q][0][0]: return 'loc'
    return None
