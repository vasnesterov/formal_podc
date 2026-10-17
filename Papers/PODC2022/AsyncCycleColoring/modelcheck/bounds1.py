import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mc12 import *
def dists(Xs,n,p):
    l=r=None
    up=[i for i in ((p-1)%n,(p+1)%n) if Xs[i]>Xs[p]]
    if len(up)!=1: return None
    # walk up
    def walk(start,prev,inc):
        k=1; cur=start; pr=prev
        while True:
            nxt=[i for i in ((cur-1)%n,(cur+1)%n) if i!=pr][0]
            if (Xs[nxt]>Xs[cur])!=inc: return k
            pr,cur=cur,nxt; k+=1
    dn=[i for i in ((p-1)%n,(p+1)%n) if Xs[i]<Xs[p]][0]
    return walk(up[0],p,True), walk(dn,p,False)
n=int(sys.argv[1])
seen=set()
for perm in itertools.permutations(range(n)):
    pat=tuple(perm[i]<perm[(i+1)%n] for i in range(n))
    if pat in seen: continue
    cands=[pat[r:]+pat[:r] for r in range(n)]
    cands+= [tuple(not x for x in reversed(c)) for c in cands]
    seen.update(cands)
    size,bad,outs,res=analyse(n,perm,step1)
    info=[]
    for p in range(n):
        d=dists(perm,n,p)
        bnd = 4 if d is None else min(3*d[0],3*d[1],d[0]+d[1])+4
        info.append((res[p],d,bnd, 'VIOL' if res[p]>bnd else ''))
    print(perm,size,bad is not None,info,flush=True)
