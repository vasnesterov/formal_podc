# Brute force over symmetric four-state protocols with gamma(S0)=gamma(X)=0, gamma(S1)=gamma(Y)=1,
# same-output pairs fixed as in Claim B.5: lists the protocols that satisfy the second and third
# correctness properties on all populations of size <= N, and whether they preserve #S0 - #S1.
# Usage: python3 -I b1.py N   (not part of the Lean development)
import sys, itertools
from functools import lru_cache
# states 0=S0 1=S1 2=X 3=Y ; gamma
G=[0,1,0,1]
NAMES=['S0','S1','X','Y']
PAIRS=[(i,j) for i in range(4) for j in range(i,4)]
OUT=PAIRS
same=[(0,0),(0,2),(2,2),(1,1),(1,3),(3,3)]
cross=[(0,1),(0,3),(1,2),(2,3)]
def mkdelta(t):
    d={p:[p] for p in same}
    for p,o in zip(cross,t): d[p]=o if isinstance(o,list) else [o]
    return d
def succ(c,d):
    res=set()
    for (i,j),outs in d.items():
        if c[i]==0 or c[j]-(1 if i==j else 0)<=0: continue
        for (k,l) in outs:
            e=list(c); e[i]-=1; e[j]-=1; e[k]+=1; e[l]+=1
            res.add(tuple(e))
    return res
def reach(c,d):
    seen={c}; st=[c]
    while st:
        e=st.pop()
        for f in succ(e,d):
            if f not in seen: seen.add(f); st.append(f)
    return seen
def allout(c,i): return all(c[s]==0 or G[s]==i for s in range(4))
def correct(d,N):
    for n in range(1,N+1):
        cache={}
        def R(c):
            if c not in cache: cache[c]=frozenset(reach(c,d))
            return cache[c]
        for z in range(n+1):
            if 2*z==n: continue
            i=0 if 2*z>n else 1
            init=(z,n-z,0,0)
            Rs=R(init)
            for c in Rs:
                # P2: c not in C_{1-i}
                if all(allout(e,1-i) for e in R(c)): return (n,z,'P2',c)
                # P3: c can reach C_i
                if not any(all(allout(f,i) for f in R(e)) for e in R(c)): return (n,z,'P3',c)
    return None
def inv(d):
    for (i,j),outs in d.items():
        for (k,l) in outs:
            f=lambda a,b: (a==0)-(a==1)+(b==0)-(b==1)
            if f(i,j)!=f(k,l): return False
    return True
N=int(sys.argv[1])
surv=[]; bad=[]
for t in itertools.product(OUT,repeat=4):
    d=mkdelta(t)
    r=correct(d,N)
    if r is None:
        surv.append(t)
        if not inv(d): bad.append(t)
print("survivors",len(surv),"noninv",len(bad))
for t in surv: print([ (NAMES[p[0]]+NAMES[p[1]], NAMES[o[0]]+NAMES[o[1]]) for p,o in zip(cross,t)], inv(mkdelta(t)))
