# Explicit-state model checker for Optimal-Silent-SSR (Protocols 2-4), reachability semantics.
# Usage: python3 oss.py n Rmax Dmax Emax fixed   (fixed=0: printed guard `<`, fixed=1: `<=`)
# Counts the configurations (multisets) from which no correctly ranked configuration is reachable.
# The transition function agrees with `OptimalSilent.δ` (checked on all pairs for n=3,Rmax=2,Dmax=3,Emax=2).
import sys, itertools
from collections import deque
n, Rmax, Dmax, Emax, fixed = map(int, sys.argv[1:6])
# states: ('S',rank,children) ('U',ec) ('R',leader,rc,dt)   leader: 1=L 0=F
def reset(i):
    if i[1]==1: return ('S',1,0)
    return ('U',Emax)
def prop_reset(a,b):
    # a Resetting. returns (a,b)
    a=list(a); b=list(b) if b[0]=='R' else b
    if a[2]>0 and b[0]!='R':
        b=['R',1,0,Dmax]   # brought in, leader L (text: all set to L upon entering Resetting)
    old=[a[2], b[2] if b[0]=='R' else None]
    if b[0]=='R':
        m=max(a[2]-1,b[2]-1,0); a[2]=m; b[2]=m
    res=[a,b]
    other_comp=[res[1][0]!='R', res[0][0]!='R']
    for k in (0,1):
        i=res[k]
        if i[0]=='R' and i[2]==0:
            if old[k] is not None and old[k]>0:
                i[3]=Dmax
            else:
                i[3]=max(i[3]-1,0)
            # other agent role (after possible reset of first)
            oth = res[1-k]
            if i[3]==0 or (oth[0]!='R'):
                res[k]=list(reset(i))
    return tuple(res[0]), tuple(res[1])
def step(a,b):
    a=tuple(a); b=tuple(b)
    if a[0]=='R' or b[0]=='R':
        if a[0]=='R': a,b = prop_reset(a,b)
        else: b,a = prop_reset(b,a)
        if a[0]=='R' and b[0]=='R' and a[1]==1 and b[1]==1:
            b=('R',0,b[2],b[3])
    if a[0]=='S' and b[0]=='S' and a[1]==b[1]:
        a=('R',1,Rmax,Dmax); b=('R',1,Rmax,Dmax)
    ag=[a,b]
    for (x,y) in ((0,1),(1,0)):
        i,j=ag[x],ag[y]
        if i[0]=='S' and j[0]=='U' and i[2]<2 and (2*i[1]+i[2] <= n if fixed else 2*i[1]+i[2] < n):
            ag[y]=('S',2*i[1]+i[2],0); ag[x]=('S',i[1],i[2]+1)
    for x in (0,1):
        i=ag[x]
        if i[0]=='U':
            e=max(i[1]-1,0); ag[x]=('U',e)
            if e==0:
                ag=[('R',1,Rmax,Dmax),('R',1,Rmax,Dmax)]
                break
    return ag[0],ag[1]
states=[('S',r,c) for r in range(1,n+1) for c in range(3)]+[('U',e) for e in range(Emax+1)]+[('R',l,rc,dt) for l in (0,1) for rc in range(Rmax+1) for dt in range(Dmax+1)]
def good(C): return all(s[0]=='S' for s in C) and sorted(s[1] for s in C)==list(range(1,n+1))
def succ(C):
    out=set()
    for i in range(n):
        for j in range(n):
            if i!=j:
                a,b=step(C[i],C[j]); D=list(C); D[i]=a; D[j]=b
                out.add(tuple(sorted(D)))
    return out
states.sort()
configs=list(itertools.combinations_with_replacement(states,n))
idx={c:k for k,c in enumerate(configs)}
print("configs",len(configs))
# backward reachability from good
pred=[[] for _ in configs]
for k,C in enumerate(configs):
    for D in succ(C): pred[idx[D]].append(k)
canreach=[False]*len(configs); dq=deque()
for k,C in enumerate(configs):
    if good(C): canreach[k]=True; dq.append(k)
# closedness of good
for k,C in enumerate(configs):
    if good(C):
        assert all(good(D) for D in succ(C)), C
while dq:
    k=dq.popleft()
    for p in pred[k]:
        if not canreach[p]: canreach[p]=True; dq.append(p)
bad=[configs[k] for k in range(len(configs)) if not canreach[k]]
print("cannot reach stable:",len(bad))
for b in bad[:5]: print(b)
