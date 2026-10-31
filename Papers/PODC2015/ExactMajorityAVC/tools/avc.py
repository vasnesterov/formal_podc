# Model checker for AVC (Figure 1), as printed (literal=True) and corrected (literal=False).
# For small (n, m, d) it checks the sum invariant and that from every configuration with nonzero
# sum, every reachable configuration can still reach "all signs = sign of the sum" (which must be
# closed). Prints, per parameter set, the number of failing initial configurations and one example.
# Usage: python3 -I avc.py   (not part of the Lean development)
import sys, itertools
from collections import deque
# state: (sign, weight, level) ; sign in {+1,-1}; weight 0, 1, or odd 3..m ; level only for weight 1 (1..d) else 0
def states(m,d):
    S=[]
    for s in (1,-1):
        S.append((s,0,0))
        for j in range(1,d+1): S.append((s,1,j))
        for w in range(3,m+1,2): S.append((s,w,0))
    return S
def value(x): return x[0]*x[1]
def phi(k):
    if k==1: return (1,1,1)
    if k==-1: return (-1,1,1)
    return (1 if k>0 else -1, abs(k), 0)
def Rdown(k): return phi(k if k%2 else k-1)
def Rup(k): return phi(k if k%2 else k+1)
def shift(x,d):
    if x[1]==1 and x[2]<d: return (x[0],1,x[2]+1)
    return x
def s2z(x): return (1,0,0) if x[0]>0 else (-1,0,0)
def update(x,y,d,literal):
    wx,wy=x[1],y[1]
    if (wx>0 and wy>1) or (wy>0 and wx>1):
        a=(value(x)+value(y))//2
        return Rdown(a),Rup(a)
    cond = (value(x)+value(y)>0) if literal else (wx+wy>0)
    if wx*wy==0 and cond:
        if wx!=0: return shift(x,d), s2z(x)
        else: return s2z(y), shift(y,d)
    if (x[1]==1 and x[2]==d and wy==1 and x[0]!=y[0]) or (y[1]==1 and y[2]==d and wx==1 and x[0]!=y[0]):
        return (-1,0,0),(1,0,0)
    return shift(x,d), shift(y,d)
def check(n,m,d,literal):
    S=states(m,d); idx={s:i for i,s in enumerate(S)}
    def succ(c):
        res=set()
        for i in range(len(S)):
            if c[i]==0: continue
            for j in range(len(S)):
                if c[j]-(1 if i==j else 0)<=0: continue
                x,y=update(S[i],S[j],d,literal)
                l=list(c); l[i]-=1; l[j]-=1; l[idx[x]]+=1; l[idx[y]]+=1
                res.add(tuple(l))
        return res
    bad=[]
    allc=[c for c in itertools.product(range(n+1),repeat=len(S)) if sum(c)==n]
    # sum invariant check
    for c in allc:
        sm=sum(c[i]*value(S[i]) for i in range(len(S)))
        for c2 in succ(c):
            assert sum(c2[i]*value(S[i]) for i in range(len(S)))==sm, (c,c2)
    for c in allc:
        sm=sum(c[i]*value(S[i]) for i in range(len(S)))
        if sm==0: continue
        sg=1 if sm>0 else -1
        good=lambda e: all(e[i]==0 or S[i][0]==sg for i in range(len(S)))
        # reachable set
        seen={c}; dq=deque([c])
        while dq:
            e=dq.popleft()
            for f in succ(e):
                if f not in seen: seen.add(f); dq.append(f)
        # each reachable must reach good
        # backward: compute set that can reach good within seen
        canr={e for e in seen if good(e)}
        changed=True
        while changed:
            changed=False
            for e in seen:
                if e not in canr and any(f in canr for f in succ(e)):
                    canr.add(e); changed=True
        if canr!=seen:
            bad.append((c,[e for e in seen if e not in canr][:1]))
        # closure of good
        for e in seen:
            if good(e):
                for f in succ(e): assert good(f)
    return S,bad
for literal in (True,False):
  for (n,m,d) in [(2,1,1),(3,1,1),(3,3,1),(3,3,2),(4,3,1),(3,5,1),(4,3,2),(5,3,1),(4,5,2)]:
    S,bad=check(n,m,d,literal)
    print(literal,n,m,d,len(bad), [ ( {S[i]:c[i] for i in range(len(S)) if c[i]}, {S[i]:e[0][i] for i in range(len(S)) if e[0][i]}) for c,e in bad[:1]])
