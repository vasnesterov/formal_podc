import sys; sys.path.insert(0,'.')
from mc import *; from protos import W, exch
from itertools import combinations_with_replacement as cwr
def rng(k,x,y): return frozenset((x+t)%k for t in range(((y-x)%k)+1))
def sub(k,e,f):
    (x,y),(x2,y2)=e,f
    return rng(k,x,y) <= rng(k,x2,y2) and (x!=y2 or y!=x2)
def psub(k,e,f): return sub(k,e,f) and rng(k,*e)!=rng(k,*f)
def tieshare(k):
    def d(p,q):
        e,f,ex=exch(k,(p[0],p[1]),(q[0],q[1]))
        S=[p[3],q[3]]; O=[p[2],q[2]]; B=[e,f]; P=[(p[0],p[1]),(q[0],q[1])]
        dg=lambda z: z[0]==z[1]
        for a in (0,1):
            if ex and not dg(B[a]): S[a]='WS'
        for a in (0,1):
            if not dg(P[a]) and dg(B[a]): S[a]='W'
        for a,b in ((0,1),(1,0)):
            if dg(B[a]):
                i=B[a][0]
                if B[b][0]==i: S[b]='W'
                elif B[b][0] not in (i,B[b][1]): S[b]='L'
        for a,b in ((0,1),(1,0)):
            if S[a]=='WS' and S[b]=='L' and B[b][0]==B[a][1]: S[b]='WS'
        for a,b in ((0,1),(1,0)):
            if S[a]=='WS' and psub(k,B[a],B[b]):
                S[b]='WS'; S[a]='W' if B[a][0]==B[b][0] else 'L'
        for a,b in ((0,1),(1,0)):
            if S[a]=='WS' and S[b]=='WS' and sub(k,B[a],B[b]):
                S[a]='W' if B[a][0]==B[b][0] else 'L'
        for a,b in ((0,1),(1,0)):
            if S[a]=='WS':
                if B[b][0]==B[a][0]: S[b]='W'
                elif psub(k,B[b],B[a]): S[b]='L'
        for a,b in ((0,1),(1,0)):
            if dg(B[a]) and not dg(B[b]): O[b]=B[a][0]
        for a,b in ((0,1),(1,0)):
            if S[a]=='WS' and sub(k,B[b],B[a]): O[b]=B[a][0]
        return (e[0],e[1],O[0],S[0]),(f[0],f[1],O[1],S[1])
    return d
fails=[]
for k in [2,3]:
    for n in range(1,6 if k==2 else 5):
        for c in cwr(range(k),n):
            x=[c.count(i) for i in range(k)]; m=max(x); M=[i for i in range(k) if x[i]==m]
            bad=lambda C: any((s[0] in M and s[3]=='L') or (s[0] not in M and s[3]!='L') or (s[3]=='L' and s[2] not in M) for s in C)
            ok,b,N,confs,edges=check(tuple((i,i,i,'W') for i in c),tieshare(k),n,bad)
            if not ok:
                fails.append((k,c)); 
                if len(fails)<=3: print(k,c,b,path_to(confs,edges,b))
print(len(fails),fails)
