# Usage: python3 -I genasym.py A|B NMAX   (e.g. NMAX=5; writes treeasym_<case>.pkl, prints counts
# of refuted leaves, invariant leaves and failures; 'fail': 0 means every ordered protocol not
# preserving #S0 - #S1 is refuted on populations <= NMAX). Not part of the Lean development.
# Asymmetric (ordered) version of the case tree search. Table keyed by ORDERED pairs.
import sys, itertools, pickle
NAMES=['S0','S1','X','Y']
UPAIRS=[(i,j) for i in range(4) for j in range(i,4)]
NMAX=int(sys.argv[2])
case=sys.argv[1]
G=[0,1,0,1] if case=='A' else [0,1,1,0]
def avail(c,p,q):
    if c[p]==0: return False
    return c[q]-(1 if p==q else 0)>=1
def fire(c,p,q,a,b):
    e=list(c); e[p]-=1; e[q]-=1; e[a]+=1; e[b]+=1; return tuple(e)
def reach_known(c,tbl):
    par={c:None}; fr=[c]
    while fr:
        nf=[]
        for e in fr:
            for (p,q),(a,b) in tbl.items():
                if avail(e,p,q):
                    f=fire(e,p,q,a,b)
                    if f not in par: par[f]=(e,(p,q)); nf.append(f)
        fr=nf
    return par
def path(par,c):
    res=[]
    while par[c] is not None:
        e,pq=par[c]; res.append(pq); c=e
    return res[::-1]
def closure(c,tbl):
    seen={c}; st=[c]
    while st:
        e=st.pop()
        for p in range(4):
            for q in range(4):
                if avail(e,p,q):
                    if (p,q) not in tbl: return None
                    f=fire(e,p,q,*tbl[(p,q)])
                    if f not in seen: seen.add(f); st.append(f)
    return seen
def allout(c,i): return all(c[s]==0 or G[s]==i for s in range(4))
def find_cert(tbl):
    for n in range(1,NMAX+1):
        inits=[(a,n-a,0,0) for a in range(n+1)]
        R={ab:reach_known(ab,tbl) for ab in inits}
        for (ab,cd) in itertools.combinations(inits,2):
            common=set(R[ab])&set(R[cd])
            if common:
                c=min(common,key=lambda x:len(path(R[ab],x))+len(path(R[cd],x)))
                return ('b2',ab[:2],cd[:2],path(R[ab],c),path(R[cd],c))
        for ab in inits:
            a,b=ab[0],ab[1]
            if a==b: continue
            i=0 if a>b else 1
            for c in sorted(R[ab],key=lambda x:len(path(R[ab],x))):
                F=closure(c,tbl)
                if F is None: continue
                if all(allout(f,1-i) for f in F): return ('safe',i,(a,b),path(R[ab],c),sorted(F))
                if not any(allout(f,i) for f in F): return ('live',i,(a,b),path(R[ab],c),sorted(F))
    return None
def inv_ok(tbl):
    f=lambda a,b: (a==0)-(a==1)+(b==0)-(b==1)
    return all(f(*k)==f(*v) for k,v in tbl.items())
same=[(p,q) for p in range(4) for q in range(4) if G[p]==G[q]]
cross=[(p,q) for p in range(4) for q in range(4) if G[p]!=G[q]]
base={k:(min(k),max(k)) for k in same}
# order: (S0,S1),(S1,S0),(X,Y),(Y,X), then others
order=sorted(cross,key=lambda k:{(0,1):0,(1,0):1,(2,3):2,(3,2):3}.get(k,4+k[0]*4+k[1]))
stats={'leaves':0,'inv':0,'fail':0}
def rec(tbl,rest):
    c=find_cert(tbl)
    if c is not None:
        stats['leaves']+=1; return ('leaf',c)
    if not rest:
        if inv_ok(tbl): stats['inv']+=1; return ('inv',)
        stats['fail']+=1; print('FAIL',tbl); return ('fail',)
    k=rest[0]
    return ('split',k,[(o,rec({**tbl,k:o},rest[1:])) for o in UPAIRS])
t=rec(base,order)
print(case,stats)
pickle.dump(t,open('treeasym_%s.pkl'%case,'wb'))
