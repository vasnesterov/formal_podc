# Helpers (certificate search) used by gen2.py; run alone it builds an unoptimised case tree.
# Usage: python3 -I gen.py A|B [NMAX]   (A: gamma(X)=0, B: gamma(X)=1; writes tree_<case>.pkl)
# Generate the case tree for Theorem B.1 (symmetric protocols, after Claim B.5).
import sys, itertools
NAMES=['S0','S1','X','Y']
UPAIRS=[(i,j) for i in range(4) for j in range(i,4)]
NMAX=int(sys.argv[2]) if len(sys.argv)>2 else 5
def cnt(a,b): return (a,b,0,0)
def avail(c,p,q):
    if c[p]==0: return False
    return c[q]-(1 if p==q else 0)>=1
def fire(c,p,q,a,b):
    e=list(c); e[p]-=1; e[q]-=1; e[a]+=1; e[b]+=1; return tuple(e)
def succs(c,tbl):
    """returns list of (pair,(p,q)) successors or None if some applicable pair unknown"""
    res=[]
    for p in range(4):
        for q in range(4):
            if avail(c,p,q):
                k=(min(p,q),max(p,q))
                if k not in tbl: return None
                a,b=tbl[k]
                res.append(((p,q),fire(c,p,q,a,b)))
    return res
def reach_known(c,tbl):
    """BFS using only known pairs; returns dict config -> (parent, pair)"""
    par={c:None}; fr=[c]
    while fr:
        nf=[]
        for e in fr:
            for p in range(4):
                for q in range(p,4):
                    if avail(e,p,q) and (p,q) in tbl:
                        a,b=tbl[(p,q)]
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
        s=succs(e,tbl)
        if s is None: return None
        for _,f in s:
            if f not in seen: seen.add(f); st.append(f)
    return seen
def allout(c,i,G): return all(c[s]==0 or G[s]==i for s in range(4))
def find_cert(tbl,G):
    for n in range(1,NMAX+1):
        inits=[(a,n-a) for a in range(n+1)]
        R={ab:reach_known(cnt(*ab),tbl) for ab in inits}
        # b2
        for (ab,cd) in itertools.combinations(inits,2):
            common=set(R[ab])&set(R[cd])
            if common:
                c=min(common,key=lambda x:len(path(R[ab],x))+len(path(R[cd],x)))
                return ('b2',ab,cd,path(R[ab],c),path(R[cd],c))
        for (a,b) in inits:
            if a==b: continue
            i=0 if a>b else 1
            for c in sorted(R[(a,b)],key=lambda x:len(path(R[(a,b)],x))):
                F=closure(c,tbl)
                if F is None: continue
                if all(allout(f,1-i,G) for f in F):
                    return ('safe',i,(a,b),path(R[(a,b)],c),sorted(F))
                if not any(allout(f,i,G) for f in F):
                    return ('live',i,(a,b),path(R[(a,b)],c),sorted(F))
    return None
def inv_ok(tbl):
    f=lambda a,b: (a==0)-(a==1)+(b==0)-(b==1)
    return all(f(*k)==f(*v) for k,v in tbl.items())
def build(G,cross,same):
    base={k:k for k in same}
    stats={'leaves':0,'inv':0}
    def rec(tbl,rest):
        c=find_cert(tbl,G)
        if c is not None:
            stats['leaves']+=1
            return ('leaf',c)
        if not rest:
            if inv_ok(tbl):
                stats['inv']+=1; return ('inv',dict(tbl))
            raise Exception("no cert and not inv: %s"%tbl)
        k=rest[0]
        ch=[]
        for o in UPAIRS:
            t2=dict(tbl); t2[k]=o
            ch.append((o,rec(t2,rest[1:])))
        return ('split',k,ch)
    return rec(base,cross),stats
if __name__=='__main__':
    case=sys.argv[1]
    if case=='A': G=[0,1,0,1]
    else: G=[0,1,1,0]
    same=[k for k in UPAIRS if G[k[0]]==G[k[1]]]
    cross=[k for k in UPAIRS if G[k[0]]!=G[k[1]]]
    # order: (S0,S1) first, then (X,Y), then others
    cross=sorted(cross,key=lambda k:{(0,1):0,(2,3):1}.get(k,2))
    tree,stats=build(G,cross,same)
    print(stats)
    import pickle; pickle.dump(tree,open('tree_%s.pkl'%case,'wb'))
