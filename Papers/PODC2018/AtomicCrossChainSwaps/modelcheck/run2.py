import sys, itertools, time
sys.path.insert(0, sys.argv[1])
from swap import *
n=int(sys.argv[2]); variants=sys.argv[3].split(','); Bs=[int(x) for x in sys.argv[4].split(',')]; rush=sys.argv[5]=='1'
allarcs=[(a,b) for a in range(n) for b in range(n) if a!=b]
def reach(arcs,s):
    R={s};ch=True
    while ch:
        ch=False
        for a,b in arcs:
            if a in R and b not in R: R.add(b);ch=True
    return R
def sc(arcs): return all(reach(arcs,s)==set(range(n)) for s in range(n))
def acyclic_without(arcs,L):
    F=[v for v in range(n) if v not in L]
    fa=[(a,b) for a,b in arcs if a in F and b in F]
    # cycle detection
    for v in F:
        R=set();fr=[b for a,b in fa if a==v]
        while fr:
            x=fr.pop()
            if x==v: return False
            if x in R: continue
            R.add(x); fr+= [b for a,b in fa if a==x]
    return True
seen_graphs=set()
for r in range(n, len(allarcs)+1):
  for arcs in itertools.combinations(allarcs,r):
    if not sc(arcs): continue
    # canonical up to iso
    can=min(tuple(sorted((p[a],p[b]) for a,b in arcs)) for p in itertools.permutations(range(n)))
    if can in seen_graphs: continue
    seen_graphs.add(can)
    for k in range(1,n+1):
      for L in itertools.permutations(range(n),k):
        if list(L)!=sorted(L): continue
        if not acyclic_without(arcs,L): continue
        for c in range(1,n):
          for C in itertools.combinations(range(n),c):
            for B in Bs:
              for var in variants:
                I=Inst(n,arcs,L,C,B,var,rush)
                t0=time.time()
                res=search(I)
                print('inst',var,B,arcs,L,C,'res' if res else 'ok',round(time.time()-t0,1),flush=True)
                if res:
                    print('FOUND',var,'B=',B,'arcs',arcs,'L',L,'C',C,res if res=='limit' else (res[0],sorted(res[1]),res[2]),flush=True)
print('done',len(seen_graphs))
