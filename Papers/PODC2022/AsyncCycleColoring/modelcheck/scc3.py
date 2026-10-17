import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from alg3 import *
import mc12, random
def build(n,ids,seq=False,cap=400000):
    init=tuple(((ids[i],0,0,0),None,None) for i in range(n))
    succ={init:None}; stack=[init]; viol=None
    while stack:
        s=stack.pop()
        out=list(succs(n,s,seq))
        for S,t in out:
            c=check45(n,t)
            if c and viol is None: viol=(c,t)
            if t not in succ:
                succ[t]=None; stack.append(t)
        succ[s]=out
        if len(succ)>cap: return None,None,'cap'
    return init,succ,viol
def analyse(n,ids,seq=False):
    init,succ,viol=build(n,ids,seq)
    if init is None: return 'cap'
    comp=mc12.tarjan(succ)
    order=sorted(succ,key=lambda s:comp[s])
    res=[]
    for p in range(n):
        inf=False; val={}
        for s in order:
            best=0
            for (S,t) in succ[s]:
                w=1 if (p in S and s[p][2] is None) else 0
                if comp[t]==comp[s]:
                    if w: inf=True
                    continue
                best=max(best,w+val[t])
            val[s]=best
        ch=not inf
        while ch:
            ch=False
            for s in order:
                for (S,t) in succ[s]:
                    w=1 if (p in S and s[p][2] is None) else 0
                    if w+val[t]>val[s]: val[s]=w+val[t]; ch=True
        res.append(float('inf') if inf else val[init])
    return len(succ),viol,res
random.seed(int(sys.argv[3]))
n=int(sys.argv[1]); trials=int(sys.argv[2]); hi=int(sys.argv[4]); seq=len(sys.argv)>5
for _ in range(trials):
    while True:
        ids=[random.randrange(hi) for _ in range(n)]
        if all(ids[i]!=ids[(i+1)%n] for i in range(n)): break
    print(ids, analyse(n,ids,seq), flush=True)
