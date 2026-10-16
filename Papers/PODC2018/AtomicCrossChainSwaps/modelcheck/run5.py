import sys
sys.path.insert(0, sys.argv[1])
import swap
def strict(arcs, p):
    if len(p)==0: return False
    for a,b in zip(p,p[1:]):
        if (a,b) not in arcs: return False
    body=p[:-1]
    if len(set(body))!=len(body): return False
    return p[-1] not in body or p[-1]==p[0]
swap.lax_path=strict
from swap import *
K3=[(0,1),(1,0),(1,2),(2,1),(0,2),(2,0)]
for C in [(0,),(1,),(2,),(0,1),(0,2),(1,2)]:
  for L in [[0,1],[0,1,2]]:
    I=Inst(3,K3,L,C,4,'fixed',False)
    r=search(I)
    print(C,L, r if r in (None,'limit') else ([x for x in r[0] if x[1] or x[2]], sorted(r[1]), r[2]),flush=True)
