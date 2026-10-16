import sys
sys.path.insert(0, sys.argv[1])
from swap import *
K3=[(0,1),(1,0),(1,2),(2,1),(0,2),(2,0)]
for (n,arcs,L,C,B,var,rush) in [(3,K3,[0,1],[0],4,'literal',False),
                                (2,[(0,1),(1,0)],[0],[1],3,'literal',True),
                                (3,[(0,1),(1,2),(2,0)],[0],[1,2],4,'literal',False),
                                (3,[(0,1),(1,2),(2,0)],[0],[1,2],4,'fixed',False)]:
    I=Inst(n,arcs,L,C,B,var,rush)
    r=search(I)
    print(n,arcs,L,C,B,var,rush)
    if r and r!='limit':
        for x in r[0]:
            if x[1] or x[2]: print('  ',x)
        print('  trig',sorted(r[1]),'bad',r[2])
    else: print('  ',r)
