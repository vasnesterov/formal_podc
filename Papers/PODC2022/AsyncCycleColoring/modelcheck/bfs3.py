import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from alg3 import *
from rand3b import chk
import random
random.seed(int(sys.argv[1])); n=int(sys.argv[2]); trials=int(sys.argv[3]); cap=int(sys.argv[4])
for _ in range(trials):
    hi=random.choice([16,64,1024,10**6])
    while True:
        ids=[random.randrange(hi) for _ in range(n)]
        if all(ids[i]!=ids[(i+1)%n] for i in range(n)): break
    init=tuple(((ids[i],0,0,0),None,None) for i in range(n))
    seen={init}; st=[init]; bad=None
    while st and len(seen)<cap:
        s=st.pop()
        for S,t in succs(n,s):
            if t not in seen:
                b=chk(n,t)
                if b: bad=(b,t); break
                seen.add(t); st.append(t)
        if bad: break
    print(ids,len(seen),bad,flush=True)
