import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sys
from mc12 import *
from collections import deque
def lasso(n,Xs,step,p):
    init,succ=build(n,Xs,step)
    comp=tarjan(succ)
    # find edge s->t in same SCC with p activated & working
    for s in succ:
        for (S,t) in succ[s]:
            if comp[s]==comp[t] and p in S and s[p][2] is None:
                # path init->s, then t->s
                def path(a,b,restrict=None):
                    prev={a:None}; q=deque([a])
                    while q:
                        u=q.popleft()
                        if u==b: break
                        for (S2,v) in succ[u]:
                            if restrict is not None and comp[v]!=restrict: continue
                            if v not in prev: prev[v]=(u,S2); q.append(v)
                    out=[]; u=b
                    while prev[u] is not None:
                        u0,S2=prev[u]; out.append((S2,u)); u=u0
                    return out[::-1]
                return init, path(init,s), (S,t), path(t,s,comp[s])
alg=sys.argv[1]; n=int(sys.argv[2]); Xs=tuple(map(int,sys.argv[3].split(','))); p=int(sys.argv[4])
step={'1':step1,'2':step2}[alg]
init,pre,e,cyc=lasso(n,Xs,step,p)
print('init',init)
for S,s in pre: print('prefix step',S,'->',s)
print('LOOP')
print('step',e[0],'->',e[1])
for S,s in cyc: print('step',S,'->',s)
