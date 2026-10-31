import sys, os
from collections import deque
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'mutex_model.py')).read())
m=int(sys.argv[1]); H,locs,succ=mk_model(m)
pis=(tuple(range(m)), tuple(int(x) for x in sys.argv[2].split(',')))
s0=(tuple([0]*m),(('rem',),('rem',)))
start=(s0,0,0)
par={start:None}; q=deque([start]); goal=None
while q:
    st=q.popleft(); (s,w0,w1)=st
    if w0 and w1: goal=st; break
    for x in (0,1):
        for t in succ(s,x,pis):
            if t[1][x][0]=='retLock': ns=(t,0,0)
            else:
                nw0=w0 or (x==0 and s[1][0][0]=='coll' and t[1][0][0]=='rst')
                nw1=w1 or (x==1 and s[1][1][0]=='coll' and t[1][1][0]=='rst')
                ns=(t,int(nw0),int(nw1))
            if ns not in par: par[ns]=(st,x); q.append(ns)
path=[]; st=goal
while par[st]: path.append((par[st][1],st[0])); st=par[st][0]
for p in reversed(path): print(p)
