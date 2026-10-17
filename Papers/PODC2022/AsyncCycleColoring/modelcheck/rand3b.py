import sys; import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from alg3 import *
import random
def chk(n,s):
    bad=[]
    for p in range(n):
        for q in ((p-1)%n,(p+1)%n):
            Xp=s[p][0][0]; Xq=s[q][0][0]; rq=s[q][1]; rp=s[p][1]
            if Xp==Xq: bad.append('loc')
            if rq is not None and Xp==rq[0]: bad.append('loc-reg')
            if rp is not None and rq is not None and rp[0]==rq[0]: bad.append('reg')
    return bad
if __name__=="__main__":
    random.seed(int(sys.argv[1])); runs=int(sys.argv[2])
    cnt={}
    for it in range(runs):
        n=random.randint(3,8); hi=random.choice([16,64,1024,10**6])
        while True:
            ids=[random.randrange(hi) for _ in range(n)]
            if all(ids[i]!=ids[(i+1)%n] for i in range(n)): break
        s=tuple(((ids[i],0,0,0),None,None) for i in range(n))
        pr=[random.random() for _ in range(n)]
        for t in range(60):
            working=[i for i in range(n) if s[i][2] is None]
            if not working: break
            S=tuple(i for i in working if random.random()<pr[i])
            if not S: continue
            regs=[s[i][1] for i in range(n)]
            for i in S: regs[i]=s[i][0]
            new=list(s)
            for i in S:
                kind,v=step3(s[i][0],[regs[(i-1)%n],regs[(i+1)%n]])
                new[i]=(s[i][0],regs[i],v) if kind=='ret' else (v,regs[i],None)
            s=tuple(new)
            b=chk(n,s)
            if b:
                for x in set(b):
                    cnt[x]=cnt.get(x,0)+1
                    if cnt[x]<3: print(x,ids,t,s)
                break
    print(cnt)
