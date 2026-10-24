import sys, random, math
sys.path.insert(0,'.')
from g2s_fix import simulate
rng=random.Random(3)
from collections import Counter
worst={}
cnt=Counter()
for trial in range(3000):
    n=rng.randint(2,40)
    kind=rng.choice(['line','tree','rand'])
    if kind=='line': E=[(i,i+1) for i in range(n-1)]
    elif kind=='tree': E=[(i,rng.randrange(i)) for i in range(1,n)]
    else:
        E=[(i,rng.randrange(i)) for i in range(1,n)]+[(rng.randrange(n),rng.randrange(n)) for _ in range(n)]
        E=[(a,b) for a,b in E if a!=b]
    ids=list(range(n)); rng.shuffle(ids)
    if rng.random()<0.3: ids=list(range(n))
    r=simulate(n,E,ids,maxph=500)
    cnt[r[0]]+=1
    if r[0]=='ok': worst[n]=max(worst.get(n,0),r[1])
    elif cnt[r[0]]<3: print(r, n, kind)
print(cnt)
for n in sorted(worst):
    if n%5==0: print(n, worst[n], round(worst[n]/math.log2(n),2))
