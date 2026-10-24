import sys, random, math
sys.path.insert(0,'.')
from g2s_fix import simulate
rng=random.Random(5)
for n in [16,64,128,256]:
    E=[(i,i+1) for i in range(n-1)]
    r1=simulate(n,E,list(range(n)),maxph=1000)
    ids=list(range(n)); rng.shuffle(ids)
    r2=simulate(n,E,ids,maxph=1000)
    Et=[(i,rng.randrange(i)) for i in range(1,n)]
    r3=simulate(n,Et,ids,maxph=1000)
    print(n, r1[:2], r2[:2], r3[:2], round(math.log2(n),1))
