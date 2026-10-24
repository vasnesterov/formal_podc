import math
def k(i):
    if i+1<3: return 0
    return int(math.floor(math.log2((i+1)//3)))+1
def Q(r,i): return i-2**min(r,k(i)) if i>0 else 0
def step(P,N):
    ch={}
    for v in range(1,N): ch[P[v]]=ch.get(P[v],0)+1
    new=list(P)
    for u in range(1,N):
        if P[u]!=0 and ch.get(P[P[u]],0)<2: new[u]=P[P[u]]
    return new
ok=True
for N in range(1,300):
    P=[max(i-1,0) for i in range(N)]
    for r in range(12):
        if P!=[Q(r,i) for i in range(N)]: ok=False; print("mismatch",N,r); break
        P=step(P,N)
print(ok)
