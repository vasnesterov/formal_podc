def run(N, permanent):
    P=[max(i-1,0) for i in range(N)]; stopped=set(); hist=[list(P)]
    for r in range(12):
        ch={}
        for v in range(1,N): ch[P[v]]=ch.get(P[v],0)+1
        new=list(P)
        for u in range(1,N):
            if u in stopped or P[u]==0: continue
            g=P[P[u]]
            if ch.get(g,0)>=2:
                if permanent: stopped.add(u)
                continue
            new[u]=g
            if g==0 and permanent: stopped.add(u)
        P=new; hist.append(list(P))
    return hist
print(all(run(N,True)==run(N,False) for N in range(1,301)))
