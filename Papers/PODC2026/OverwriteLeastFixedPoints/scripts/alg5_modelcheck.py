# Model-check Algorithm 5 (lock-free Gale-Shapley) under a "stale view" semantics that
# over-approximates interleaving, parallel non-interleaving and distributed executions:
# process i updates G[i] := f_i(V)[i] for any view V with V[i] = G[i], V[k] <= G[k].
import itertools, sys, random

def man_optimal(n, mp, rk):
    # standard GS, men propose. mp[m] list of women; rk[w][m] rank (lower better)
    nxt=[0]*n; partner=[None]*n; free=list(range(n))
    while free:
        m=free.pop()
        w=mp[m][nxt[m]]; nxt[m]+=1
        if partner[w] is None: partner[w]=m
        elif rk[w][m]<rk[w][partner[w]]:
            free.append(partner[w]); partner[w]=m
        else: free.append(m)
    pos=[0]*n
    for w in range(n):
        m=partner[w]; pos[m]=mp[m].index(w)+1
    return tuple(pos)

def f(n, mp, rk, i, V):
    g=V[i]
    if g==0: return 1
    if g>n: return g
    w=mp[i][g-1]
    for j in range(n):
        if j!=i and 1<=V[j]<=n and mp[j][V[j]-1]==w and rk[w][j]<rk[w][i]:
            return g+1
    return g

def check(n, mp, rk, stale=True):
    target=man_optimal(n,mp,rk)
    start=(0,)*n
    seen={start}; stack=[start]; bad=[]
    while stack:
        G=stack.pop()
        fixed=all(f(n,mp,rk,i,G)==G[i] for i in range(n))
        if fixed and G!=target: bad.append(G)
        for i in range(n):
            ranges=[range(G[k]+1) if (k!=i and stale) else [G[k]] for k in range(n)]
            for V in itertools.product(*ranges):
                v=f(n,mp,rk,i,V)
                if v!=G[i]:
                    H=list(G); H[i]=v; H=tuple(H)
                    if H not in seen: seen.add(H); stack.append(H)
    return bad, target

def main():
    n=int(sys.argv[1]); mode=sys.argv[2]
    perms=list(itertools.permutations(range(n)))
    cnt=0; badc=0
    if mode=='all':
        it=((tuple([perms[0]]+list(m)), r) for m in itertools.product(perms,repeat=n-1) for r in itertools.product(perms,repeat=n))
    else:
        random.seed(1)
        it=((tuple(random.choice(perms) for _ in range(n)), tuple(random.choice(perms) for _ in range(n))) for _ in range(int(sys.argv[3])))
    for mp, rkp in it:
        rk=[[0]*n for _ in range(n)]
        for w in range(n):
            for r,m in enumerate(rkp[w]): rk[w][m]=r
        bad,target=check(n,mp,rk)
        cnt+=1
        if bad:
            badc+=1
            if badc<=3: print("BAD", mp, rkp, target, bad[:3])
    print("profiles",cnt,"bad",badc)
main()
