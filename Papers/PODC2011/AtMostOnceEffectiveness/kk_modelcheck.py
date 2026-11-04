import sys
# Exhaustive model checker for KK_beta (PODC 2011, Kentros-Kiayias), small parameters only.
# usage: python3 -I kk_modelcheck.py n m beta f maxstates [maxDo]
# prints the minimum number of performed jobs over terminal configurations with <= f crashes.
from collections import deque
# KK_beta model checker. processes 1..m, jobs 1..n.
# status codes
CN,SN,GT,GD,CK,DO,DN,END,STOP=range(9)
def run(n,m,beta,f,maxstates=3_000_000,target=None):
    J=frozenset(range(1,n+1))
    def rank(S,i):
        s=sorted(S)
        return s[i-1] if 1<=i<=len(s) else None
    # proc state: (status, DONE(frozenset), TRY(frozenset), POS(tuple m), NEXT, Q)
    init_p=(CN,frozenset(),frozenset(),tuple([1]*m),0,1)
    # shared: next tuple m, done: tuple of tuples (line contents as tuple of written values)
    init=(tuple([init_p]*m),tuple([0]*m),tuple([()]*m),0, frozenset())  # crashes count, jobs done set
    seen={init}
    stack=[init]
    best=None; bestw=None
    terminal=0
    viol=False
    while stack:
        st=stack.pop()
        procs,nxt,done,cr,jd=st
        succ=[]
        anyen=False
        for i in range(m):
            p=i+1
            status,D,T,POS,NX,Q=procs[i]
            if status in (END,STOP): continue
            anyen=True
            F=J-D
            P=list(procs); nn=list(nxt); dd=list(done); njd=jd
            if status==CN:
                if len(F-T)>=beta:
                    if len(F)>=2*m-1:
                        k=((p-1)*(len(F)-(m-1)))//m+1
                    else: k=p
                    r=rank(F-T,k)
                    if r is None: print("rank undefined",st); return
                    P[i]=(SN,D,frozenset(),POS,r,1)
                else:
                    P[i]=(END,D,T,POS,NX,Q)
            elif status==SN:
                nn[i]=NX; P[i]=(GT,D,T,POS,NX,Q)
            elif status==GT:
                T2=T
                if Q!=p and nxt[Q-1]>0: T2=T|{nxt[Q-1]}
                if Q+1<=m: P[i]=(GT,D,T2,POS,NX,Q+1)
                else: P[i]=(GD,D,T2,POS,NX,1)
                # combine
            elif status==GD:
                D2=D;POS2=POS;Q2=Q
                if Q!=p:
                    line=done[Q-1]; ps=POS[Q-1]
                    v=line[ps-1] if ps-1<len(line) else 0
                    if ps<=n and v>0:
                        D2=D|{v}; POS2=POS[:Q-1]+(ps+1,)+POS[Q:]
                    else: Q2=Q+1
                else: Q2=Q+1
                if Q2>m: P[i]=(CK,D2,T,POS2,NX,1)
                else: P[i]=(GD,D2,T,POS2,NX,Q2)
            elif status==CK:
                if NX not in T and NX not in D: P[i]=(DO,D,T,POS,NX,Q)
                else: P[i]=(CN,D,T,POS,NX,Q)
            elif status==DO:
                if NX in jd: viol=True
                njd=jd|{NX}
                P[i]=(DN,D,T,POS,NX,Q)
            elif status==DN:
                line=done[i]; assert len(line)==POS[i]-1
                dd[i]=line+(NX,)
                P[i]=(CN,D|{NX},T,POS[:i]+(POS[i]+1,)+POS[i+1:],NX,Q)
            succ.append((tuple(P),tuple(nn),tuple(dd),cr,njd))
            if cr<f:
                P=list(procs); P[i]=(STOP,)+procs[i][1:]
                succ.append((tuple(P),nxt,done,cr+1,jd))
        if not anyen:
            terminal+=1
            d=len(jd)
            if best is None or d<best: best=d; bestw=st
        for s in succ:
            if target is not None and len(s[4])>target: continue
            if s not in seen:
                seen.add(s); stack.append(s)
                if len(seen)>maxstates: print("too many states"); return
    print(f"n={n} m={m} beta={beta} f={f}: states={len(seen)} terminal={terminal} minDo={best} paper={n-(beta+m-2)} viol={viol}")
    return best
if __name__=="__main__":
    a=list(map(int,sys.argv[1:]))
    n,m,beta,f,ms=a[:5]
    t=a[5] if len(a)>5 else None
    run(n,m,beta,f,ms,t)
