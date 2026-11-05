import sys, random
K=int(sys.argv[1]); MAXCR=int(sys.argv[2]); RUNS=int(sys.argv[3]); SEED=int(sys.argv[4])
sys.argv=['mc.py',str(K),str(MAXCR)]
src=open('mc.py').read().replace("\nmain()\n","\n")
g={}
exec(compile(src,'mc','exec'),g)
random.seed(SEED)
def run():
    st=(4,tuple([0]*K),(),tuple([g['EMPTYP']]*K),(),0)
    pcr=random.choice([0.01,0.03,0.1])
    tr=[]
    nsteps=random.randint(50,400)
    for t in range(nsteps):
        q=random.randrange(K)
        if st[5]<MAXCR and not st[3][q][1] and random.random()<pcr:
            st=g['crash'](st,q); tr.append(('crash',q))
        else:
            succ=g['steps'](st,q)
            st=random.choice(succ); tr.append(('step',q))
        g['check'](st)
    # liveness phase: no crashes, round robin; all try processes should reach CS
    waiting={q for q in range(K) if not st[3][q][1] and st[3][q][0] not in (27,28,29)}
    if not waiting: return None
    for t in range(200*K*K):
        q=t%K
        if st[3][q][1]: continue
        st=random.choice(g['steps'](st,q)); g['check'](st)
        if st[3][q][0]==27: waiting.discard(q)
        if not waiting: return None
    return (st,tr,waiting)
for r in range(RUNS):
    try:
        res=run()
    except g['Bug'] as b:
        print("BUG",b,"run",r); break
    if res:
        print("STUCK",res[2]); print(g['show'](res[0])); break
else:
    print("ok",RUNS)
