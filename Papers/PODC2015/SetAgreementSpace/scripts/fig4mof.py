# Model checker for Figure 4 (repeated m-OF k-set agreement), orig or fixed, T instances per process.
# Processes invoke Propose back-to-back (instances 1..T); input of process p in instance t: inp(p,t).
import sys, itertools
n,k,m,T = map(int, sys.argv[1:5]); fixed = sys.argv[5]=='fix'
mode = sys.argv[6] if len(sys.argv)>6 else 'distinct'
r = n+2*m-k
def inp(p,t): return p if mode=='distinct' else (p+t)%2
# proc: (pc, t, hist, pref, i)  pc: 'S' start-of-propose, 'U' update, 'C' scan, 'D' done (t==T complete)
# outputs recorded in hist (history) - outputs of instance t = hist[t-1]
def first_dup(s):
    for j1 in range(r):
        for j2 in range(j1+1,r):
            if s[j1] is not None and s[j1]==s[j2]: return j1
    return None
def finish(ps,p,hist,t):
    pc = 'D' if t>=T else 'S'
    ps[p]=(pc,t,hist,None,ps[p][4]); 
def step(c,p):
    A,ps=c; A=list(A); ps=list(ps)
    pc,t,hist,pref,i = ps[p]
    if pc=='S':
        t+=1
        if len(hist)>=t: finish(ps,p,hist,t)
        else: ps[p]=('U',t,hist,inp(p,t),i)
    elif pc=='U':
        A[i]=(pref,p,t,hist); ps[p]=('C',t,hist,pref,i)
    elif pc=='C':
        s=A
        hi=[x for x in s if x is not None and x[2]>t]
        if hi:
            his=hi[0][3]; finish(ps,p,his,t)   # adopt history (first found)
        elif len(set(s))<=m and all(x is not None and x[2]>=t for x in s):
            d=first_dup(s); w=s[d][0]; finish(ps,p,hist+(w,),t)
        else:
            # first dup among t-tuples
            d=None
            for j1 in range(r):
                if s[j1] is not None and s[j1][2]==t and any(s[j2]==s[j1] for j2 in range(j1+1,r)): d=j1; break
            cond = all(s[j] is not None and s[j]!=(pref,p,t,hist) for j in range(r) if j!=i) and d is not None
            if cond and fixed and s[d][0]==pref: cond=False
            if cond: ps[p]=('U',t,hist,s[d][0],i)
            else: ps[p]=('U',t,hist,pref,(i+1)%r)
    return (tuple(A),tuple(ps))
init=(tuple([None]*r), tuple(('S',0,(),None,0) for p in range(n)))
seen={init}; stack=[init]
while stack:
    c=stack.pop()
    for p in range(n):
        if c[1][p][0]!='D':
            d=step(c,p)
            if d not in seen: seen.add(d); stack.append(d)
# agreement/validity per instance: outputs = hist entries of processes (all hist are consistent?) collect per instance
bad=None
for c in seen:
    for t in range(1,T+1):
        outs={pr[2][t-1] for pr in c[1] if len(pr[2])>=t and (pr[1]>t or pr[0] in ('S','D') and pr[1]>=t)}
        if len(outs)>k or not outs <= {inp(p,t) for p in range(n)}: bad=(t,c); break
    if bad: break
print("reachable",len(seen),"agreement", "VIOLATION "+str(bad) if bad else "ok")
def succ(c,P): return [(p,step(c,p)) for p in P if c[1][p][0]!='D']
def find_cycle(P):
    idx={};low={};on=set();st=[];cnt=[0]
    for root in seen:
        if root in idx: continue
        work=[(root,iter(succ(root,P)))]; idx[root]=low[root]=cnt[0]; cnt[0]+=1; st.append(root); on.add(root)
        while work:
            v,it=work[-1]; adv=False
            for p,w in it:
                if w not in idx:
                    idx[w]=low[w]=cnt[0]; cnt[0]+=1; st.append(w); on.add(w); work.append((w,iter(succ(w,P)))); adv=True; break
                elif w in on: low[v]=min(low[v],idx[w])
            if adv: continue
            work.pop()
            if work: low[work[-1][0]]=min(low[work[-1][0]],low[v])
            if low[v]==idx[v]:
                comp=set()
                while True:
                    w=st.pop(); on.discard(w); comp.add(w)
                    if w==v: break
                for x in comp:
                    for p,y in succ(x,P):
                        if y in comp: return x
    return None
for sz in range(1,m+1):
    for P in itertools.combinations(range(n),sz):
        x=find_cycle(P)
        if x: print("LIVELOCK P=",P,"at",x); sys.exit()
print("m-OF ok (bounded T)")
