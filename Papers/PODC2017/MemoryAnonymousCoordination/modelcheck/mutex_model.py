import sys, itertools
# Lean-like model. ids 1,2 ; 0 = none
def mk_model(m):
    H=(m+1)//2
    def locs():
        L=[('rem',),('retLock',),('cs',),('retUnlock',)]
        for j in range(m):
            L+= [('scan',j),('scanW',j),('rst',j),('rstW',j),('exit',j),('wait',j,True),('wait',j,False)]
            for o in range(j+1):
                for z in range(j+1-o): L.append(('coll',j,o,z))
        return L
    def succ(st, x, pis):
        """successor states for process index x (0/1) taking a step (tau/ret/inv lock/unlock)."""
        mem, ls = st; l=ls[x]; me=x+1; pi=pis[x]
        def put(nl, nm=mem):
            nls=list(ls); nls[x]=nl; return (nm, tuple(nls))
        def w(r,v): nm=list(mem); nm[r]=v; return tuple(nm)
        k=l[0]
        if k=='rem': return [put(('scan',0))]
        if k=='cs': return [put(('exit',0))]
        if k=='retLock': return [put(('cs',))]
        if k=='retUnlock': return [put(('rem',))]
        j=l[1]; r=pi[j]; nxt=j+1<m
        if k=='scan':
            if mem[r]==0: return [put(('scanW',j))]
            return [put(('scan',j+1) if nxt else ('coll',0,0,0))]
        if k=='scanW': return [put(('scan',j+1) if nxt else ('coll',0,0,0), w(r,me))]
        if k=='coll':
            o,z=l[2],l[3]; v=mem[r]
            o2=o+(v==me); z2=z+(v==0)
            if nxt: return [put(('coll',j+1,o2,z2))]
            if o2==m: return [put(('retLock',))]
            if o2<H: return [put(('rst',0))]
            return [put(('scan',0))]
        if k=='rst':
            if mem[r]==me: return [put(('rstW',j))]
            return [put(('rst',j+1) if nxt else ('wait',0,True))]
        if k=='rstW': return [put(('rst',j+1) if nxt else ('wait',0,True), w(r,0))]
        if k=='wait':
            z=l[2] and mem[r]==0
            if nxt: return [put(('wait',j+1,z))]
            return [put(('scan',0) if z else ('wait',0,True))]
        if k=='exit': return [put(('exit',j+1) if nxt else ('retUnlock',), w(r,0))]
        raise Exception(l)
    return H, locs, succ
