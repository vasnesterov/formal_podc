from itertools import product
def W(k,i,j): return k if i==j else (j-i)%k
def exch(k,e,f):
    (i1,j1),(i2,j2)=e,f
    if min(W(k,i1,j2),W(k,i2,j1)) < min(W(k,i1,j1),W(k,i2,j2)):
        return (i1,j2),(i2,j1),True
    return e,f,False
def circles(k):
    def d(p,q):
        e,f,_=exch(k,(p[0],p[1]),(q[0],q[1]))
        oa,ob=p[2],q[2]
        da,db=e[0]==e[1],f[0]==f[1]
        if da and not db: oa=ob=e[0]
        elif db and not da: oa=ob=f[0]
        return (e[0],e[1],oa),(f[0],f[1],ob)
    return d
def tiereport(k, order="23", selfreset=False):
    def d(p,q):
        e,f,ex=exch(k,(p[0],p[1]),(q[0],q[1]))
        oa,ob=p[2],q[2]
        da,db=e[0]==e[1],f[0]==f[1]
        if da and not db: oa=ob=e[0]
        elif db and not da: oa=ob=f[0]
        ta,tb=p[3],q[3]
        # (1) tie detection
        if p[0]==p[1] and not da: ta='S'
        if q[0]==q[1] and not db: tb='S'
        sa,sb=ta,tb
        def r2(ta,tb):
            if sa=='S' and not db: tb='T'
            if sb=='S' and not da: ta='T'
            return ta,tb
        def r3(ta,tb):
            if da: tb='N'
            if db: ta='N'
            if selfreset:
                if da: ta='N'
                if db: tb='N'
            return ta,tb
        for r in order:
            ta,tb = r2(ta,tb) if r=='2' else r3(ta,tb)
        return (e[0],e[1],oa,ta),(f[0],f[1],ob,tb)
    return d
def outTR(s): return s[2] if s[3]=='N' else 'tie'
def tiebreak(k):
    def d(p,q):
        e,f,ex=exch(k,(p[0],p[1]),(q[0],q[1]))
        oa,ob=p[2],q[2]
        da,db=e[0]==e[1],f[0]==f[1]
        if da and not db: oa=ob=e[0]
        elif db and not da: oa=ob=f[0]
        ta,tb=p[3],q[3]
        if ex and ta==0 and tb==0: ta=1
        if ta==1 and tb==1: ta=0
        if ta+tb==1:
            ka=(W(k,e[0],e[1]),e[0]); kb=(W(k,f[0],f[1]),f[0])
            if ka>kb: ta,tb=1,0
            elif kb>ka: ta,tb=0,1
        if ta==1: oa=ob=e[0]
        if tb==1: oa=ob=f[0]
        return (e[0],e[1],oa,ta),(f[0],f[1],ob,tb)
    return d
