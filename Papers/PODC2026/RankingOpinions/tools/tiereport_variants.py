import sys; sys.path.insert(0,'.')
from mc import *; from protos import W, exch
from itertools import combinations_with_replacement as cwr
def tiereport(k, onlyN, pre, selfreset, order):
    def d(p,q):
        e,f,ex=exch(k,(p[0],p[1]),(q[0],q[1]))
        oa,ob=p[2],q[2]
        da,db=e[0]==e[1],f[0]==f[1]
        if da and not db: oa=ob=e[0]
        elif db and not da: oa=ob=f[0]
        ta,tb=p[3],q[3]
        if p[0]==p[1] and not da: ta='S'
        if q[0]==q[1] and not db: tb='S'
        sa,sb=(p[3],q[3]) if pre else (ta,tb)
        def r2(ta,tb):
            if sa=='S' and not db and (not onlyN or tb=='N'): tb='T'
            if sb=='S' and not da and (not onlyN or ta=='N'): ta='T'
            return ta,tb
        def r3(ta,tb):
            if da: tb='N'
            if db: ta='N'
            if selfreset:
                if da: ta='N'
                if db: tb='N'
            return ta,tb
        for r in order: ta,tb = r2(ta,tb) if r=='2' else r3(ta,tb)
        return (e[0],e[1],oa,ta),(f[0],f[1],ob,tb)
    return d
def outTR(s): return s[2] if s[3]=='N' else 'tie'
if __name__=='__main__':
  res={}
  for onlyN in [False,True]:
    for pre in [False,True]:
      for selfreset in [False,True]:
        for order in ["23","32"]:
          key=(onlyN,pre,selfreset,order); res[key]=[]
          for k in [2,3]:
            for n in range(1,6 if k==2 else 5):
              for c in cwr(range(k),n):
                  x=[c.count(i) for i in range(k)]; m=max(x); w=[i for i in range(k) if x[i]==m]
                  target = w[0] if len(w)==1 else 'tie'
                  bad=lambda C: any(outTR(s)!=target for s in C)
                  ok,b,N,confs,edges=check(tuple((i,i,i,'N') for i in c),tiereport(k,onlyN,pre,selfreset,order),n,bad)
                  if not ok: res[key].append((k,c,'tie' if len(w)>1 else 'notie'))
          print(key, len(res[key]), res[key][:4])
  