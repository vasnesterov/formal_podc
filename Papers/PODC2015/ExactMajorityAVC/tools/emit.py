# Prints the Lean `Tree` term for tree2_<case>.pkl produced by gen2.py.
# Usage: python3 emit.py A|B
import sys,pickle
N=['S0','S1','X','Y']
def pairs(pi): return '[' + ', '.join('(%s, %s)'%(N[p],N[q]) for p,q in pi) + ']'
def cnt(c): return '⟨%d, %d, %d, %d⟩'%c
def cert(c):
    if c[0]=='b2':
        (a,b),(a2,b2),p1,p2=c[1],c[2],c[3],c[4]
        return '.cert (.b2 %d %d %d %d %s %s)'%(a,b,a2,b2,pairs(p1),pairs(p2))
    kind,i,(a,b),pi,F=c
    if i==0: A,B,ib=a,b,'false'
    else: A,B,ib=b,a,'true'
    return '.cert (.%s %s %d %d %s [%s])'%(kind,ib,A,B,pairs(pi),', '.join(cnt(f) for f in F))
def emit(t,ind):
    sp='  '*ind
    if t[0]=='leaf': return sp+'('+cert(t[1])+')'
    if t[0]=='inv': return sp+'.inv'
    k=t[1]
    s=sp+'(.split %s %s\n'%(N[k[0]],N[k[1]])
    s+='\n'.join(emit(ch,ind+1) for o,ch in t[2])
    return s+')'
case=sys.argv[1]
t=pickle.load(open('tree2_%s.pkl'%case,'rb'))
print(emit(t,1))
