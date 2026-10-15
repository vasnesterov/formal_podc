import sys, itertools, subprocess, os, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from rank import make_delta, rank_of, fmt
def run(x, variant, limit=60000000):
    k=len(x); d=make_delta(k,variant); r=rank_of(x)
    states=[(a,b,c,e,t) for a in range(k) for b in range(k) for c in range(k) for e in range(k) for t in (0,1)]
    sid={s:i for i,s in enumerate(states)}; S=len(states)
    lines=[f"{k} {S} {sum(x)}"]
    for a in states:
        for b in states:
            p,q=d(a,b); lines.append(f"{sid[p]} {sid[q]}")
    lines.append(' '.join(str(sid[(i,i,i,i,1)]) for i in range(k) for _ in range(x[i])))
    lines.append(' '.join('1' if s[1]!=r[s[0]] else '0' for s in states))
    fn=os.path.join(tempfile.gettempdir(), f"rk_tab_{os.getpid()}.txt")
    open(fn,'w').write('\n'.join(lines))
    out=subprocess.run([os.path.dirname(os.path.abspath(__file__))+'/mc',fn,str(limit)],capture_output=True,text=True).stdout
    res=[]
    for l in out.splitlines():
        if l.startswith('BADSCC'):
            parts=l.split(':'); l=parts[0]+': '+' '.join(fmt(states[int(z)]) for z in parts[1].split())
        res.append(l)
    return '\n   '.join(res)
if __name__=='__main__':
    variants=eval(sys.argv[1]); cfgs=eval(sys.argv[2])
    for v in variants:
        print(v,flush=True)
        for base in cfgs:
            for x in sorted(set(itertools.permutations(base))):
                print(' ',x,run(list(x),v),flush=True)
