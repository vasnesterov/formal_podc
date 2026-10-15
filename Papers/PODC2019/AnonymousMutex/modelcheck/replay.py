# Replay Algorithm 1 (deterministic rule) on a fixed schedule; check periodicity.
import sys
m=5
def run(perms, rule, sched, periods=3):
    mem=[None]*m
    st=[{'pc':'snap','view':None,'x':None,'rem':[]} for _ in range(4)]
    def afterSnap(p,w):
        s=st[p]; s['view']=w
        own=sum(1 for x in range(m) if w[x]==p)
        if not (own>0 or all(v is None for v in w)): s['pc']='snap'; return
        bots=[x for x in range(m) if w[x] is None]
        if bots:
            x = bots[0] if rule=='first' else bots[-1]
            s['pc']='write'; s['x']=x; return
        if own==m: s['pc']='CS'; return
        cnt=len(set(w))
        if own*cnt<m:
            s['rem']=[x for x in range(m) if w[x]==p]; s['pc']='shRead'; return
        s['pc']='snap'
    for _ in range(periods):
        for p in sched:
            s=st[p]; P=perms[p]
            if s['pc']=='snap': afterSnap(p,[mem[P[x]] for x in range(m)])
            elif s['pc']=='write': mem[P[s['x']]]=p; s['pc']='snap'
            elif s['pc']=='shRead':
                x=s['rem'][0]
                if mem[P[x]]==p: s['pc']='shWrite'; s['x']=x
                else:
                    s['rem']=s['rem'][1:]; s['pc']='shRead' if s['rem'] else 'snap'
            elif s['pc']=='shWrite':
                mem[P[s['x']]]=None; s['rem']=s['rem'][1:]; s['pc']='shRead' if s['rem'] else 'snap'
            else: return 'stuck/'+s['pc']
        if any(s['pc']=='CS' for s in st): return 'CS reached'
        print(mem,[s['pc'] for s in st])
    return 'ok'
sched=[0,1,2,3,0,0,0,1,1,1,1,1,0,0,2,2,2,3,1,3,0,2,0,0,1,1,3,3]
perms=[[0,4,1,2,3],[1,2,3,0,4],[2,0,1,3,4],[3,0,1,2,4]]
print('first:',run(perms,'first',sched))
rev=[p[::-1] for p in perms]
print('last, reversed perms:',run(rev,'last',sched))
