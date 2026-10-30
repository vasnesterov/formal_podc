# Event-driven simulation of Algorithm 4 (BCA_Byz) in normalized asynchronous time:
# every message between correct parties has delay <= 1 (self-delivery 0).
# Scenario n=7, t=2: correct A1,A2 (input 1), B1,B2,B3 (input 0); Byzantine Z1,Z2
# send only <echo,1> to B2 at time 2-eps and nothing else.
import heapq
n, t = 7, 2
eps = 0.01
correct = ['A1','A2','B1','B2','B3']
inp = {'A1':1,'A2':1,'B1':0,'B2':0,'B3':0}
byz = ['Z1','Z2']
parties = correct + byz
st = {p: dict(rcv={}, sent=set(), approved=set(), echo2=None, echo3=None, dec=None, dect=None) for p in correct}
ev = []  # (time, seq, receiver, sender, msg)
seq = [0]
def push(time, r, s, m):
    seq[0] += 1; heapq.heappush(ev, (time, seq[0], r, s, m))
def bcast(time, p, m):
    if m in st[p]['sent']: return
    st[p]['sent'].add(m)
    for q in correct:
        push(time + (0 if q == p else 1.0), q, p, m)
def cnt(p, m): return sum(1 for s, ms in st[p]['rcv'].items() if m in ms)
def cnt_kind(p, k): return sum(1 for s, ms in st[p]['rcv'].items() if any(x[0] == k for x in ms))
def react(time, p):
    S = st[p]
    changed = True
    while changed:
        changed = False
        for v in (0, 1):
            if cnt(p, ('echo', v)) >= t + 1 and ('echo', v) not in S['sent']:
                bcast(time, p, ('echo', v)); changed = True
            if cnt(p, ('echo', v)) >= n - t and v not in S['approved']:
                S['approved'].add(v); changed = True
                if S['echo2'] is None:
                    S['echo2'] = v; bcast(time, p, ('echo2', v))
        if S['echo3'] is None:
            if len(S['approved']) > 1:
                S['echo3'] = 'bot'; bcast(time, p, ('echo3', 'bot')); changed = True
            else:
                for v in (0, 1):
                    if cnt(p, ('echo2', v)) >= n - t and S['echo3'] is None:
                        S['echo3'] = v; bcast(time, p, ('echo3', v)); changed = True
        if S['echo3'] is not None and S['dec'] is None:
            if len(S['approved']) > 1 and cnt_kind(p, 'echo3') >= n - t:
                S['dec'] = 'bot'; S['dect'] = time
            for v in (0, 1):
                if cnt(p, ('echo3', v)) >= n - t and S['dec'] is None:
                    S['dec'] = v; S['dect'] = time
for p in correct:
    bcast(0.0, p, ('echo', inp[p]))
for z in byz:
    push(2 - eps, 'B2', z, ('echo', 1))
for p in correct: react(0.0, p)
while ev:
    time, _, r, s, m = heapq.heappop(ev)
    st[r]['rcv'].setdefault(s, set()).add(m)
    react(time, r)
for p in correct:
    S = st[p]
    print(p, 'echo2', S['echo2'], 'echo3', S['echo3'], 'decision', S['dec'], 'at time', S['dect'],
          'broadcasts', len(S['sent']))
