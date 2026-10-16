# Bounded exhaustive schedule exploration for Algorithms 2 and 3 (small rings).
# Usage: (ulimit -v 4000000; timeout 600 python3 -I mc.py 3 4)   # max ring size, max ID
import sys, itertools
# ports: 0 = port0, 1 = port1. Oriented ring: port1 -> next (arrives at port0 of next), port0 -> prev (arrives at port1 of prev)
def peer(n, flips, v, i):
    j = i ^ flips[v]          # oriented port
    if j == 1: w, k = (v+1) % n, 0
    else: w, k = (v-1) % n, 1
    return (w, k ^ flips[w])

# Algorithm 2 (oriented): state = (id, rcw, rccw, started, leader, waiting, done)
# CW pulses: received port0, sent port1. CCW: received port1, sent port0.
def a2_init(i):
    return (i,0,0,False,False,False,False), {1:1}
def a2_ready(s, p):
    i,rcw,rccw,st,ld,wt,dn = s
    if dn: return False
    if p == 0: return not wt
    return rcw >= i
def a2_recv(s, p):
    i,rcw,rccw,st,ld,wt,dn = s
    out = {0:0,1:0}
    if p == 0:
        rcw += 1
        if rcw == i: ld = True
        else: ld = False; out[1] += 1
        if rcw >= i and not st: out[0] += 1; st = True
        if rcw == i == rccw: out[0] += 1; wt = True
        if rccw > rcw: dn = True
    else:
        if wt:
            rccw += 1; wt = False
            if rccw > rcw: dn = True
        else:
            rccw += 1
            if rccw != i: out[0] += 1
            if rcw == i == rccw: out[0] += 1; wt = True
            if rccw > rcw: dn = True
    return (i,rcw,rccw,st,ld,wt,dn), out

# Algorithm 3 with virtual ids f(ID, i)
def mk_a3(f):
    def init(i): return (i,0,0), {0:1,1:1}
    def ready(s,p): return True
    def recv(s,p):
        i,r0,r1 = s
        out = {0:0,1:0}
        if p == 0:
            r0 += 1
            if r0 != f(i,1): out[1] += 1
        else:
            r1 += 1
            if r1 != f(i,0): out[0] += 1
        return (i,r0,r1), out
    return init, ready, recv

def explore(n, ids, flips, alg, check_final, bound):
    init, ready, recv = alg
    st = []; sent = {}
    for v in range(n):
        s, o = init(ids[v]); st.append(s)
        for p in (0,1): sent[(v,p)] = o.get(p,0)
    recvd = {(v,p):0 for v in range(n) for p in (0,1)}
    def key(st, sent, recvd): return (tuple(st), tuple(sorted(sent.items())), tuple(sorted(recvd.items())))
    start = (tuple(st), dict(sent), dict(recvd))
    seen = set(); stack=[start]; finals=0; maxsent=0
    while stack:
        st, sent, recvd = stack.pop()
        k = key(st,sent,recvd)
        if k in seen: continue
        seen.add(k)
        tot = sum(sent.values()); maxsent=max(maxsent,tot)
        assert tot <= bound, ("bound", tot, bound)
        en = False
        for v in range(n):
            for p in (0,1):
                src = peer(n, flips, v, p)
                if recvd[(v,p)] < sent[src] and ready(st[v], p):
                    en = True
                    s2, o = recv(st[v], p)
                    st2 = list(st); st2[v] = s2
                    sent2 = dict(sent); recvd2 = dict(recvd)
                    recvd2[(v,p)] += 1
                    for q in (0,1): sent2[(v,q)] += o.get(q,0)
                    stack.append((tuple(st2), sent2, recvd2))
        if not en:
            finals += 1
            check_final(n, ids, flips, st, sent, recvd)
    return len(seen), finals, maxsent

def chk2(n, ids, flips, st, sent, recvd):
    M = max(ids)
    quies = all(recvd[(v,p)] == sent[peer(n,flips,v,p)] for v in range(n) for p in (0,1))
    assert quies, "not quiescent"
    assert all(s[6] for s in st), "not all done"
    for v in range(n): assert st[v][4] == (ids[v]==M), ("leader", st)
    assert sum(sent.values()) == n*(2*M+1), ("exact", sum(sent.values()))

def chk3(f):
    def chk(n, ids, flips, st, sent, recvd):
        M = max(ids)
        quies = all(recvd[(v,p)] == sent[peer(n,flips,v,p)] for v in range(n) for p in (0,1))
        assert quies
        leaders = []
        cwport = []
        for v in range(n):
            i,r0,r1 = st[v]
            assert max(r0,r1) >= f(i,1), ("cond", st)
            if r0 == f(i,1) and r1 < f(i,1): leaders.append(v)
            cwport.append(1 if r0 > r1 else 0)
        assert leaders == [ids.index(M)], (leaders, ids, flips, st)
        # orientation: following cw ports passes all edges: cw port of v leads to w, and w's cw port leads away from v
        for v in range(n):
            w, k = peer(n, flips, v, cwport[v])
            # k is w's port toward v; cw port of w must be the other one
            assert cwport[w] != k or n == 1 and False, ("orient", ids, flips, st)
        return
    return chk

if __name__ == "__main__":
    maxn = int(sys.argv[1]); maxid = int(sys.argv[2])
    tot=0
    for n in range(1, maxn+1):
        for ids in itertools.permutations(range(1, maxid+1), n):
            if ids[0] != max(ids) and n>1 and False: continue
            r = explore(n, list(ids), [0]*n, (a2_init,a2_ready,a2_recv), chk2, n*(2*max(ids)+1))
            tot += r[0]
    print("alg2 ok, states", tot)
    for name, f, bnd in [("thm2", lambda i,k: i+k, lambda M: 2*M+1), ("prop14", lambda i,k: 2*i-1+k, lambda M: 4*M-1)]:
        tot=0
        for n in range(1, maxn+1):
            for ids in itertools.permutations(range(1, maxid+1), n):
                for flips in itertools.product((0,1), repeat=n):
                    r = explore(n, list(ids), list(flips), mk_a3(f), chk3(f), n*bnd(max(ids)))
                    tot += r[0]
        print(name, "ok, states", tot)
