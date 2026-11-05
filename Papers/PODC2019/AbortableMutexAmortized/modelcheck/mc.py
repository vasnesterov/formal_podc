import sys
from collections import deque
n = int(sys.argv[1])
SENT = n
NIL, TOK = 0, 1
def A(j): return 2 + j
def G(p): return 2 + n + 1 + p
def isA(x): return 2 <= x < 2 + n + 1
def isG(x): return x >= 2 + n + 1
def aof(x): return x - 2
def gof(x): return x - (2 + n + 1)

# state: (pc, mynode, pred, v, node, go, tail)
init = (tuple([1]*n), tuple(range(n)), tuple(range(n)), tuple([NIL]*n),
        tuple([NIL]*n + [TOK]), tuple([False]*n), SENT)

class Err(Exception): pass

def setv(t, i, x):
    l = list(t); l[i] = x; return tuple(l)

def line9(s, p):
    pc, my, pr, v, nd, go, tl = s
    val = nd[pr[p]]
    nd = setv(nd, pr[p], NIL)
    v = setv(v, p, val)
    if val == TOK:
        pc = setv(pc, p, 7)
    else:
        if val not in (NIL, G(p)):
            if not isA(val): raise Err(("l9 pred<-go", s, p))
            pr = setv(pr, p, aof(val))
        pc = setv(pc, p, 10)
    return (pc, my, pr, v, nd, go, tl)

def step(s, p, abort=False):
    pc, my, pr, v, nd, go, tl = s
    l = pc[p]
    if abort:
        assert l in (4,5,6)
        return line9(s, p)
    if l == 1:
        old = nd[my[p]]
        nd = setv(nd, my[p], NIL)
        pc = setv(pc, p, 3 if old == A(pr[p]) else 2)
    elif l == 2:
        pr = setv(pr, p, tl); tl = my[p]; pc = setv(pc, p, 3)
    elif l in (3, 6):
        val = nd[pr[p]]
        nd = setv(nd, pr[p], G(p))
        v = setv(v, p, val)
        if val == TOK: pc = setv(pc, p, 7)
        elif val not in (NIL, G(p)):
            if not isA(val): raise Err(("l36 pred<-go", s, p))
            pr = setv(pr, p, aof(val)); pc = setv(pc, p, 6)
        else: pc = setv(pc, p, 4)
    elif l == 4:
        if go[p]: pc = setv(pc, p, 5)
    elif l == 5:
        go = setv(go, p, False); pc = setv(pc, p, 6)
    elif l == 7:
        val = nd[my[p]]
        nd = setv(nd, my[p], TOK)
        v = setv(v, p, val)
        my = setv(my, p, pr[p])
        pc = setv(pc, p, 8 if val != NIL else 1)
    elif l in (8, 11):
        if not isG(v[p]): raise Err(("l8/11 v not go", s, p))
        go = setv(go, gof(v[p]), True); pc = setv(pc, p, 1)
    elif l == 9:
        return line9(s, p)
    elif l == 10:
        val = nd[my[p]]
        nd = setv(nd, my[p], A(pr[p]))
        v = setv(v, p, val)
        pc = setv(pc, p, 11 if val != NIL else 1)
    return (pc, my, pr, v, nd, go, tl)

def succs(s):
    pc = s[0]
    for p in range(n):
        yield (p, False), step(s, p)
        if pc[p] in (4,5,6):
            yield (p, True), step(s, p, True)

def computeQ(s):
    pc, my, pr, v, nd, go, tl = s
    owner = {my[p]: p for p in range(n)}
    Q = []
    x = tl
    seen = set()
    while x in owner:
        q = owner[x]
        if q in seen: return None
        seen.add(q); Q.append(q); x = pr[q]
    Q.reverse()
    return Q, x

def checkI(s, extra=False):
    pc, my, pr, v, nd, go, tl = s
    errs = []
    if len(set(my)) != n: return ["mynode not injective"]
    r = computeQ(s)
    if r is None: return ["cycle"]
    Q, a0 = r
    k = len(Q)
    Aa = [a0] + [my[q] for q in Q]
    # I4: a0 not a mynode
    if a0 in my: errs.append("I4")
    # I3 holds by construction; I1 holds by construction
    for p in range(n):
        if pc[p] in (2, 8) and p in Q: errs.append("I6a")
        if pc[p] == 2 and nd[my[p]] != NIL: errs.append("I6b")
        if pc[p] == 8 and nd[my[p]] not in (NIL, G(p)): errs.append("I6c")
    for i in range(k):
        q = Q[i]
        if i == k-1:
            if pc[q] in (3,4,5,6,7,9,10) and nd[my[q]] != NIL: errs.append("I7last")
            if pc[q] in (1,11) and nd[my[q]] != A(pr[q]): errs.append("I7lastab")
        else:
            if pc[q] in (3,4,5,6,7,9,10) and nd[my[q]] not in (NIL, G(Q[i+1])): errs.append("I7mid")
            if pc[q] in (1,11) and nd[my[q]] != A(pr[q]): errs.append("I7midab")
    for p in range(n):
        if p not in Q and not (pc[p] in (1,2,8,11) and nd[my[p]] != A(pr[p])): errs.append("I8")
    if k == 0 or pc[Q[0]] != 7:
        if nd[a0] != TOK: errs.append("I9a")
    else:
        if nd[a0] not in (NIL, G(Q[0])): errs.append("I9b")
    for p in range(n):
        if pc[p] == 7 and (k == 0 or p != Q[0]): errs.append("I10")
    if k >= 1 and pc[Q[0]] == 4 and not go[Q[0]]:
        if not any(pc[p] == 8 and v[p] == G(Q[0]) for p in range(n)): errs.append("I11a")
    for i in range(1, k):
        qi, qm = Q[i], Q[i-1]
        if pc[qi] == 4 and not go[qi]:
            if not (nd[Aa[i]] == G(qi) or (nd[Aa[i]] == A(pr[qm]) and pc[qm] == 11 and v[qm] == G(qi))):
                errs.append("I11b")
    for p in range(n):
        if pc[p] in (8, 11) and not isG(v[p]): errs.append("I11c")
        if pc[p] == 5 and not go[p]: errs.append("I12")
    if extra:
        for i in range(k):
            q = Q[i]
            if pc[q] in (1, 10, 11) and nd[Aa[i]] == G(q): errs.append("X1")
    return errs

def bfs():
    seen = {init}
    dq = deque([init])
    cnt = 0
    while dq:
        s = dq.popleft()
        cnt += 1
        e = checkI(s, extra=True)
        if e: print("VIOL", e, s); return
        if sum(1 for p in range(n) if s[0][p] == 7) > 1: print("MUTEX", s); return
        for lab, t in succs(s):
            if t not in seen:
                seen.add(t); dq.append(t)
    print("reachable", cnt)
    return seen

if __name__ == "__main__":
    R = bfs()
    import pickle
    if R is not None and len(sys.argv) > 2:
        pickle.dump(R, open(sys.argv[2], "wb"))
