#!/usr/bin/env python3
"""Explicit-state model checker for the k-ported RME algorithm of Jayanti-Jayanti-Joshi (PODC'19),
Figures 3-4.  One process per port.  Signals are atomic bits.  RLock = FIFO recoverable lock.

Node ids: 0 NIL, 1 Crash, 2 InCS, 3 Exit, 4 SpecialNode, >=5 dynamically allocated QNodes.
"""
import sys
from collections import deque

NIL, CRASH, INCS, EXIT, SPECIAL = 0, 1, 2, 3, 4
SENT = (CRASH, INCS, EXIT)

K = int(sys.argv[1]) if len(sys.argv) > 1 else 2
MAXCR = int(sys.argv[2]) if len(sys.argv) > 2 else 1
LIVE = (len(sys.argv) > 3 and sys.argv[3] == 'live')
MAXS = int(sys.argv[4]) if len(sys.argv) > 4 else 10**9

# process local state: tuple
# (pc, idle, mynode, mypred, tl, V, E, i, cur, paths, todo, sig, tailpath, headpath)
F = dict(pc=0, idle=1, mynode=2, mypred=3, tl=4, V=5, E=6, i=7, cur=8, paths=9, todo=10, sig=11,
         tailpath=12, headpath=13)
EMPTYP = (10, 1, 0, 0, 0, frozenset(), frozenset(), 0, 0, (), frozenset(), -1, -1, -1)
CRASHEDP = (10, 0, 0, 0, 0, frozenset(), frozenset(), 0, 0, (), frozenset(), -1, -1, -1)


def setp(p, **kw):
    l = list(p)
    for k, v in kw.items():
        l[F[k]] = v
    return tuple(l)


# global state: (tail, nodearr, nodes, procs, rq, crashes)
# nodes: tuple of (id, pred, nonnil, cs) sorted by id (only ids >= 5)

def getnode(nodes, x):
    if x == SPECIAL:
        return (SPECIAL, EXIT, 1, 1)
    if x in SENT:
        return (x, x, 0, 0)
    for n in nodes:
        if n[0] == x:
            return n
    raise KeyError(x)


def setnode(nodes, x, pred=None, nonnil=None, cs=None):
    out = []
    for n in nodes:
        if n[0] == x:
            n = (x, n[1] if pred is None else pred, n[2] if nonnil is None else nonnil,
                 n[3] if cs is None else cs)
        out.append(n)
    return tuple(out)


def pred_of(nodes, x):
    return getnode(nodes, x)[1]


class Bug(Exception):
    pass


def compute_paths(V, E):
    """maximal paths in (V,E); edges (u,v) = u -> v.  Return list of tuples (start..end)."""
    out = {}
    indeg = {v: 0 for v in V}
    for (u, v) in E:
        if u in out:
            raise Bug("outdeg>1 at %d" % u)
        out[u] = v
        indeg[v] += 1
    paths = []
    for s in sorted(V):
        if indeg[s] == 0:
            path = [s]
            x = s
            seen = {s}
            while x in out:
                x = out[x]
                if x in seen:
                    raise Bug("cycle")
                seen.add(x)
                path.append(x)
            paths.append(tuple(path))
    # check all vertices covered (cycles not reachable from indeg-0 vertices)
    cov = set()
    for pth in paths:
        cov |= set(pth)
    if cov != set(V):
        raise Bug("cycle (uncovered vertices)")
    return tuple(paths)


def deadclear(p):
    pc = p[0]
    if pc == 10:
        return setp(CRASHEDP, idle=p[1])
    if pc in (12, 13, 17, 18, 181, 19, 221, 222, 23, 24, 30, 50, 25, 26, 27, 28, 29, 14, 15):
        keepmp = pc in (14, 15, 23, 24, 30, 50, 25)
        return setp(CRASHEDP, pc=pc, idle=p[1], mynode=p[2], mypred=p[3] if keepmp else 0)
    return p


def canon(st):
    tail, arr, nodes, procs, rq, cr = st
    procs = tuple(deadclear(p) for p in procs)
    ren = {}
    nxt = [5]
    ndict = {n[0]: n for n in nodes}

    def r(x):
        if x is None or x < 5:
            return x
        if x not in ren:
            ren[x] = nxt[0]
            nxt[0] += 1
        return ren[x]

    r(tail)
    for a in arr:
        r(a)
    for p in procs:
        r(p[F['mynode']]); r(p[F['mypred']]); r(p[F['tl']]); r(p[F['cur']])
        for v in sorted(p[F['V']]):
            r(v)
        for (u, v) in sorted(p[F['E']]):
            r(u); r(v)
        for pth in p[F['paths']]:
            for v in pth:
                r(v)
    # closure via preds
    changed = True
    while changed:
        changed = False
        for old in sorted(ren.keys(), key=lambda o: ren[o]):
            pr = ndict[old][1]
            if pr >= 5 and pr not in ren:
                r(pr)
                changed = True
    nnodes = tuple(sorted((ren[o], r(ndict[o][1]), ndict[o][2], ndict[o][3]) for o in ren))
    narr = tuple(r(a) for a in arr)
    nprocs = []
    for p in procs:
        paths = tuple(tuple(r(v) for v in pth) for pth in p[F['paths']])
        # paths order: keep as is (indices referenced by todo/sig/tailpath/headpath)
        nprocs.append(setp(p, mynode=r(p[F['mynode']]), mypred=r(p[F['mypred']]), tl=r(p[F['tl']]),
                           cur=r(p[F['cur']]), V=frozenset(r(v) for v in p[F['V']]),
                           E=frozenset((r(u), r(v)) for (u, v) in p[F['E']]), paths=paths))
    return (r(tail), narr, nnodes, tuple(nprocs), rq, cr)


def fresh_id(st):
    tail, arr, nodes, procs, rq, cr = st
    m = 4
    for n in nodes:
        m = max(m, n[0])
    return m + 1


def step(st, q):
    """normal step of process q. returns new state (not canonical)."""
    tail, arr, nodes, procs, rq, cr = st
    p = procs[q]
    pc = p[0]

    def upd(np_, tail_=None, arr_=None, nodes_=None, rq_=None):
        pr = list(procs)
        pr[q] = np_
        return (tail if tail_ is None else tail_, arr if arr_ is None else arr_,
                nodes if nodes_ is None else nodes_, tuple(pr), rq if rq_ is None else rq_, cr)

    my = p[F['mynode']]
    if pc == 10:
        if arr[q] == NIL:
            return upd(setp(p, pc=12, idle=0))  # line 11 merged into 12
        return upd(setp(p, pc=17, idle=0))
    if pc == 12:  # alloc + Node[p] <- mynode
        x = fresh_id(st)
        nodes2 = tuple(sorted(nodes + ((x, NIL, 0, 0),)))
        a = list(arr); a[q] = x
        return upd(setp(p, pc=13, mynode=x), arr_=tuple(a), nodes_=nodes2)
    if pc == 13:
        return upd(setp(p, pc=14, mypred=tail), tail_=my)
    if pc == 14:
        return upd(setp(p, pc=15), nodes_=setnode(nodes, my, pred=p[F['mypred']]))
    if pc == 15:
        return upd(setp(p, pc=25), nodes_=setnode(nodes, my, nonnil=1))
    if pc == 17:
        return upd(setp(p, pc=18, mynode=arr[q]))
    if pc == 18:
        if pred_of(nodes, my) == NIL:
            return upd(setp(p, pc=181))
        return upd(setp(p, pc=19))
    if pc == 181:
        return upd(setp(p, pc=19), nodes_=setnode(nodes, my, pred=CRASH))
    if pc == 19:
        mp = pred_of(nodes, my)
        if mp == INCS:
            return upd(setp(p, pc=27, mypred=mp))
        if mp == EXIT:
            return upd(setp(p, pc=221, mypred=mp))
        return upd(setp(p, pc=23, mypred=mp))
    if pc == 221:
        return upd(setp(p, pc=222), nodes_=setnode(nodes, my, cs=1))
    if pc == 222:
        a = list(arr); a[q] = NIL
        return upd(setp(p, pc=10), arr_=tuple(a))
    if pc == 23:
        return upd(setp(p, pc=24), nodes_=setnode(nodes, my, nonnil=1))
    if pc == 24:
        rq2 = rq if q in rq else rq + (q,)
        if rq2[0] == q:
            return upd(setp(p, pc=30), rq_=rq2)
        return upd(p, rq_=rq2)
    if pc == 30:
        if p[F['mypred']] != CRASH:
            return upd(setp(p, pc=50))  # go to exit of RLock
        return upd(setp(p, pc=33, tl=tail, V=frozenset(), E=frozenset(), i=0, tailpath=-1, headpath=-1))
    if pc == 33:
        i = p[F['i']]
        if i == K:
            V, E = p[F['V']], p[F['E']]
            paths = compute_paths(V, E)
            mp = [j for j, pth in enumerate(paths) if my in pth]
            if len(mp) != 1:
                raise Bug("mypath not unique: %r" % (paths,))
            tp = -1
            if p[F['tl']] in V:
                tps = [j for j, pth in enumerate(paths) if p[F['tl']] in pth]
                if len(tps) != 1:
                    raise Bug("tailpath not unique")
                tp = tps[0]
            # store mypath index in 'cur' field?  use separate: encode mypath index as i (i no longer needed)
            return upd(setp(p, pc=42, paths=paths, i=mp[0], tailpath=tp, todo=frozenset(range(len(paths))),
                            sig=-1))
        c = arr[i]
        if c == NIL:
            return upd(setp(p, i=i + 1))
        return upd(setp(p, pc=35, cur=c))
    if pc == 35:
        if getnode(nodes, p[F['cur']])[2] == 1:
            return upd(setp(p, pc=36))
        return upd(p)
    if pc == 36:
        c = p[F['cur']]
        cp = pred_of(nodes, c)
        V, E = p[F['V']], p[F['E']]
        if cp in SENT:
            V = V | {c}
        else:
            if cp == NIL:
                raise Bug("curpred NIL")
            V = V | {c, cp}
            E = E | {(c, cp)}
        return upd(setp(p, pc=33, V=V, E=E, i=p[F['i']] + 1, cur=0))
    raise Bug("unknown pc %r" % pc)


def steps(st, q):
    """list of successor states for a normal step of q (nondeterminism at line 42)."""
    tail, arr, nodes, procs, rq, cr = st
    p = procs[q]
    pc = p[0]

    def upd(np_, tail_=None, nodes_=None, rq_=None):
        pr = list(procs)
        pr[q] = np_
        return (tail if tail_ is None else tail_, arr, nodes if nodes_ is None else nodes_, tuple(pr),
                rq if rq_ is None else rq_, cr)

    my = p[F['mynode']]
    paths = p[F['paths']]
    if pc == 10 and p[1]:
        if cr // 1000 >= MAXS:
            return []
        st = (tail, arr, nodes, procs, rq, cr + (1000 if MAXS < 10**9 else 0))
        tail, arr, nodes, procs, rq, cr = st
    if pc == 42:
        todo = p[F['todo']]
        if not todo:
            return [upd(setp(p, pc=46))]
        return [upd(setp(p, pc=43, sig=j, todo=todo - {j})) for j in sorted(todo)]
    if pc == 43:
        s = paths[p[F['sig']]]
        if pred_of(nodes, s[-1]) in (INCS, EXIT):
            return [upd(setp(p, pc=44))]
        return [upd(setp(p, pc=42))]
    if pc == 44:
        s = paths[p[F['sig']]]
        if pred_of(nodes, s[0]) != EXIT:
            return [upd(setp(p, pc=42, headpath=p[F['sig']]))]
        return [upd(setp(p, pc=42))]
    if pc == 46:
        tp = p[F['tailpath']]
        if tp == -1 or pred_of(nodes, paths[tp][-1]) in (INCS, EXIT):
            return [upd(setp(p, pc=47))]
        hp = p[F['headpath']]
        mp = paths[hp][0] if hp != -1 else SPECIAL
        return [upd(setp(p, pc=49, mypred=mp))]
    if pc == 47:
        st_ = paths[p[F['i']]][0]
        return [upd(setp(p, pc=49, mypred=tail), tail_=st_)]
    if pc == 49:
        return [upd(setp(p, pc=50), nodes_=setnode(nodes, my, pred=p[F['mypred']]))]
    if pc == 50:  # exit of RLock
        assert rq and rq[0] == q, (rq, q)
        return [upd(setp(p, pc=25), rq_=rq[1:])]
    if pc == 25:
        mp = p[F['mypred']]
        if mp < 4:
            raise Bug("line 25 with mypred=%d" % mp)
        if getnode(nodes, mp)[3] == 1:
            return [upd(setp(p, pc=26))]
        return [upd(p)]
    if pc == 26:
        return [upd(setp(p, pc=27), nodes_=setnode(nodes, my, pred=INCS))]
    if pc == 27:
        return [upd(setp(p, pc=28), nodes_=setnode(nodes, my, pred=EXIT))]
    if pc == 28:
        return [upd(setp(p, pc=29), nodes_=setnode(nodes, my, cs=1))]
    if pc == 29:
        a = list(arr); a[q] = NIL
        return [(tail, tuple(a), nodes, tuple(list(procs[:q]) + [setp(p, pc=10, idle=1)] + list(procs[q + 1:])),
                 rq, cr)]
    return [step(st, q)]


INVIS = (10, 17, 18, 19, 30, 42)


def isinvis(st, q):
    p = st[3][q]
    pc = p[0]
    if pc in INVIS:
        return True
    if pc == 33 and p[F['i']] == q:
        return True
    if pc == 46 and p[F['tailpath']] == -1:
        return True
    return False


def rsteps(st, q):
    out = []
    work = steps(st, q)
    while work:
        s2 = work.pop()
        if isinvis(s2, q):
            work.extend(steps(s2, q))
        else:
            out.append(s2)
    return out


def crash(st, q):
    tail, arr, nodes, procs, rq, cr = st
    pr = list(procs)
    pr[q] = CRASHEDP
    return (tail, arr, nodes, tuple(pr), rq, cr + 1)


def check(st):
    procs = st[3]
    if sum(1 for p in procs if p[0] == 27) > 1:
        raise Bug("mutual exclusion")


def show(st):
    tail, arr, nodes, procs, rq, cr = st
    s = "Tail=%d Node=%s nodes=%s rq=%s cr=%d\n" % (tail, arr, nodes, rq, cr)
    for q, p in enumerate(procs):
        s += "   p%d pc=%d idle=%d my=%d mypred=%d tl=%d V=%s E=%s i=%d cur=%d paths=%s tp=%d hp=%d\n" % (
            q, p[0], p[1], p[2], p[3], p[4], sorted(p[5]), sorted(p[6]), p[7], p[8], p[9], p[12], p[13])
    return s


def main():
    init = (SPECIAL, tuple([NIL] * K), (), tuple([EMPTYP] * K), (), 0)
    init = canon(init)
    if LIVE:
        return main_full(init)
    seen = {hash(init): 0}
    dq = deque([init])
    while dq:
        st = dq.popleft()
        for q in range(K):
            try:
                succ = [canon(s2) for s2 in rsteps(st, q)]
                for s2 in succ:
                    check(s2)
            except Bug as b:
                print("BUG:", b, "process", q)
                print(show(st))
                return
            if st[5] % 1000 < MAXCR and not st[3][q][1]:
                succ.append(canon(crash(st, q)))
            for s2 in succ:
                h = hash(s2)
                if h not in seen:
                    seen[h] = 0
                    dq.append(s2)
        if len(seen) % 500000 == 0:
            print("states", len(seen), len(dq), file=sys.stderr)
    print("OK states", len(seen))


def main_full(init):
    parent = {init: None}
    dq = deque([init])
    edges = {}
    while dq:
        st = dq.popleft()
        succs = []
        for q in range(K):
            for s2 in rsteps(st, q):
                s2 = canon(s2)
                check(s2)
                succs.append((q, 'step', s2))
            if st[5] % 1000 < MAXCR and not st[3][q][1]:
                succs.append((q, 'crash', canon(crash(st, q))))
        edges[st] = succs
        for (q, kind, s2) in succs:
            if s2 not in parent:
                parent[s2] = (st, "%s p%d" % (kind, q))
                dq.append(s2)
    print("OK states", len(parent))
    liveness(edges, parent)


def liveness(edges, parent):
    # crash-free subgraph; for each q, states where q is in Try (not idle, pc != 27, pc not in exit 28/29)
    sys.setrecursionlimit(1000000)
    states = list(edges.keys())
    for q in range(K):
        def inTry(s):
            p = s[3][q]
            return (not p[1]) and p[0] not in (27, 28, 29)
        S = set(s for s in states if inTry(s))
        # Tarjan iterative on S with crash-free edges
        idx = {}
        low = {}
        onst = set()
        stack = []
        comps = []
        counter = [0]
        for root in S:
            if root in idx:
                continue
            work = [(root, iter([s2 for (qq, kk, s2) in edges[root] if kk == 'step' and s2 in S]))]
            idx[root] = low[root] = counter[0]; counter[0] += 1
            stack.append(root); onst.add(root)
            while work:
                v, it = work[-1]
                adv = False
                for w in it:
                    if w not in idx:
                        idx[w] = low[w] = counter[0]; counter[0] += 1
                        stack.append(w); onst.add(w)
                        work.append((w, iter([s2 for (qq, kk, s2) in edges[w] if kk == 'step' and s2 in S])))
                        adv = True
                        break
                    elif w in onst:
                        low[v] = min(low[v], idx[w])
                if adv:
                    continue
                work.pop()
                if work:
                    u = work[-1][0]
                    low[u] = min(low[u], low[v])
                if low[v] == idx[v]:
                    comp = []
                    while True:
                        w = stack.pop(); onst.discard(w)
                        comp.append(w)
                        if w == v:
                            break
                    comps.append(comp)
        bad = 0
        for comp in comps:
            cs = set(comp)
            stepped = set()
            for s in comp:
                for (qq, kk, s2) in edges[s]:
                    if kk == 'step' and s2 in cs:
                        stepped.add(qq)
            if not stepped:
                continue
            ok = True
            for r in range(K):
                if r in stepped:
                    continue
                # r never steps: obligated unless idle
                if not all(s[3][r][1] for s in comp):
                    ok = False
                    break
            if ok:
                bad += 1
                print("STARVATION of p%d: fair SCC of size %d, e.g." % (q, len(comp)))
                print(show(comp[0]))
                # trace to it
                x = comp[0]
                tr = []
                while x is not None:
                    tr.append(x)
                    x = parent[x][0] if parent[x] else None
                for x in reversed(tr):
                    print(parent[x][1] if parent[x] else "init")
                    print(show(x))
                return
        print("p%d: no starvation (%d SCCs)" % (q, len(comps)))


main()
