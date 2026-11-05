"""Candidate invariant for the JJJ RME algorithm; checked on reachable states of inv.py."""
NIL, CRASH, INCS, EXIT, SPECIAL = 0, 1, 2, 3, 4


class InvBug(Exception):
    pass


def invcheck(st, K):
    tail, arr, nodes, procs, rq, cr = st
    nd = {n[0]: n for n in nodes}

    def pred(z):
        if z == SPECIAL:
            return EXIT
        return nd[z][1]

    def nn(z):
        return True if z == SPECIAL else bool(nd[z][2])

    def cs(z):
        return True if z == SPECIAL else bool(nd[z][3])

    def released(z):
        return pred(z) == EXIT and cs(z)

    def vp(q):
        p = procs[q]
        if p[0] in (14, 49):
            return p[3]
        return pred(arr[q])

    def fail(msg):
        raise InvBug(msg)

    active = {arr[q]: q for q in range(K) if arr[q] != NIL}
    behind = {}
    for q in range(K):
        if arr[q] == NIL:
            continue
        v = vp(q)
        if v >= 4:
            if v in behind:
                fail("S2 two behind %d" % v)
            behind[v] = arr[q]
    # node table
    for z in nd:
        if z not in active and not released(z):
            fail("table: inactive unreleased node %d" % z)
        if cs(z) and pred(z) != EXIT:
            fail("S4 csig")
        if nn(z) and pred(z) == NIL:
            fail("S4 nn")
    if tail in behind:
        fail("S2 behind Tail")
    for q in range(K):
        p = procs[q]
        if p[0] == 13:
            if p[2] in behind or p[2] == tail:
                fail("S2 l13")
    H = []
    for y in active:
        q = active[y]
        v = vp(q)
        if pred(y) == INCS or (v >= 4 and released(v)) or \
                (pred(y) == EXIT and not cs(y) and (y in behind or tail == y)):
            H.append(y)
    # WF of current links
    for y in active:
        seen = set()
        z = y
        while z in active and vp(active[z]) >= 4:
            if z in seen:
                fail("WF cycle")
            seen.add(z)
            z = vp(active[z])

    def root(z):
        while z in active and vp(active[z]) >= 4:
            z = vp(active[z])
        return pred(z) if z not in active else vp(active[z])
    if len(H) > 1:
        fail("S1 H=%r" % H)
    if released(tail) and H:
        fail("S3")
    # repairer
    for q in range(K):
        p = procs[q]
        pc = p[0]
        if pc not in (33, 35, 36, 42, 43, 44, 46, 47):
            continue
        x = p[2]
        tl = p[4]
        V, E = p[5], p[6]
        EA = p[14]

        def late(y):
            return y not in EA
        if pc != 47:
            if late(tl) or late(x):
                fail("R1")
            if not (tail == tl or late(tail)):
                fail("R2")
            for y in active:
                v = vp(active[y])
                if v >= 4:
                    if late(y) and not (v == tl or late(v)):
                        fail("R3a")
                    if not late(y) and late(v):
                        fail("R3b")
                if late(y) and pred(y) in (INCS, EXIT) and pred(tl) != EXIT:
                    fail("R4")
            for (u, v) in E:
                if not (pred(u) == v or (pred(u) in (INCS, EXIT) and released(v))):
                    fail("R5 E1 %d %d" % (u, v))
                if v in behind and behind[v] != u:
                    fail("R6 E2")
                if v == tail:
                    fail("R6 tail")
            scanned = range(p[7]) if pc in (33, 35, 36) else range(K)
            for j in scanned:
                y = arr[j]
                if y == NIL or late(y):
                    continue
                if y not in V:
                    fail("R7 not in V")
                v = vp(j)
                if v >= 4 and (y, v) not in E:
                    fail("R7 edge")
            if pc in (42, 43, 44, 46):
                outs = {u for (u, v) in E}
                for u in V:
                    if u not in outs and not late(u):
                        if not (pred(u) in (CRASH, INCS, EXIT)):
                            fail("R8 sink")
                ins = [v for (u, v) in E]
                if len(ins) != len(set(ins)):
                    fail("R9 indeg")
                paths = p[9]
                hp = p[13]
                Hempty = not H
                if hp != -1:
                    sg = paths[hp]
                    if pred(sg[-1]) not in (INCS, EXIT):
                        fail("R10a")
                    outm = {u: v for (u, v) in E}
                    tgood = tl not in V
                    if not tgood:
                        z = tl
                        while z in outm:
                            z = outm[z]
                        tgood = pred(z) in (INCS, EXIT)
                    if pred(sg[0]) == EXIT and not Hempty and not tgood:
                        fail("R10b")
                tp = p[12]
                attach = tp != -1 and pred(paths[tp][-1]) not in (INCS, EXIT)
                if attach:
                    if root(tl) not in (CRASH,):
                        fail("Broken tl root=%d" % root(tl))
                    if released(tail):
                        fail("attach tail released")
                    if hp != -1:
                        m = paths[hp][0]
                        if m in behind or m == tail:
                            fail("attach hp i/ii")
                if pc == 46:
                    if attach:
                        m = paths[hp][0] if hp != -1 else SPECIAL
                        if m in behind or m == tail:
                            fail("46 attach m")
                        if pred(m) == EXIT and H:
                            fail("46 attach H")
                    else:
                        sm = paths[p[7]][0]
                        if sm in behind or sm == tail:
                            fail("46 fas s")
                if pc in (42, 43, 44):
                    todo = set(p[10])
                    cur = p[11] if pc in (43, 44) else -1
                    for j in range(len(paths)):
                        if j in todo or j == cur:
                            continue
                        sg = paths[j]
                        if pred(sg[-1]) in (INCS, EXIT) and not late(sg[-1]):
                            if not (pred(sg[0]) == EXIT or hp != -1):
                                fail("R11")
        else:
            s = p[9][p[7]][0]
            if s in behind or s == tail:
                fail("R12")
    return True


def F_s(p):
    return 15  # placeholder (not used)
