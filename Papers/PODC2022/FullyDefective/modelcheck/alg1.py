# Exhaustive model checker for Algorithm 1 (simple cycle simulator), content-oblivious ring.
import sys
from collections import deque

def run(n, pushes, T0, check_cap=10**7):
    # node state: (ph, tok, q, ep, log, pi) ; ph: ('idle',), ('waitReq',), ('ready',), ('send',d,r), ('waitEnd',d), ('fwd',c)
    # pi: index into pushes[u] already pushed
    nodes = tuple((('idle',), u == T0, (), 0, (), 0) for u in range(n))
    cwS = (0,)*n; cwR=(0,)*n; ccwS=(0,)*n; ccwR=(0,)*n
    hist = ()  # global ghost: tuple of (holder, d)
    init = (nodes, cwS, cwR, ccwS, ccwR, hist)
    seen = {init}
    dq = deque([init])
    finals = 0
    while dq:
        st = dq.popleft()
        nodes, cwS, cwR, ccwS, ccwR, hist = st
        succ = []
        def upd(tup, i, v):
            l = list(tup); l[i] = v; return tuple(l)
        for u in range(n):
            ph, tok, q, ep, log, pi = nodes[u]
            # push
            if pi < len(pushes[u]):
                succ.append((upd(nodes, u, (ph, tok, q + (pushes[u][pi],), ep, log, pi+1)), cwS, cwR, ccwS, ccwR, hist))
            # start
            if ph == ('idle',) and q:
                succ.append((upd(nodes, u, (('waitReq',), tok, q, ep, log, pi)), upd(cwS, u, cwS[u]+1), cwR, ccwS, ccwR, hist))
            p = (u - 1) % n; s = (u + 1) % n
            # receive cw
            if cwS[p] > cwR[u] and ph[0] in ('idle', 'waitReq', 'ready', 'send', 'fwd'):
                ncwR = upd(cwR, u, cwR[u]+1)
                ncwS, nccwS, ntok, nq, nh = cwS, ccwS, tok, q, hist
                nlog, nep = log, ep
                if ph[0] in ('idle', 'waitReq'):
                    if ph[0] == 'idle':
                        ncwS = upd(ncwS, u, ncwS[u]+1)
                    if tok:
                        ntok = False; nccwS = upd(nccwS, u, nccwS[u]+1)
                    nph = ('ready',)
                elif ph[0] == 'ready':
                    ncwS = upd(ncwS, u, ncwS[u]+1); nph = ('fwd', 1)
                elif ph[0] == 'fwd':
                    ncwS = upd(ncwS, u, ncwS[u]+1); nph = ('fwd', ph[1]+1)
                elif ph[0] == 'send':
                    d, r = ph[1], ph[2]
                    if r + 1 < d: nph = ('send', d, r+1)
                    else:
                        nccwS = upd(nccwS, u, nccwS[u]+1); nph = ('waitEnd', d)
                succ.append((upd(nodes, u, (nph, ntok, nq, nep, nlog, pi)), ncwS, ncwR, nccwS, ccwR, nh))
            # receive ccw
            if ccwS[s] > ccwR[u] and ph[0] in ('ready', 'fwd', 'waitEnd'):
                nccwR = upd(ccwR, u, ccwR[u]+1)
                ncwS, nccwS, ntok, nq, nh = cwS, ccwS, tok, q, hist
                nlog, nep = log, ep
                if ph[0] == 'ready':
                    if q:
                        d = q[0]; nq = q[1:]; ntok = True
                        assert not tok
                        ncwS = upd(ncwS, u, ncwS[u]+d); nph = ('send', d, 0)
                        nh = hist + ((u, d),)
                    else:
                        nccwS = upd(nccwS, u, nccwS[u]+1); nph = ('ready',)
                elif ph[0] == 'fwd':
                    c = ph[1]
                    nlog = log + (c,); nep = ep+1
                    nccwS = upd(nccwS, u, nccwS[u]+1); nph = ('idle',)
                elif ph[0] == 'waitEnd':
                    nlog = log + (ph[1],); nep = ep + 1; nph = ('idle',)
                succ.append((upd(nodes, u, (nph, ntok, nq, nep, nlog, pi)), ncwS, cwR, nccwS, nccwR, nh))
        for t in succ:
            # invariants
            tn = t[0]; th = t[5]
            g = tuple(d for (_, d) in th)
            for u in range(n):
                lg = tn[u][4]
                assert g[:len(lg)] == lg, ("log mismatch", t)
            assert sum(1 for u in range(n) if tn[u][1]) <= 1, ("two tokens", t)
            if t not in seen:
                seen.add(t); dq.append(t)
                if len(seen) > check_cap: raise Exception("too big")
        if not succ:
            finals += 1
            # final: everything delivered
            total = sum(len(x) for x in pushes)
            for u in range(n):
                ph, tok, q, ep, log, pi = nodes[u]
                assert ph == ('idle',) and q == () and pi == len(pushes[u]), ("stuck", st)
                assert len(log) == total, ("missing", st)
            for u in range(n):
                assert cwS[(u-1)%n] == cwR[u] and ccwS[(u+1)%n] == ccwR[u], ("transit", st)
            # per-holder FIFO
            for u in range(n):
                assert tuple(d for (h, d) in hist if h == u) == tuple(pushes[u]), ("fifo", st)
    return len(seen), finals

if __name__ == '__main__':
    cases = [
        (1, [[2, 1]], 0),
        (2, [[1], [2]], 0),
        (2, [[2], [1, 1]], 1),
        (3, [[1], [], [2]], 0),
        (3, [[1], [2], [1]], 1),
        (3, [[2, 1], [], [1]], 2),
        (4, [[1], [], [1], []], 0),
        (4, [[], [1], [], [2]], 1),
        (4, [[1], [1], [1], [1]], 2),
        (5, [[1], [], [1], [], []], 3),
    ]
    for c in cases:
        print(c, run(*c), flush=True)
