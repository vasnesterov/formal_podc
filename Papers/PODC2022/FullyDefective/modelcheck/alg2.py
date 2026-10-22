# Model checker: Algorithm 1(a) token phase + Algorithm 2 binary data phase, oriented ring.
from collections import deque

def pad(M, L):
    out = []; z = 0
    for b in M:
        out.append(b)
        if b == 0:
            z += 1
            if z == L - 1:
                out.append(1); z = 0
        else:
            z = 0
    return out

def unpad(P, L):
    out = []; z = 0; skip = False
    for b in P:
        if skip:
            assert b == 1; skip = False; z = 0; continue
        out.append(b)
        if b == 0:
            z += 1
            if z == L - 1: skip = True; z = 0
        else: z = 0
    return tuple(out)

def encode(M, L):
    return tuple([1] + pad(list(M), L) + [1] + [0] * L)

def parse(Z, L):
    assert Z[0] == 1 and Z[-L:] == (0,) * L and Z[-L-1] == 1
    return unpad(list(Z[1:-L-1]), L)

def run(n, pushes, T0, L=2, cap=10**7):
    # ph: ('idle',) ('waitReq',) ('ready',) ('rec', Z) non-holder data phase with recorded bits
    #     ('hold', Z, j) holder sent bit j, waiting for it to come back
    nodes = tuple((('idle',), u == T0, (), (), 0) for u in range(n))
    z = (0,) * n
    init = (nodes, z, z, z, z, ())
    seen = {init}; dq = deque([init]); finals = 0
    def upd(t, i, v):
        l = list(t); l[i] = v; return tuple(l)
    while dq:
        st = dq.popleft(); nodes, cwS, cwR, ccwS, ccwR, hist = st
        succ = []
        for u in range(n):
            ph, tok, q, log, pi = nodes[u]
            p = (u - 1) % n; s = (u + 1) % n
            if pi < len(pushes[u]):
                succ.append((upd(nodes, u, (ph, tok, q + (pushes[u][pi],), log, pi + 1)), cwS, cwR, ccwS, ccwR, hist))
            if ph == ('idle',) and q:
                succ.append((upd(nodes, u, (('waitReq',), tok, q, log, pi)), upd(cwS, u, cwS[u] + 1), cwR, ccwS, ccwR, hist))
            def mk(nph, ntok=tok, nq=q, nlog=log):
                return upd(nodes, u, (nph, ntok, nq, nlog, pi))
            cwReady = ph[0] in ('idle', 'waitReq', 'ready', 'rec') or (ph[0] == 'hold' and ph[1][ph[2]] == 1)
            ccwReady = ph[0] in ('ready', 'rec') or (ph[0] == 'hold' and ph[1][ph[2]] == 0)
            if cwS[p] > cwR[u] and cwReady:
                ncwR = upd(cwR, u, cwR[u] + 1)
                if ph[0] in ('idle', 'waitReq'):
                    ncwS = upd(cwS, u, cwS[u] + 1) if ph[0] == 'idle' else cwS
                    nccwS = upd(ccwS, u, ccwS[u] + 1) if tok else ccwS
                    succ.append((mk(('ready',), False), ncwS, ncwR, nccwS, ccwR, hist))
                elif ph[0] == 'ready':
                    succ.append((mk(('rec', (1,))), upd(cwS, u, cwS[u] + 1), ncwR, ccwS, ccwR, hist))
                elif ph[0] == 'rec':
                    succ.append((mk(('rec', ph[1] + (1,))), upd(cwS, u, cwS[u] + 1), ncwR, ccwS, ccwR, hist))
                elif ph[0] == 'hold':
                    Z, j = ph[1], ph[2]
                    succ.append(holdnext(u, nodes, Z, j, tok, q, log, pi, cwS, ncwR, ccwS, ccwR, hist, upd))
            if ccwS[s] > ccwR[u] and ccwReady:
                nccwR = upd(ccwR, u, ccwR[u] + 1)
                if ph[0] == 'ready':
                    if q:
                        M = q[0]; Z = encode(M, L)
                        # send first bit (always 1, clockwise)
                        succ.append((mk(('hold', Z, 0), True, q[1:]), upd(cwS, u, cwS[u] + 1), cwR, ccwS, nccwR, hist + ((u, M),)))
                    else:
                        succ.append((mk(('ready',)), cwS, cwR, upd(ccwS, u, ccwS[u] + 1), nccwR, hist))
                elif ph[0] == 'rec':
                    Z = ph[1] + (0,)
                    nccwS = upd(ccwS, u, ccwS[u] + 1)
                    if len(Z) >= L and Z[-L:] == (0,) * L:
                        try:
                            M = parse(Z, L)
                        except AssertionError:
                            raise Exception(("parse failure", Z, st))
                        succ.append((mk(('idle',), nlog=log + (M,)), cwS, cwR, nccwS, nccwR, hist))
                    else:
                        succ.append((mk(('rec', Z)), cwS, cwR, nccwS, nccwR, hist))
                elif ph[0] == 'hold':
                    Z, j = ph[1], ph[2]
                    succ.append(holdnext(u, nodes, Z, j, tok, q, log, pi, cwS, cwR, ccwS, nccwR, hist, upd))
        for t in succ:
            g = tuple(M for (_, M) in t[5])
            for u in range(n):
                lg = t[0][u][3]
                assert g[:len(lg)] == lg, ("log mismatch", t)
            assert sum(1 for u in range(n) if t[0][u][1]) <= 1
            if t not in seen:
                seen.add(t); dq.append(t)
                if len(seen) > cap: raise Exception("too big")
        if not succ:
            finals += 1
            total = sum(len(x) for x in pushes)
            for u in range(n):
                ph, tok, q, log, pi = nodes[u]
                assert ph == ('idle',) and q == () and len(log) == total, ("stuck", st)
    return len(seen), finals

def holdnext(u, nodes, Z, j, tok, q, log, pi, cwS, cwR, ccwS, ccwR, hist, upd):
    # bit j came back; send bit j+1 or finish
    if j + 1 == len(Z):
        L = 0
        M = hist[-1][1]
        return (upd(nodes, u, (('idle',), tok, q, log + (M,), pi)), cwS, cwR, ccwS, ccwR, hist)
    b = Z[j + 1]
    if b == 1:
        return (upd(nodes, u, (('hold', Z, j + 1), tok, q, log, pi)), upd(cwS, u, cwS[u] + 1), cwR, ccwS, ccwR, hist)
    return (upd(nodes, u, (('hold', Z, j + 1), tok, q, log, pi)), cwS, cwR, upd(ccwS, u, ccwS[u] + 1), ccwR, hist)

if __name__ == '__main__':
    for L in (2, 3):
        for c in [(1, [[(0,), (1, 0)]], 0), (2, [[(0, 0)], [(1,)]], 0), (3, [[(0,)], [], [(1, 0, 0)]], 1),
                  (3, [[(0,)], [(0, 1)], [(1,)]], 2), (4, [[(0,)], [], [(0, 0, 0)], []], 1), (4, [[(1,)], [(0,)], [(0,)], [(1,)]], 0)]:
            print(L, c, run(*c, L=L), flush=True)
