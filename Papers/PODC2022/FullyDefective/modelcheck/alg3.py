# Exhaustive model checker for Algorithm 3 (simulator over a Robbins cycle), blocking-receive semantics.
import sys
from collections import deque

class Bug(Exception): pass

def setup(C, tau):
    L = len(C); V = sorted(set(C))
    occ = {}
    for u in V:
        pos = [j for j in range(L) if C[j] == u]
        # occurrence 0: first occurrence at or after tau (cw)
        pos.sort(key=lambda j: (j - tau) % L)
        occ[u] = pos
    prev = {u: tuple(C[(j-1) % L] for j in occ[u]) for u in V}
    nxt = {u: tuple(C[(j+1) % L] for j in occ[u]) for u in V}
    return V, prev, nxt

def run(C, tau, pushes, cap=3*10**6):
    V, prev0, next0 = setup(C, tau)
    T0 = C[tau]
    edges = sorted(set((C[j], C[(j+1) % len(C)]) for j in range(len(C))))
    for (x, y) in edges:
        assert (y, x) not in edges, "not a Robbins cycle"
    alle = sorted(set(edges) | set((y, x) for (x, y) in edges))
    eidx = {e: i for i, e in enumerate(alle)}
    E = len(alle)
    # node: (ph, tok, q, log, pi, prev, next, cnt)
    # ph: ('idle',) ('waitReq', got tuple per i?)  we track REQ counts per incoming edge as tuple over edges
    nodes = {}
    for u in V:
        nodes[u] = (('idle',), u == T0, (), (), 0, prev0[u], next0[u], 0)
    def key(nodes, S, R, hist):
        return (tuple(nodes[u] for u in V), S, R, hist)
    S0 = (0,)*E; R0 = (0,)*E
    init = (dict(nodes), S0, R0, ())
    seen = {key(*init)}
    dq = deque([init])
    finals = 0
    def mult(u, pv):  # required REQ pulses per incoming edge
        m = {}
        for x in pv:
            m[(x, u)] = m.get((x, u), 0) + 1
        return m
    while dq:
        nodes, S, R, hist = dq.popleft()
        succ = []
        def inc(t, e, k=1):
            l = list(t); l[eidx[e]] += k; return tuple(l)
        def avail(e):
            return S[eidx[e]] > R[eidx[e]]
        for u in V:
            ph, tok, q, log, pi, pv, nx, cnt = nodes[u]
            k = len(pv)
            def mk(nph, ntok=tok, nq=q, nlog=log, npi=pi, npv=pv, nnx=nx, ncnt=cnt):
                d = dict(nodes); d[u] = (nph, ntok, nq, nlog, npi, npv, nnx, ncnt); return d
            if pi < len(pushes.get(u, [])):
                succ.append((mk(ph, nq=q + (pushes[u][pi],), npi=pi+1), S, R, hist))
            def sendreq(S):
                for x in nx: S = inc(S, (u, x))
                return S
            def afterreq(S, tok):
                # lines 4-7
                if tok:
                    S = inc(S, (u, pv[0])); tok = False
                return S, tok
            if ph[0] == 'idle':
                if q:
                    succ.append((mk(('waitReq', ()),), sendreq(S), R, hist))
                for x in sorted(set(pv)):
                    e = (x, u)
                    if avail(e):
                        nS = sendreq(S); nR = inc(R, e)
                        got = ((e, 1),)
                        m = mult(u, pv)
                        if all(dict(got).get(ee, 0) >= m[ee] for ee in m):
                            nS, ntok = afterreq(nS, tok)
                            succ.append((mk(('ready',), ntok), nS, nR, hist))
                        else:
                            succ.append((mk(('waitReq', got)), nS, nR, hist))
            elif ph[0] == 'waitReq':
                got = dict(ph[1]); m = mult(u, pv)
                for e in sorted(m):
                    if got.get(e, 0) < m[e] and avail(e):
                        g2 = dict(got); g2[e] = g2.get(e, 0) + 1
                        nR = inc(R, e)
                        if all(g2.get(ee, 0) >= m[ee] for ee in m):
                            nS, ntok = afterreq(S, tok)
                            succ.append((mk(('ready',), ntok), nS, nR, hist))
                        else:
                            succ.append((mk(('waitReq', tuple(sorted(g2.items())))), S, nR, hist))
            elif ph[0] == 'ready':
                # ccw pulses from next nodes
                for x in sorted(set(nx)):
                    e = (x, u)
                    if avail(e):
                        nR = inc(R, e)
                        if x != nx[k-1]:
                            raise Bug(("token from wrong edge", u, e, nodes, hist))
                        npv = (pv[k-1],) + pv[:k-1]; nnx = (nx[k-1],) + nx[:k-1]
                        if q:
                            d = q[0]
                            # holder: send first data to next_0, wait from prev_{1 mod k}
                            nS = inc(S, (u, nnx[0]))
                            succ.append((mk(('hdata', 1, 0, d), True, q[1:], npv=npv, nnx=nnx), nS, nR, hist + ((u, d),)))
                        else:
                            nS = inc(S, (u, npv[0]))
                            succ.append((mk(('ready',), npv=npv, nnx=nnx), nS, nR, hist))
                for x in sorted(set(pv)):
                    e = (x, u)
                    if avail(e):
                        nR = inc(R, e)
                        if x != pv[0]:
                            raise Bug(("first data from wrong edge", u, e, nodes, hist))
                        nS = inc(S, (u, nx[0]))
                        nph = ('fdata', 1 % k, 1 if k == 1 else 0)  # (i, completed tours)
                        succ.append((mk(nph, ncnt=1), nS, nR, hist))
            elif ph[0] == 'fdata':
                i, tours = ph[1], ph[2]
                e = (pv[i], u)
                if avail(e):
                    nR = inc(R, e); nS = inc(S, (u, nx[i]))
                    ni = (i + 1) % k; nt = tours + (1 if ni == 0 else 0)
                    succ.append((mk(('fdata', ni, nt), ncnt=cnt+1), nS, nR, hist))
                if i == 0:
                    for x in sorted(set(nx)):
                        e2 = (x, u)
                        if avail(e2):
                            if x != nx[k-1]:
                                raise Bug(("end from wrong edge", u, e2))
                            nR = inc(R, e2)
                            if cnt % k != 0: raise Bug(("count not multiple", u))
                            c = cnt // k
                            nlog = log + (c,)
                            nS = inc(S, (u, pv[k-1]))
                            if k == 1:
                                succ.append((mk(('idle',), nlog=nlog, ncnt=0), nS, nR, hist))
                            else:
                                succ.append((mk(('fend', k-2), nlog=nlog, ncnt=0), nS, nR, hist))
            elif ph[0] == 'fend':
                i = ph[1]
                e = (nx[i], u)
                if avail(e):
                    nR = inc(R, e); nS = inc(S, (u, pv[i]))
                    if i == 0:
                        succ.append((mk(('idle',)), nS, nR, hist))
                    else:
                        succ.append((mk(('fend', i-1)), nS, nR, hist))
            elif ph[0] == 'hdata':
                t, i, d = ph[1], ph[2], ph[3]
                # sent data #t to next_i, waiting from prev_{(i+1)%k}
                e = (pv[(i+1) % k], u)
                if avail(e):
                    nR = inc(R, e)
                    if i + 1 < k:
                        nS = inc(S, (u, nx[i+1]))
                        succ.append((mk(('hdata', t, i+1, d)), nS, nR, hist))
                    elif t < d:
                        nS = inc(S, (u, nx[0]))
                        succ.append((mk(('hdata', t+1, 0, d)), nS, nR, hist))
                    else:
                        # END loop: i from k-1: send END to prev_{(i+1)%k}, wait END from next_i
                        nS = inc(S, (u, pv[0]))
                        succ.append((mk(('hend', k-1, d)), nS, nR, hist))
            elif ph[0] == 'hend':
                i, d = ph[1], ph[2]
                e = (nx[i], u)
                if avail(e):
                    nR = inc(R, e)
                    if i == 0:
                        succ.append((mk(('idle',), nlog=log + (d,)), S, nR, hist))
                    else:
                        nS = inc(S, (u, pv[i]))
                        succ.append((mk(('hend', i-1, d)), nS, nR, hist))
        for t in succ:
            tn, _, _, th = t
            g = tuple(d for (_, d) in th)
            for u in V:
                lg = tn[u][3]
                if g[:len(lg)] != lg: raise Bug(("log mismatch", u, lg, g))
            if sum(1 for u in V if tn[u][1]) > 1: raise Bug("two tokens")
            kk = key(*t)
            if kk not in seen:
                seen.add(kk); dq.append(t)
                if len(seen) > cap: raise Exception("too big")
        if not succ:
            finals += 1
            total = sum(len(x) for x in pushes.values())
            for u in V:
                ph, tok, q, log, pi, pv, nx, cnt = nodes[u]
                if not (ph == ('idle',) and q == () and pi == len(pushes.get(u, [])) and len(log) == total):
                    raise Bug(("stuck", {v: nodes[v] for v in V}, S, R, hist))
            if S != R: raise Bug(("transit", S, R))
    return len(seen), finals

if __name__ == '__main__':
    cases = [
        ([0, 1, 2], 0, {0: [1], 2: [2]}),
        ([0, 1, 2, 3, 4, 2], 0, {1: [1], 3: [1]}),          # bowtie a b d c e d
        ([0, 1, 2, 3, 4, 2], 2, {0: [1], 4: [2]}),
        ([0, 1, 2, 3, 4, 2], 5, {2: [1], 3: [1], 0: [1]}),
        ([0, 1, 2, 3, 0, 1, 2], 0, {3: [1], 1: [1]}),       # repeated edges 0->1, 1->2
        ([0, 1, 2, 3, 0, 1, 2], 5, {0: [1], 2: [2]}),
        ([0, 1, 2, 3, 0, 1, 2], 3, {1: [1, 1], 2: [1]}),
        ([0, 1, 2, 3, 0, 1, 2], 6, {0: [1], 1: [1], 3: [1]}),
    ]
    for c in cases:
        try:
            print(c, run(*c), flush=True)
        except Bug as b:
            print(c, "BUG", b.args[0] if isinstance(b.args[0], str) else b.args[0][:2], flush=True)
            print("   detail:", b.args)
