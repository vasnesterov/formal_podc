#!/usr/bin/env python3
"""Explicit-state model checker for Mostefaoui-Raynal two-bit SWMR register (Fig. 1).

Usage: python3 -I twobit_mc.py N T W R READERS CRASH [VARIANT]
  N processes (0 = writer), T = resilience (quorum N-T), W writes, R reads per reader,
  READERS = comma-separated reader ids, CRASH = max crashes actually injected,
  VARIANT in {paper, noparity, split12}:
    paper    -- Figure 1, every code block between two waits atomic;
    noparity -- line 11 removed (sanity check: the checker must find a wrong value);
    split12  -- lines 1 and 2 of write() executed as two separate atomic steps (message
                handlers may run in between) -> duplicate WRITE message -> wrong value adopted.
Run under resource limits, e.g. (ulimit -v 4000000; timeout 600 python3 -I twobit_mc.py 3 1 2 1 1 0).

Non-FIFO reliable channels (multiset), crash failures (<= T), messages of crashed senders may be
dropped (covers crash in the middle of a broadcast).  Process 0 is the writer; every process may read
(using lines 5-10).  Writes write value k for the k-th write (v0 = 0).

Checks: (a) safety -- the three claims of Lemma 10 (which characterize atomicity of SWMR registers
with distinct values) at each read return, history contents; (b) liveness -- no terminal state in
which a correct process has a pending operation (the graph is acyclic, so every fair maximal run is
finite and ends in a terminal state).
"""
import sys
from collections import deque

N = int(sys.argv[1]) if len(sys.argv) > 1 else 3
T = int(sys.argv[2]) if len(sys.argv) > 2 else 1
W = int(sys.argv[3]) if len(sys.argv) > 3 else 2
R = int(sys.argv[4]) if len(sys.argv) > 4 else 1   # reads per process
READERS = [int(x) for x in sys.argv[5].split(',')] if len(sys.argv) > 5 else list(range(1, N))
CRASH = int(sys.argv[6]) if len(sys.argv) > 6 else T
VARIANT = sys.argv[7] if len(sys.argv) > 7 else "paper"
Q = N - T

# process state: (hist tuple, wsync tuple, rsync tuple, phase, tasks tuple, crashed, opsdone, lb)
# phase: ('idle',) | ('w3', wsn) | ('r7', rsn) | ('r9', sn)
# net: sorted tuple of (src, dst, msg) with msg = ('W', b, v) | ('R',) | ('P',)
# ghost: (winv, wcomp, maxret)


def init():
    ps = tuple(((0,), (0,) * N, (0,) * N, ('idle',), (), False, 0, 0) for _ in range(N))
    return (ps, (), (0, 0, 0))


def setp(ps, i, p):
    return ps[:i] + (p,) + ps[i + 1:]


def addmsgs(net, msgs):
    return tuple(sorted(net + tuple(msgs)))


def rmmsg(net, idx):
    return net[:idx] + net[idx + 1:]


def upd(t, i, v):
    return t[:i] + (v,) + t[i + 1:]


def successors(s):
    ps, net, (winv, wcomp, maxret) = s
    ncrashed = sum(1 for p in ps if p[5])
    out = []
    for i in range(N):
        hist, ws, rs, ph, tasks, cr, done, lb = ps[i]
        if cr:
            continue
        # crash
        if ncrashed < CRASH:
            out.append(('crash', i, (setp(ps, i, (hist, ws, rs, ph, tasks, True, done, lb)), net, (winv, wcomp, maxret))))
        # invocations
        if ph == ('idle',):
            if i == 0 and done < W and winv == wcomp:
                wsn = ws[i] + 1
                ws2 = upd(ws, i, wsn)
                hist2 = hist + (wsn,)
                b = wsn % 2
                msgs = [(i, j, ('W', b, wsn)) for j in range(N) if ws2[j] == wsn - 1]
                p2 = (hist2, ws2, rs, ('w3', wsn), tasks, cr, done, lb)
                if VARIANT == 'split12':
                    msgs = []
                    p2 = (hist2, ws2, rs, ('w2', wsn), tasks, cr, done, lb)
                out.append(('winv', i, (setp(ps, i, p2), addmsgs(net, msgs), (winv + 1, wcomp, maxret))))
            if i in READERS and i != 0 and done < R:
                rsn = rs[i] + 1
                rs2 = upd(rs, i, rsn)
                msgs = [(i, j, ('R',)) for j in range(N) if j != i]
                lb2 = max(wcomp, maxret)
                p2 = (hist, ws, rs2, ('r7', rsn), tasks, cr, done, lb2)
                out.append(('rinv', i, (setp(ps, i, p2), addmsgs(net, msgs), (winv, wcomp, maxret))))
        # waits
        if ph[0] == 'w2':
            wsn = ph[1]
            msgs = [(i, j, ('W', wsn % 2, wsn)) for j in range(N) if ws[j] == wsn - 1]
            p2 = (hist, ws, rs, ('w3', wsn), tasks, cr, done, lb)
            out.append(('w2', i, (setp(ps, i, p2), addmsgs(net, msgs), (winv, wcomp, maxret))))
        if ph[0] == 'w3':
            z = sum(1 for j in range(N) if ws[j] == ph[1])
            if z >= Q:
                p2 = (hist, ws, rs, ('idle',), tasks, cr, done + 1, lb)
                out.append(('wret', i, (setp(ps, i, p2), net, (winv, wcomp + 1, maxret))))
        if ph[0] == 'r7':
            z = sum(1 for j in range(N) if rs[j] == ph[1])
            if z >= Q:
                sn = ws[i]
                p2 = (hist, ws, rs, ('r9', sn), tasks, cr, done, lb)
                out.append(('r8', i, (setp(ps, i, p2), net, (winv, wcomp, maxret))))
        if ph[0] == 'r9':
            sn = ph[1]
            z = sum(1 for j in range(N) if ws[j] >= sn)
            if z >= Q:
                val = hist[sn]
                # checks
                err = None
                if val != sn:
                    err = 'history content'
                if val > winv:
                    err = 'read from future'
                if val < lb:
                    err = 'overwritten/new-old inversion: ret %d < lb %d' % (val, lb)
                p2 = (hist, ws, rs, ('idle',), tasks, cr, done + 1, 0)
                out.append(('rret', i, (setp(ps, i, p2), net, (winv, wcomp, max(maxret, val))), err))
        # proceed tasks
        for k, (j, sn) in enumerate(tasks):
            if k > 0 and tasks[k - 1] == (j, sn):
                continue
            if ws[j] >= sn:
                p2 = (hist, ws, rs, ph, tasks[:k] + tasks[k + 1:], cr, done, lb)
                out.append(('proc', i, (setp(ps, i, p2), addmsgs(net, [(i, j, ('P',))]), (winv, wcomp, maxret))))
    # deliveries / drops
    seen = set()
    for idx, (src, dst, m) in enumerate(net):
        if (src, dst, m) in seen:
            continue
        seen.add((src, dst, m))
        net2 = rmmsg(net, idx)
        if ps[src][5]:
            out.append(('drop', dst, (ps, net2, (winv, wcomp, maxret))))
        if ps[dst][5]:
            # message to crashed process: just drop it (irrelevant)
            out.append(('drop', dst, (ps, net2, (winv, wcomp, maxret))))
            continue
        hist, ws, rs, ph, tasks, cr, done, lb = ps[dst]
        i, j = dst, src
        if m[0] == 'W':
            b, v = m[1], m[2]
            if VARIANT != 'noparity' and b != (ws[j] + 1) % 2:
                continue
            wsn = ws[j] + 1
            msgs = []
            err = None
            if VARIANT == 'noparity' and v != wsn:
                pass
            if wsn == ws[i] + 1:
                ws2 = upd(ws, i, wsn)
                hist2 = hist + (v,)
                if v != wsn:
                    err = 'adopted wrong value %d at %d' % (v, wsn)
                bb = wsn % 2
                msgs = [(i, l, ('W', bb, v)) for l in range(N) if ws2[l] == wsn - 1]
            else:
                ws2 = ws
                hist2 = hist
                if wsn > ws[i] + 1:
                    err = 'lemma3 violated'
                if wsn < ws[i]:
                    msgs = [(i, j, ('W', (wsn + 1) % 2, hist[wsn + 1]))]
            ws2 = upd(ws2, j, wsn)
            p2 = (hist2, ws2, rs, ph, tasks, cr, done, lb)
            out.append(('rcvW', i, (setp(ps, i, p2), addmsgs(net2, msgs), (winv, wcomp, maxret)), err))
        elif m[0] == 'R':
            p2 = (hist, ws, rs, ph, tuple(sorted(tasks + ((j, ws[i]),))), cr, done, lb)
            out.append(('rcvR', i, (setp(ps, i, p2), net2, (winv, wcomp, maxret))))
        else:
            rs2 = upd(rs, j, rs[j] + 1)
            p2 = (hist, ws, rs2, ph, tasks, cr, done, lb)
            out.append(('rcvP', i, (setp(ps, i, p2), net2, (winv, wcomp, maxret))))
    return out


def main():
    s0 = init()
    seen = {s0: None}
    dq = deque([s0])
    terminals = 0
    nstates = 0
    while dq:
        s = dq.popleft()
        nstates += 1
        succ = successors(s)
        real = [x for x in succ if x[0] != 'crash']
        if not real:
            terminals += 1
            ps = s[0]
            for i in range(N):
                if not ps[i][5] and ps[i][3] != ('idle',):
                    print('LIVENESS: stuck pending op at', i, s)
                    trace(seen, s)
                    return
            # also all ops done for correct processes?
        for x in succ:
            name, i, s2 = x[0], x[1], x[2]
            if len(x) > 3 and x[3]:
                print('SAFETY:', x[3], 'step', name, i)
                trace(seen, s)
                return
            if s2 not in seen:
                seen[s2] = (s, name, i)
                dq.append(s2)
        if nstates % 200000 == 0:
            print('states', nstates, len(seen), flush=True)
    print('OK states', nstates, 'terminals', terminals)


def trace(seen, s):
    path = []
    while seen[s] is not None:
        prev, name, i = seen[s]
        path.append((name, i, s))
        s = prev
    for name, i, st in reversed(path):
        print(name, i, '->', st)


main()
