#!/usr/bin/env python3
"""Exhaustive model checker for Algorithm 1 (Figure 1) of
Attiya, Castaneda, Hendler, Perrin, "Separating Lock-Freedom from Wait-Freedom" (PODC 2018):
lock-free 2-LLAA for processes p0, p1.

Steps of p_i:
  INV    (model B only) silent invocation event
  WROUND line 01-02: me.round += 1; M[i].round <- me.round   (model A: this IS the invocation)
  WPOS   line 04:    M[i].pos <- me.pos
  READ   lines 05-15 atomically: you <- M[j]; rounds; range; test; maybe return.

Line 08 readings:
  'notin' : you.pos in range  OR  you.pos not in prev     (this is what the paper writes)
  'less'  : you.pos in range  OR  you.pos < min(prev)    (deliberately wrong mutant, only used to
            check that the checker detects linearizability violations; it does, from K=(1,3))
  'mutant': closeness radius doubled (another sanity-check mutant)

Usage (bounded resources): (ulimit -v 4000000; timeout 600 python3 -I llaa_mc.py notin)
Result with 'notin': lock-free and linearizable for all K up to (3,3), in both invocation models.
Not part of the Lean development.

Checks:
  (a) linearizability of every reachable quiescent history w.r.t. 2-LLAA (Definition 1);
  (b) lock-freedom: no reachable cycle (all cycles are return-free since done-counters are monotone),
      and no unbounded run (iteration cap);
  (c) max loop iterations per op, number of states.
"""
import sys
from fractions import Fraction as F
from collections import deque

IDLE, INVOKED, WPOS, READ = 0, 1, 2, 3
PCNAME = {IDLE: 'idle', INVOKED: 'invoked', WPOS: 'at04', READ: 'at05'}


def init_state():
    shared = (F(0), 0, F(1), 0)  # M[0].pos, M[0].round, M[1].pos, M[1].round
    procs = []
    for i in (0, 1):
        j = 1 - i
        # pc, mepos, meround, youpos, youround, prevlo, prevhi, done
        procs.append((IDLE, F(i), 0, F(j), 0, F(i - 1), F(i + 1), 0))
    return (shared, procs[0], procs[1])


def get_M(shared, k):
    return (shared[0], shared[1]) if k == 0 else (shared[2], shared[3])


def set_M(shared, k, pos=None, rnd=None):
    s = list(shared)
    if pos is not None:
        s[2 * k] = pos
    if rnd is not None:
        s[2 * k + 1] = rnd
    return tuple(s)


def steps(state, i, K, modelB, reading):
    """Yield (label, newstate, event) for the enabled steps of p_i.
    event: None | ('inv', i) | ('ret', i, value)."""
    shared, p0, p1 = state
    p = p0 if i == 0 else p1
    pc, mepos, mer, youpos, your, plo, phi, done = p
    j = 1 - i

    def mk(sh, np):
        return (sh, np, p1) if i == 0 else (sh, p0, np)

    if pc == IDLE:
        if done >= K[i]:
            return
        if modelB:
            yield ('INV', mk(shared, (INVOKED, mepos, mer, youpos, your, plo, phi, done)), ('inv', i))
        else:
            nr = mer + 1
            yield ('INV+WROUND', mk(set_M(shared, i, rnd=nr), (WPOS, mepos, nr, youpos, your, plo, phi, done)),
                   ('inv', i))
    elif pc == INVOKED:
        nr = mer + 1
        yield ('WROUND', mk(set_M(shared, i, rnd=nr), (WPOS, mepos, nr, youpos, your, plo, phi, done)), None)
    elif pc == WPOS:
        yield ('WPOS', mk(set_M(shared, i, pos=mepos), (READ, mepos, mer, youpos, your, plo, phi, done)), None)
    elif pc == READ:
        ypos, yr = get_M(shared, j)
        rounds = mer + yr
        d = F(1, 2 ** rounds)
        rlo, rhi = mepos - d, mepos + d
        if reading == 'mutant':  # sanity-check mutant: closeness radius doubled
            rlo, rhi = mepos - 2 * d, mepos + 2 * d
        inrange = rlo <= ypos <= rhi
        if reading == 'notin':
            invalid = not (plo <= ypos <= phi)
        else:
            invalid = ypos < plo
        if inrange or invalid:
            np = (IDLE, mepos, mer, ypos, yr, rlo, rhi, done + 1)
            yield ('READ->ret %s (%s)' % (mepos, 'close' if inrange else 'invalid'), mk(shared, np),
                   ('ret', i, mepos))
        else:
            npos = mepos + d if mepos < ypos else mepos - d
            np = (WPOS, npos, mer, ypos, yr, plo, phi, done)
            yield ('READ->move to %s' % npos, mk(shared, np), None)


def all_steps(state, K, modelB, reading):
    for i in (0, 1):
        for lab, ns, ev in steps(state, i, K, modelB, reading):
            yield i, lab, ns, ev


def legal_linearizable(vals0, vals1, need0, need1):
    """vals_i: outputs of p_i's ops; need0[x] = #ops of p1 that completed before invocation of P0^{x+1}
    (they must be linearized before it); similarly need1. Returns a witness order or None."""
    n0, n1 = len(vals0), len(vals1)
    pos0 = [F(0)] + list(vals0)
    pos1 = [F(1)] + list(vals1)
    # reachable (x, y) prefix states; parent pointers
    par = {(0, 0): None}
    stack = [(0, 0)]
    while stack:
        x, y = stack.pop()
        if (x, y) == (n0, n1):
            order = []
            cur = (n0, n1)
            while par[cur] is not None:
                prv = par[cur]
                order.append('P0^%d' % cur[0] if cur[0] != prv[0] else 'P1^%d' % cur[1])
                cur = prv
            return list(reversed(order))
        r = x + y + 1
        if x < n0 and y >= need0[x] and (x + 1, y) not in par:
            if abs(pos0[x + 1] - pos1[y]) <= F(1, 2 ** r):
                par[(x + 1, y)] = (x, y)
                stack.append((x + 1, y))
        if y < n1 and x >= need1[y] and (x, y + 1) not in par:
            if abs(pos0[x] - pos1[y + 1]) <= F(1, 2 ** r):
                par[(x, y + 1)] = (x, y)
                stack.append((x, y + 1))
    return None


def fmt_state(s):
    sh, p0, p1 = s
    out = 'M0=(%s,r%d) M1=(%s,r%d)' % (sh[0], sh[1], sh[2], sh[3])
    for i, p in ((0, p0), (1, p1)):
        out += ' | p%d %s me=(%s,r%d) you=(%s,r%d) prev=[%s,%s] done=%d' % (
            i, PCNAME[p[0]], p[1], p[2], p[3], p[4], p[5], p[6], p[7])
    return out


def check_lockfree(K, modelB, reading, cap_states=3_000_000):
    """Build the reachable graph; detect cycles; compute max iterations per op."""
    s0 = init_state()
    succ = {}
    order = deque([s0])
    seen = {s0}
    while order:
        s = order.popleft()
        lst = []
        for i, lab, ns, ev in all_steps(s, K, modelB, reading):
            lst.append((i, lab, ns, ev))
            if ns not in seen:
                seen.add(ns)
                order.append(ns)
                if len(seen) > cap_states:
                    return {'aborted': True, 'states': len(seen)}
        succ[s] = lst
    # cycle detection: iterative DFS with colors
    WHITE, GREY, BLACK = 0, 1, 2
    color = {s: WHITE for s in succ}
    cycle = None
    for root in succ:
        if color[root] != WHITE or cycle:
            continue
        stack = [(root, iter(succ[root]))]
        path = [root]
        color[root] = GREY
        while stack and not cycle:
            s, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                color[s] = BLACK
                stack.pop()
                path.pop()
                continue
            t = nxt[2]
            if color[t] == GREY:
                k = path.index(t)
                cycle = path[k:] + [t]
            elif color[t] == WHITE:
                color[t] = GREY
                stack.append((t, iter(succ[t])))
                path.append(t)
    res = {'aborted': False, 'states': len(succ), 'cycle': cycle}
    if cycle:
        return res
    # longest number of READ steps of p_i within its current op (DAG DP, reverse topological via post-order)
    topo = []
    vis = set()
    for root in succ:
        if root in vis:
            continue
        vis.add(root)
        stack = [(root, iter(succ[root]))]
        while stack:
            s, it = stack[-1]
            nxt = next(it, None)
            if nxt is None:
                topo.append(s)
                stack.pop()
                continue
            t = nxt[2]
            if t not in vis:
                vis.add(t)
                stack.append((t, iter(succ[t])))
    L = [{}, {}]
    maxit = [0, 0]
    for s in topo:  # successors first
        for i in (0, 1):
            pc = s[1 + i][0]
            best = 0
            if pc != IDLE:
                for (pi, lab, t, ev) in succ[s]:
                    if pi == i and lab.startswith('READ'):
                        v = 1 if ev is not None else 1 + L[i][t]
                    else:
                        v = L[i][t]
                    best = max(best, v)
            L[i][s] = best
            maxit[i] = max(maxit[i], best)
    res['max_iters'] = maxit
    return res


def check_lin(K, modelB, reading, cap_states=6_000_000):
    """DFS over (state, history abstraction); check every quiescent history."""
    s0 = init_state()
    h0 = ((), (), (), ())  # vals0, vals1, need0, need1
    start = (s0, h0)
    seen = {start}
    parent = {start: None}
    stack = [start]
    checked = {}
    nquiescent = 0
    while stack:
        node = stack.pop()
        s, h = node
        if s[1][0] == IDLE and s[2][0] == IDLE:
            nquiescent += 1
            if h not in checked:
                w = legal_linearizable(*h)
                checked[h] = w
                if w is None:
                    # reconstruct trace
                    trace = []
                    cur = node
                    while parent[cur] is not None:
                        prv, lab = parent[cur]
                        trace.append((lab, cur[0]))
                        cur = prv
                    trace.reverse()
                    return {'ok': False, 'history': h, 'trace': trace, 'states': len(seen)}
        for i, lab, ns, ev in all_steps(s, K, modelB, reading):
            vals0, vals1, need0, need1 = h
            if ev is not None and ev[0] == 'inv':
                if i == 0:
                    need0 = need0 + (len(vals1),)
                else:
                    need1 = need1 + (len(vals0),)
            elif ev is not None and ev[0] == 'ret':
                if i == 0:
                    vals0 = vals0 + (ev[2],)
                else:
                    vals1 = vals1 + (ev[2],)
            nn = (ns, (vals0, vals1, need0, need1))
            if nn not in seen:
                seen.add(nn)
                parent[nn] = (node, 'p%d %s' % (i, lab))
                stack.append(nn)
                if len(seen) > cap_states:
                    return {'ok': None, 'aborted': True, 'states': len(seen)}
    return {'ok': True, 'states': len(seen), 'histories': len(checked), 'quiescent': nquiescent}


def run_schedule(sched, reading='notin'):
    """Run a fixed schedule: list of process ids (model A). Print each step."""
    s = init_state()
    K = (10, 10)
    for i in sched:
        st = list(steps(s, i, K, False, reading))
        assert len(st) == 1, (i, fmt_state(s))
        lab, s, ev = st[0]
        print('  p%d %-28s %s' % (i, lab, fmt_state(s)))
    return s


def paper_example():
    print('== Section 3.2 example ==')
    # p0: invoke, WPOS, READ (one iteration, moves to 1/2), stops before WPOS
    sched = [0, 0, 0]
    # p1: two complete ops; run p1 solo until two returns
    s = run_schedule(sched)
    K = (10, 10)
    rets = []
    for who, nops in ((1, 2), (0, 1)):
        cnt = 0
        while cnt < nops:
            lab, s, ev = list(steps(s, who, K, False, 'notin'))[0]
            print('  p%d %-28s %s' % (who, lab, fmt_state(s)))
            if ev and ev[0] == 'ret':
                cnt += 1
                rets.append((who, ev[2]))
    print('  returns:', [(w, str(v)) for w, v in rets])
    assert rets == [(1, F(1, 4)), (1, F(1, 8)), (0, F(1, 4))]


def main():
    paper_example()
    bounds = [(1, 1), (1, 2), (2, 1), (2, 2), (1, 3), (3, 1), (2, 3), (3, 2), (3, 3)]
    only = None
    if len(sys.argv) > 1 and sys.argv[1] in ('notin', 'less'):
        only = sys.argv.pop(1)
    if len(sys.argv) > 1:
        bounds = [('mutant',)] if sys.argv[1] == 'mutant' else \
            [tuple(int(x) for x in a.split(',')) for a in sys.argv[1:]]
    readings = (only,) if only else ('notin', 'less')
    if bounds and bounds[0] == ('mutant',):
        readings, bounds = ('mutant',), [(1, 1), (1, 2), (2, 2)]
    for reading in readings:
        for modelB in (False, True):
            for K in bounds:
                lf = check_lockfree(K, modelB, reading)
                msg = 'reading=%-5s model=%s K=%s: ' % (reading, 'B' if modelB else 'A', K)
                if lf.get('aborted'):
                    print(msg + 'lock-freedom ABORTED at %d states' % lf['states'])
                    continue
                if lf['cycle']:
                    print(msg + 'LOCK-FREEDOM VIOLATED: cycle of length %d' % (len(lf['cycle']) - 1))
                    for c in lf['cycle']:
                        print('    ', fmt_state(c))
                else:
                    msg += 'lock-free OK (%d states, max iters/op p0=%d p1=%d); ' % (
                        lf['states'], lf['max_iters'][0], lf['max_iters'][1])
                ln = check_lin(K, modelB, reading)
                if ln.get('aborted'):
                    print(msg + 'lin ABORTED at %d states' % ln['states'])
                elif ln['ok']:
                    print(msg + 'linearizable OK (%d state+hist nodes, %d distinct quiescent histories)' % (
                        ln['states'], ln['histories']))
                else:
                    print(msg + 'NOT LINEARIZABLE: history vals0=%s vals1=%s need0=%s need1=%s' % (
                        [str(v) for v in ln['history'][0]], [str(v) for v in ln['history'][1]],
                        ln['history'][2], ln['history'][3]))
                    for lab, st in ln['trace']:
                        print('    %-30s %s' % (lab, fmt_state(st)))
                sys.stdout.flush()


if __name__ == '__main__':
    main()
