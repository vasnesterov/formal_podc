# Explicit-state model checker for content-oblivious oriented rings.
# A process is a generator: yields ('send', port) or ('recv', ports); receives the port read.
# Its return value is its output.  Node v: port 1 -> node v+1 port 0 ; port 0 -> node v-1 port 1.
import sys
from collections import deque

class Proc:
    def __init__(self, factory):
        self.factory = factory
        self.cache = {}
    def replay(self, hist):
        r = self.cache.get(hist)
        if r is not None:
            return r
        g = self.factory()
        sent = [0, 0]
        i = 0
        val = None
        try:
            op = g.send(None)
            while True:
                if op[0] == 'send':
                    sent[op[1]] += op[2] if len(op) > 2 else 1
                    op = g.send(None)
                elif op[0] == 'recv':
                    if i == len(hist):
                        r = ('wait', tuple(sent), frozenset(op[1]))
                        break
                    p = hist[i]
                    if p not in op[1]:
                        raise RuntimeError('bad history')
                    i += 1
                    op = g.send(p)
                else:
                    raise RuntimeError(op)
        except StopIteration as e:
            if i != len(hist):
                raise RuntimeError('history too long')
            r = ('done', tuple(sent), e.value)
        self.cache[hist] = r
        return r

def explore(procs, max_states=2_000_000, check_final=None, quiet=False):
    n = len(procs)
    init = tuple(() for _ in range(n))
    seen = {init}
    q = deque([init])
    finals = []
    maxsent = 0
    while q:
        c = q.popleft()
        info = [procs[v].replay(c[v]) for v in range(n)]
        tot = sum(i[1][0] + i[1][1] for i in info)
        maxsent = max(maxsent, tot)
        moves = []
        for v in range(n):
            st = info[v]
            if st[0] != 'wait':
                continue
            rc = [c[v].count(0), c[v].count(1)]
            # in transit to port 0 of v: sent by v-1 on port 1
            avail0 = info[(v - 1) % n][1][1] - rc[0]
            avail1 = info[(v + 1) % n][1][0] - rc[1]
            assert avail0 >= 0 and avail1 >= 0
            if 0 in st[2] and avail0 > 0:
                moves.append((v, 0))
            if 1 in st[2] and avail1 > 0:
                moves.append((v, 1))
        if not moves:
            finals.append((c, info))
            if check_final:
                check_final(c, info)
        for v, p in moves:
            c2 = c[:v] + (c[v] + (p,),) + c[v + 1:]
            if c2 not in seen:
                seen.add(c2)
                q.append(c2)
                if len(seen) > max_states:
                    raise RuntimeError('too many states')
    return seen, finals, maxsent

def quiescent(c, info):
    n = len(c)
    for v in range(n):
        if info[(v - 1) % n][1][1] != c[v].count(0): return False
        if info[(v + 1) % n][1][0] != c[v].count(1): return False
    return True

def random_run(procs, rng, bias=None, max_steps=10**6):
    n = len(procs)
    c = [() for _ in range(n)]
    tot_max = 0
    for _ in range(max_steps):
        info = [procs[v].replay(tuple(c[v])) for v in range(n)]
        tot_max = max(tot_max, sum(i[1][0] + i[1][1] for i in info))
        moves = []
        for v in range(n):
            st = info[v]
            if st[0] != 'wait':
                continue
            rc = [c[v].count(0), c[v].count(1)]
            avail0 = info[(v - 1) % n][1][1] - rc[0]
            avail1 = info[(v + 1) % n][1][0] - rc[1]
            if 0 in st[2] and avail0 > 0: moves.append((v, 0))
            if 1 in st[2] and avail1 > 0: moves.append((v, 1))
        if not moves:
            return tuple(c), info, tot_max
        if bias is not None:
            w = [bias[v][p] for v, p in moves]
            v, p = rng.choices(moves, weights=w)[0]
        else:
            v, p = rng.choice(moves)
        c[v] = c[v] + (p,)
    raise RuntimeError('too long')
