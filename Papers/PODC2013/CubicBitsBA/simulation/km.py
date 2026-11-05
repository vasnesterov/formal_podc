# Simulator of the Kowalski-Mostefaoui protocol (PODC 2013), same reading as Protocol.lean. Not part of the Lean development.
import itertools, random, sys
from collections import Counter

BOT = None

class Proto:
    def __init__(self, n, t, v0=0, retro=False):
        self.n, self.t, self.R, self.v0, self.retro = n, t, t+1, v0, retro

    # state of process i: list of full inboxes (dict j -> msg or None), index r-1 for round r
    def main_of(self, r, msg):
        if msg is None: return None
        if r == 1: return msg['v1']
        if r == 2: return msg['e2']
        return msg['sus']

    def echo_of(self, r, msg):
        # echo part of a round-r message (echoing round r-1 mains)
        if msg is None: return None
        if r == 2: return msg['e2']
        if r == 3: return msg['e3']
        return msg['ek']

    def susp(self, ibs, r):
        """suspected set after round r (cumulative); ibs = list of inboxes rounds 1..>=r"""
        n, t = self.n, self.t
        S = set()
        for rr in range(2, r+1):
            new = set()
            for j in range(n):
                if j in S: continue
                m = self.recv_main(ibs, rr-1, j, S_before=None)
                cnt = 0
                if m is not None:
                    for k in range(n):
                        mk = self.recv_msg(ibs, rr, k)
                        if mk is None: continue
                        e = self.echo_of(rr, mk)
                        if e[j] == m: cnt += 1
                if m is None or cnt < n - t: new.add(j)
            S |= new
        return S

    def recv_msg(self, ibs, r, k):
        # message received from k in round r, bottom if suspected before round r
        if k in self._susp_cache(ibs, r-1): return None
        return ibs[r-1].get(k)

    def recv_main(self, ibs, r, j, S_before=None):
        return self.main_of(r, self.recv_msg(ibs, r, j))

    def _susp_cache(self, ibs, r):
        key = (id(ibs), r)
        if key not in self.cache:
            self.cache[key] = set() if r < 2 else self.susp(ibs, r)
        return self.cache[key]

    def out(self, i, x, ibs):
        """message i sends in round len(ibs)+1"""
        self.cache = {}
        r = len(ibs) + 1
        n = self.n
        if r == 1: return {'v1': x}
        if r == 2: return {'e2': tuple(self.recv_main(ibs, 1, j) for j in range(n))}
        sus = frozenset(self._susp_cache(ibs, r-1))
        if r == 3:
            return {'sus': sus, 'e3': tuple(self.recv_main(ibs, 2, j) for j in range(n))}
        return {'sus': sus, 'ek': tuple(self.recv_main(ibs, r-1, j) for j in range(n))}

    def decide(self, i, ibs):
        self.cache = {}
        n, t, R = self.n, self.t, self.R
        def rep(rmax, l, k):  # l reported suspecting k in some round 3..rmax
            for r in range(3, rmax+1):
                m = self.recv_msg(ibs, r, l)
                if m is not None and k in m['sus']: return True
            return False
        def erep(l, k, j):  # l reported (echo) by round R that k reported suspecting j
            for r in range(4, R+1):
                m = self.recv_msg(ibs, r, l)
                if m is not None and m['ek'][k] is not None and j in m['ek'][k]: return True
            return False
        def cval(x):  # x has length >= 2
            if len(x) == 2:
                j, k = x
                m = self.recv_msg(ibs, 2, k)
                return None if m is None else m['e2'][j]
            j, k, l = x[-3], x[-2], x[-1]
            return not erep(l, k, j)
        def leafval(x):
            k, l = x[-2], x[-1]
            return not rep(R, l, k)
        memo = {}
        def nv(x):
            if x in memo: return memo[x]
            L = len(x)
            if L == R: res = leafval(x)
            else:
                T = [x + (k,) for k in range(n) if k not in x and nv(x + (k,)) is True]
                if len(T) >= n - t - L:
                    c = Counter(cval(y) for y in T)
                    v, cnt = c.most_common(1)[0]
                    res = v if 2*cnt > len(T) else (BOT if L == 1 else False)
                else:
                    res = BOT if L == 1 else False
                if L >= 2 and res is None: res = False
            memo[x] = res
            return res
        vals = [nv((j,)) for j in range(n)]
        c = Counter(v for v in vals if v is not None)
        for v, cnt in c.items():
            if 2*cnt > n: return v, vals
        return self.v0, vals

def run(proto, inputs, byz, adv):
    """adv(r, b, i, views) -> message from Byzantine b to i in round r (views: correct inboxes so far)"""
    n = proto.n
    ibs = {i: [] for i in range(n)}
    for r in range(1, proto.R+1):
        outs = {j: proto.out(j, inputs[j], ibs[j]) for j in range(n) if j not in byz}
        new = {}
        for i in range(n):
            new[i] = {j: (outs[j] if j not in byz else adv(r, j, i, ibs)) for j in range(n)}
        for i in range(n): ibs[i].append(new[i])
    return {i: proto.decide(i, ibs[i]) for i in range(n) if i not in byz}
