"""Replays both attacks of attacks.py under further readings of the decision procedure.

Not part of the Lean development. Usage: python3 -I readings.py  (from this directory)
Three independent switches on top of the literal reading of km.py:
* retro:  at decision time, every message of a process suspected (by the deciding process) at any
          point, including at the end of round t + 1, is treated as bottom;
* excl:   a child `x k` is removed from the top set T of `x` if the deciding process suspects `k`;
* nonbot: the strict majority at an internal node is taken among the non-bottom cvals of T only.
The t = 2 run (Counterexample.lean) breaks agreement under the literal and `retro` readings, but
not when `excl` or `retro + nonbot` is added; the t = 3 attack breaks agreement under all 8 readings.
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from collections import Counter
from km import Proto, BOT
import attacks


class Var(Proto):
    RETRO = False; EXCL = False; NONBOT = False

    def decide(self, i, ibs):
        self.cache = {}
        n, t, R = self.n, self.t, self.R
        final = self.susp(ibs, R)
        orig = self.recv_msg
        if self.RETRO:
            self.recv_msg = lambda ibs_, r, k: None if k in final else ibs_[r - 1].get(k)
        try:
            def rep(l, k):
                for r in range(3, R + 1):
                    m = self.recv_msg(ibs, r, l)
                    if m is not None and k in m['sus']: return True
                return False
            def erep(l, k, j):
                for r in range(4, R + 1):
                    m = self.recv_msg(ibs, r, l)
                    if m is not None and m['ek'][k] is not None and j in m['ek'][k]: return True
                return False
            def cval(x):
                if len(x) == 2:
                    m = self.recv_msg(ibs, 2, x[1])
                    return None if m is None else m['e2'][x[0]]
                return not erep(x[-1], x[-2], x[-3])
            memo = {}
            def nv(x):
                if x in memo: return memo[x]
                L = len(x)
                if L == R:
                    res = not rep(x[-1], x[-2])
                else:
                    T = [x + (k,) for k in range(n) if k not in x and nv(x + (k,)) is True
                         and not (self.EXCL and k in final)]
                    vals = [cval(y) for y in T]
                    if self.NONBOT: vals = [v for v in vals if v is not None]
                    res = BOT if L == 1 else False
                    if len(T) >= n - t - L and vals:
                        v, cnt = Counter(vals).most_common(1)[0]
                        if 2 * cnt > len(vals): res = v
                    if L >= 2 and res is None: res = False
                memo[x] = res
                return res
            vals = [nv((j,)) for j in range(n)]
            for v, cnt in Counter(v for v in vals if v is not None).items():
                if 2 * cnt > n: return v, vals
            return self.v0, vals
        finally:
            self.recv_msg = orig


if __name__ == '__main__':
    for retro in (False, True):
        for excl in (False, True):
            for nonbot in (False, True):
                name = f"retro={retro} excl={excl} nonbot={nonbot}"
                attacks.Proto = attacks.Retro = type(name, (Var,), dict(RETRO=retro, EXCL=excl, NONBOT=nonbot))
                print('==', name)
                attacks.attack_t2()
                attacks.attack_t3()
