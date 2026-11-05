"""Replays the disagreement attacks on the Kowalski-Mostefaoui protocol (simulator km.py).

Not part of the Lean development. Usage: python3 -I attacks.py  (from this directory)
* t = 2, n = 7: the run formalized in Counterexample.lean (values 0 = false, 1 = true, v0 = 1),
  under the literal reading (`Proto`) and under the "retroactive" reading (`Retro`: at decision time,
  every message of a process suspected at any point is discarded).
* t = 3, n = 10: a different attack (b2 equivocates its round-3 suspicion set, b3 its round-4 echo).
"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from km import Proto, run


class Retro(Proto):
    def decide(self, i, ibs):
        self.cache = {}
        final = self.susp(ibs, self.R)
        orig = self.recv_msg
        self.recv_msg = lambda ibs_, r, k: None if k in final else ibs_[r - 1].get(k)
        try:
            return Proto.decide(self, i, ibs)
        finally:
            self.recv_msg = orig


def attack_t2():
    n, t = 7, 2
    inputs = [0, 0, 0, 1, 1, None, None]
    A = (0, 1, 2)

    def adv(r, b, i, ibs):
        if r == 1:
            if b == 5:
                return {'v1': 0 if i in A else 1}
            return {'v1': 1}
        if r == 2:
            arr = [inputs[j] for j in range(n)]
            arr[6] = 1
            arr[5] = 0 if i in A else 1
            return {'e2': tuple(arr)}
        return {'sus': frozenset(), 'e3': tuple(ibs[i][1][j]['e2'] for j in range(n))}
    for P in (Proto, Retro):
        res = run(P(n, t, v0=1), inputs, {5, 6}, adv)
        print('t=2', P.__name__, {i: d for i, (d, _) in res.items()})


def attack_t3():
    n, t = 10, 3
    B1, B2, B3 = 7, 8, 9
    byz = {B1, B2, B3}
    inputs = [0, 0, 0, 0, 0, 1, 1, None, None, None]
    Cp = {0, 1, 2, 3}

    def adv(r, b, i, ibs):
        if r == 1:
            if b == B1:
                return {'v1': 0 if i in Cp or i in byz else 1}
            return {'v1': 1}
        if r == 2:
            arr = [inputs[j] for j in range(n)]
            arr[B1] = 0; arr[B2] = 1; arr[B3] = 1
            return {'e2': tuple(arr)}
        if r == 3:
            sus = frozenset({B1}) if (b == B2 and i in (4, 5, 6)) else frozenset()
            e3 = tuple(ibs[i][1][j]['e2'] if ibs[i][1].get(j) else None for j in range(n))
            return {'sus': sus, 'e3': e3}
        ek = [ibs[i][2][j]['sus'] if ibs[i][2].get(j) else None for j in range(n)]
        if b == B3:
            ek[B2] = frozenset() if i == 0 else frozenset({B1})
        return {'sus': frozenset(), 'ek': tuple(ek)}
    res = run(Proto(n, t, v0=1), inputs, byz, adv)
    print('t=3 Proto', {i: d for i, (d, _) in res.items()})


if __name__ == '__main__':
    attack_t2()
    attack_t3()
