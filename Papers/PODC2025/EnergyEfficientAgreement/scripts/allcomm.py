# For n=5,f=3 check every assignment of 3 committees of size 3: does a disagreement execution exist?
# sem='v1': Algorithm 3 of arXiv v1. sem='ba': prose of the brief announcement (input holders send to C_1..C_T0
# in rounds 1..T0, input-1 players never re-activated).
import sys, itertools
from functools import lru_cache
pc = lambda x: bin(x).count('1')
def subsets(m):
    s = m
    while True:
        yield s
        if s == 0: break
        s = (s-1) & m

def bad_exists(n, f, C, T0, sem):
    full = (1<<n)-1
    for X in range(1, full):
        @lru_cache(maxsize=None)
        def go(r, crashed, Y, T):
            alive = full & ~crashed; used = pc(crashed)
            if r == f+1:
                H = alive & (Y | X)
                return bool(H) and used + pc(H) <= f and n - used - pc(H) >= 2
            Cr = C[r]
            senders = 0
            for p in range(n):
                if alive >> p & 1 and T[p] > 0: senders |= 1 << p
            if r == 1 and sem == 'v1': senders = alive & X
            for K in subsets(alive):
                if pc(K) > f - used: continue
                pool = Cr & alive & ~K
                if senders & ~K: choices = [pool]
                elif senders & K: choices = subsets(pool)
                else: choices = [0]
                for R in choices:
                    Tn = list(T)
                    for p in range(n):
                        if senders >> p & 1 and not (r == 1 and sem == 'v1'): Tn[p] -= 1
                    if r == 1 and sem == 'v1':
                        for p in range(n):
                            if X >> p & 1: Tn[p] = T0
                    Yn = Y
                    for p in range(n):
                        if R >> p & 1 and not (Y >> p & 1):
                            if sem == 'ba' and X >> p & 1: continue
                            Yn |= 1 << p; Tn[p] = T0
                    newc = crashed | K
                    for p in range(n):
                        if newc >> p & 1: Tn[p] = 0
                    if go(r+1, newc, Yn & ~newc, tuple(Tn)): return True
            return False
        T0v = tuple((T0 if (sem == 'ba' and X >> p & 1) else 0) for p in range(n))
        if go(1, 0, 0, T0v): return True
    return False

n, f, s, T0 = 5, 3, 3, 2
sem = sys.argv[1]
trip = [sum(1<<i for i in c) for c in itertools.combinations(range(n), s)]
good = 0; tot = 0
for cs in itertools.product(trip, repeat=f):
    C = [0] + list(cs)
    tot += 1
    if not bad_exists(n, f, C, T0, sem):
        good += 1; print("no counterexample for", [bin(c) for c in cs])
print(sem, "assignments:", tot, "without counterexample:", good)
