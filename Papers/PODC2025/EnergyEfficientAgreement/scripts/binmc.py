# Model checker for Algorithm 3 (binary consensus) of Mirault-Robinson arXiv 2506.12282v1.
import sys, math
from functools import lru_cache

def ceil_sqrt(n):
    s = math.isqrt(n)
    return s if s*s == n else s+1

def join_committees(n, a, b):
    C = [0]*(a+2)  # bitmasks, index 1..a
    for i in range(1, a*b+1):
        c = i % n
        d = -(-i // b)
        C[d] |= 1 << c
    return C

def T0_of(n, f):
    T = 0
    while T*T*n < (f+1)**2: T += 1
    return T

def subsets(m):
    s = m
    while True:
        yield s
        if s == 0: break
        s = (s-1) & m

def check(n, f, verbose=True, singles=False):
    s = ceil_sqrt(n); T0 = T0_of(n, f)
    C = join_committees(n, f, s)
    full = (1<<n)-1
    pc = lambda x: bin(x).count('1')
    sys.setrecursionlimit(10000)
    for X in ([1<<p for p in range(n)] if singles else range(1, full)):
        @lru_cache(maxsize=None)
        def go(r, crashed, Y, T):
            # returns a witness list or None
            alive = full & ~crashed
            used = pc(crashed)
            if r == f+1:
                H = alive & (Y | X)
                if H and used + pc(H) <= f and n - used - pc(H) >= 2:
                    return [('final', r, H)]
                return None
            Cr = C[r] if r <= f else 0
            if r == 1:
                senders = alive & X
            else:
                senders = 0
                for p in range(n):
                    if alive >> p & 1 and T[p] > 0: senders |= 1 << p
            budget = f - used
            for K in subsets(alive):
                if pc(K) > budget: continue
                rec_pool = Cr & alive & ~K
                if senders & ~K:
                    choices = [rec_pool]
                elif senders & K:
                    choices = list(subsets(rec_pool))
                else:
                    choices = [0]
                for R in choices:
                    Tn = list(T)
                    if r == 1:
                        for p in range(n):
                            if X >> p & 1: Tn[p] = T0
                    else:
                        for p in range(n):
                            if senders >> p & 1: Tn[p] -= 1
                    Yn = Y
                    for p in range(n):
                        if (R >> p & 1) and not (Y >> p & 1):
                            Yn |= 1 << p; Tn[p] = T0
                    newc = crashed | K
                    # crashed players' state irrelevant: normalize
                    for p in range(n):
                        if newc >> p & 1: Tn[p] = 0
                    Yn &= ~newc
                    w = go(r+1, newc, Yn, tuple(Tn))
                    if w is not None:
                        return [(r, 'crash', K, 'recv', R)] + w
            return None
        w = go(1, 0, 0, tuple([0]*n))
        if w is not None:
            if verbose:
                print(f"n={n} f={f} s={s} T0={T0} committees={[bin(c) for c in C[1:f+1]]}")
                print("  X =", [X>>p&1 for p in range(n)])
                for step in w: print("  ", step)
            return (X, w)
        go.cache_clear()
    return None

if __name__ == '__main__':
    singles = len(sys.argv) > 3
    for n in range(int(sys.argv[1]), int(sys.argv[2])+1):
        for f in range(1, n-1):
            res = check(n, f, singles=singles)
            print(f"n={n} f={f}: {'COUNTEREXAMPLE' if res else 'ok'}", flush=True)
