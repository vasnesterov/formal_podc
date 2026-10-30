# Explicit adversary family for Algorithm 3 (arXiv v1) with n = s^2, f = n - 2: a relay chain that crashes
# one player per round, choosing receivers in C_1 whenever possible, so that C_1 = C_{1+ks} eventually
# consists of crashed players and gives a crash-free ("free") round. Simulates Algorithm 3 exactly.
import sys
def committees(n, a, b):
    C = [set() for _ in range(a + 2)]
    for i in range(1, a * b + 1): C[-(-i // b)].add(i % n)
    return C
def run(s):
    n = s * s; f = n - 2
    T0 = 0
    while T0 * T0 * n < (f + 1) ** 2: T0 += 1
    C = committees(n, f, s)
    X = min(C[1]); crashed = set(); Y = set(); T = {X: T0}
    holder = X; log = []
    for r in range(1, f + 1):
        fresh = sorted(q for q in C[r] if q not in crashed and q not in Y and q != holder)
        if not fresh:
            # free round: the holder relays to a committee of crashed players (and maybe itself)
            assert T.get(holder, 0) > 0 or r == 1
            T[holder] = T.get(holder, 0) - 1; log.append((r, 'free')); continue
        assert r == 1 or T.get(holder, 0) > 0, 'holder no longer relays'
        pref = [q for q in fresh if q in C[1]]
        x = (pref or fresh)[0]
        crashed.add(holder); Y.add(x); T[x] = T0; log.append((r, 'crash', holder, '->', x))
        holder = x
    nfree = sum(1 for e in log if e[1] == 'free')
    crashed.add(holder)  # crashes in round f+1, reaching one correct player only
    correct = [p for p in range(n) if p not in crashed]
    ok = len(crashed) <= f and len(correct) >= 2
    return n, f, len(crashed), len(correct), nfree, ok
for s in range(3, int(sys.argv[1]) + 1):
    print(run(s))
