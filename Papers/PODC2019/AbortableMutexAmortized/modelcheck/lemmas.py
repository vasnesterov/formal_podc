import sys, itertools
N = sys.argv[1]
sys.argv = ["mc.py", N]
exec(open("mc.py").read().split('if __name__')[0])
R = bfs()
F = {1:3, 3:2, 4:None, 5:7, 6:2, 7:1, 9:6, 10:5, 11:4}
def f(s, r):
    pc = s[0][r]
    if pc == 4: return 8 if s[5][r] else 9
    return F[pc]
def delta(s, p):
    Q, a0 = computeQ(s)
    i = Q.index(p) + 1
    m = min(j for j in range(1, i+1) if s[0][Q[j-1]] != 1)
    digs = [3]*(m-1) + [f(s, Q[m-1])] + [0]*(i-m)
    val = int("".join(map(str, digs)))
    qm = Q[m-1]
    if s[0][qm] == 4 and not s[5][qm]:
        psi = frozenset(r for r in range(n) if s[0][r] in (8, 11) and s[3][r] == G(qm))
    else:
        psi = frozenset([qm])
    return val, psi
bad = 0
for s in R:
    for p in range(n):
        if s[0][p] not in (3,4,5,6,7): continue
        d, psi = delta(s, p)
        assert d >= 1 and ((d == 1) == (s[0][p] == 7)), (s, p, d)
        if s[0][p] == 7: continue
        assert psi, ("empty psi", s, p)
        for (pi, ab), t in succs(s):
            if pi == p and ab: continue
            d2, psi2 = delta(t, p)
            if pi in psi:
                ok = d2 < d
            else:
                ok = d2 < d or (d2 == d and psi2 == psi)
            if not ok:
                bad += 1
                if bad < 5: print("L44 fail", s, p, (pi, ab), d, d2, psi, psi2)
print("Lemma 4.4 failures:", bad)

# amortized costs
def phi_dsm(s):
    pc, my, pr, v, nd, go, tl = s
    return sum((1 if go[p] else 0) + (1 if pc[p] == 6 else 0) + (1 if nd[my[p]] == A(pr[p]) else 0) for p in range(n))
def line_of(s, p, ab):
    return 9 if ab else s[0][p]
def cost_dsm(s, p, ab):
    l = line_of(s, p, ab)
    if l in (4, 5): return 0
    if l in (8, 11): return 0 if s[3][p] == G(p) else 1
    return 1
bound_dsm = {1:1,2:1,3:1,7:1,9:1,8:2,10:2,11:2,4:0,5:0,6:0}
mx = {}
for s in R:
    for (p, ab), t in succs(s):
        l = line_of(s, p, ab)
        a = cost_dsm(s, p, ab) + phi_dsm(t) - phi_dsm(s)
        mx[l] = max(mx.get(l, -99), a)
print("DSM max amortized per line:", sorted(mx.items()))
# CC: cache bits c[p] = go_p in p's cache
def phi_cc(s, c, w=3):
    pc, my, pr, v, nd, go, tl = s
    return sum(w*(1 if go[p] else 0) + (1 if pc[p] == 6 else 0) + (1 if nd[my[p]] == A(pr[p]) else 0) + (0 if c[p] else 1) for p in range(n))
mx = {}
for s in R:
    for (p, ab), t in succs(s):
        l = line_of(s, p, ab)
        for c in itertools.product([False, True], repeat=n):
            c2 = list(c); cost = 1
            if l == 4:
                cost = 0 if c[p] else 1; c2[p] = True
            elif l == 5:
                c2[p] = False
            elif l in (8, 11):
                c2[gof(s[3][p])] = False
            a = cost + phi_cc(t, c2) - phi_cc(s, c)
            mx[l] = max(mx.get(l, -99), a)
print("CC max amortized per line:", sorted(mx.items()))
