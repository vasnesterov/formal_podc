"""SAT checks for Theorem 4.3 (Figure 3 network). Requires python-sat (pip install python-sat).

Usage: python3 -I scenarios.py <dir containing model.py>

1. The 28 scenarios used in the Lean proof (Theorem43.lean) are unsatisfiable already for
   condition (1) alone (every node connected to d has a forwarding path to d).
2. The scenarios the paper's proof uses (the cyclic-ordering scenarios of Lemma 4.2 plus the
   Figure 3 scenario, for each of the 6 cycles) are satisfiable even with loop-freedom:
   the paper's argument needs more scenarios (the misapplied Lemma 4.1).
"""
import sys, itertools
sys.path.insert(0, sys.argv[1])
from model import *

MID = {frozenset({2,3}):6, frozenset({3,4}):7, frozenset({4,5}):8, frozenset({5,2}):9,
       frozenset({2,4}):10, frozenset({3,5}):11}
def mid(a, b): return MID[frozenset({a, b})]
def eid(a, b):
    for k, e in enumerate(EDGES):
        if set(e) == {a, b}: return k
    raise KeyError((a, b))
def F_alive(pairs):
    al = {eid(a, b) for a, b in pairs}
    return frozenset(k for k in range(len(EDGES)) if k not in al)

def only1_clauses(F):
    """condition (1) only; reach is the least fixed point (ranks only along reaching darts)."""
    cl = []
    alive = [k for k in range(len(EDGES)) if k not in F]
    darts = [(k, a, b) for k in alive for (a, b) in [EDGES[k], EDGES[k][::-1]]]
    L = len(darts); idx = {(k, a): i for i, (k, a, b) in enumerate(darts)}
    reach = [pool.new() for _ in darts]
    r = [[pool.new() for t in range(L)] for _ in darts]
    for i in range(L):
        for t in range(L - 1): cl.append([-r[i][t + 1], r[i][t]])
    for i, (k, a, b) in enumerate(darts):
        if b == D: continue
        A = view_of(b, F)
        for o in INC[b]:
            fv = fvar[(b, A, k, o)]
            if o in F: cl.append([-fv, -reach[i]])
            else:
                j = idx[(o, b)]
                cl.append([-fv, -reach[i], reach[j]])
                cl.append([-fv, -reach[i], r[i][0]])
                for t in range(L - 1): cl.append([-fv, -reach[i], -r[j][t], r[i][t + 1]])
                cl.append([-fv, -reach[i], -r[j][L - 1]])
    for v in connected_to_d(F):
        if v == D: continue
        cl.append([reach[idx[(k, v)]] for k in INC[v] if k not in F])
    return cl

spokes = [(1, 2), (1, 3), (1, 4), (1, 5)]
Mw = {2: 6, 3: 7, 4: 8, 5: 9}
cyc = [F_alive(spokes + [(w, Mw[w]), (Mw[w], 0)]) for w in [2, 3, 4, 5]]
fig, aux = [], []
for a, b, c in itertools.permutations([2, 3, 4]):
    X, Y, Z = mid(a, c), mid(b, 5), mid(c, 5)
    fig.append(F_alive(spokes + [(a, X), (X, c), (b, Y), (Y, 0)]))
    aux += [F_alive([(1, a), (a, X), (X, 0)]),
            F_alive([(a, X), (X, c), (c, Z), (Z, 0)]),
            F_alive([(X, c), (c, 1), (1, b), (b, Y), (Y, 0)])]

s = Solver(bootstrap_with=clauses)
for F in cyc + fig + aux:
    for c in only1_clauses(F): s.add_clause(c)
print("Lean proof scenarios (28), condition (1) only: satisfiable =", s.solve())

s = Solver(bootstrap_with=clauses)
for F in cyc + fig:
    for c in scenario_clauses(F): s.add_clause(c)
print("paper's scenarios (10), conditions (1)+(2): satisfiable =", s.solve())
