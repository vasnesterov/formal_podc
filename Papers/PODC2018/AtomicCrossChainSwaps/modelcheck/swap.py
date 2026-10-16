"""Bounded model checker for Herlihy's multi-leader hashkey swap protocol (PODC'18).

Discrete time, Delta = 1. Actions issued at round t land at time t+1 (lock-step for conforming
parties). Adversary (coalition C) is rushing: its actions landing at t+1 may use keys from conforming
calls landing at t+1. All calls (successful or not) are public.
Deadline of key path p: B + len(p) - 1 (inclusive, landing time <= deadline).
variant: 'literal' or 'fixed'.
"""
import itertools, sys
from functools import lru_cache


def lax_path(arcs, p):
    if len(p) == 0:
        return False
    for a, b in zip(p, p[1:]):
        if (a, b) not in arcs:
            return False
    body = p[:-1]
    return len(set(body)) == len(body)


def all_lax_paths(n, arcs, src, dst):
    res = set()

    def go(p):
        if p[-1] == dst:
            res.add(tuple(p))
        if dst in p and (p[-1], dst) in arcs:
            res.add(tuple(p) + (dst,))
        for (a, b) in arcs:
            if a == p[-1] and b not in p:
                go(p + [b])
    go([src])
    return sorted(r for r in res if lax_path(arcs, r))


class Inst:
    def __init__(self, n, arcs, L, C, B, variant, rushing=True):
        self.rushing = rushing
        self.n, self.arcs, self.L, self.C, self.B, self.variant = n, frozenset(arcs), tuple(L), frozenset(C), B, variant
        self.inn = {v: [a for a in arcs if a[1] == v] for v in range(n)}
        self.out = {v: [a for a in arcs if a[0] == v] for v in range(n)}
        self.nl = len(L)
        self.keys = {}  # (v, i) -> list of valid lax paths from v to L[i]
        for v in range(n):
            for i in range(self.nl):
                self.keys[(v, i)] = all_lax_paths(n, self.arcs, v, L[i])
        self.H = B + n + 2

    def dl(self, p):
        return self.B + len(p) - 1

    def derivable(self, pub, i, p):
        # suffix of public
        for (j, q) in pub:
            if j == i and len(q) >= len(p) and q[len(q) - len(p):] == p:
                return True
        if p[0] in self.C:
            if len(p) == 1:
                return p[0] == self.L[i]
            return self.derivable(pub, i, p[1:])
        return False


def conf_actions(I, st, t):
    """st = (con, unl(dict-like frozenset of (a,i,key)), pub, released, fwd, first)"""
    con, unl, pub, released, fwd, first = st
    unlocked = {(a, i) for (a, i, k) in unl}
    pubs, calls = set(), []
    newrel, newfwd = set(released), set(fwd)
    newfirst = dict(first)
    for v in range(I.n):
        if v in I.C:
            continue
        isL = v in I.L
        allin = all(a in con for a in I.inn[v])
        if isL and t == 0:
            pubs |= set(I.out[v])
        if (not isL) and allin and any(a not in con for a in I.out[v]):
            pubs |= set(I.out[v])
        if isL:
            iv = I.L.index(v)
            if v not in released and allin and (I.variant == 'literal' or t + 1 <= I.B):
                newrel.add(v)
                for a in I.inn[v]:
                    calls.append((a, iv, (v,)))
        for i in range(I.nl):
            if I.L[i] == v:
                continue
            # first key observation
            if (v, i) not in first:
                cands = sorted(k for (a, j, k) in unl if j == i and a[0] == v)
                if cands:
                    newfirst[(v, i)] = cands[0]
            if (v, i) not in newfirst:
                continue
            p1 = newfirst[(v, i)]
            key = (v,) + p1
            if I.variant == 'literal':
                if (v, i) not in fwd:
                    newfwd.add((v, i))
                    for a in I.inn[v]:
                        if a in con:
                            calls.append((a, i, key))
            else:
                if v in p1:
                    continue
                if v in I.L and v not in newrel:
                    # leader forwards foreign keys only once released or allin (fixed: forward whenever contract present)
                    pass
                for a in I.inn[v]:
                    if a in con and (a, i) not in unlocked and t + 1 <= I.dl(key):
                        calls.append((a, i, key))
    return pubs, calls, frozenset(newrel), frozenset(newfwd), newfirst


def apply(I, st, t, pubs, calls):
    con, unl, pub, released, fwd, first = st
    con2 = con | frozenset(pubs)
    unlocked = {(a, i) for (a, i, k) in unl}
    unl2 = set(unl)
    pub2 = set(pub)
    for (a, i, k) in calls:
        pub2.add((i, k))
        if (a, i) in unlocked:
            continue
        if a in con and k[0] == a[1] and k[-1] == I.L[i] and lax_path(I.arcs, k) and t + 1 <= I.dl(k):
            unl2.add((a, i, k))
            unlocked.add((a, i))
    return con2, frozenset(unl2), frozenset(pub2)


def adv_options(I, st, t, conf_pubs, conf_calls):
    con, unl, pub, released, fwd, first = st
    pubset = set(pub) | ({(i, k) for (a, i, k) in conf_calls} if I.rushing else set())
    unlocked = {(a, i) for (a, i, k) in unl}
    own = [a for a in I.arcs if a[0] in I.C and a not in con]
    pub_opts = [frozenset(s) for r in range(len(own) + 1) for s in itertools.combinations(own, r)]
    for ps in pub_opts:
        con2 = con | frozenset(conf_pubs) | ps
        slots = []
        for a in sorted(I.arcs):
            if a[1] not in I.C or a not in con:
                continue
            for i in range(I.nl):
                if (a, i) in unlocked:
                    continue
                ks = [k for k in I.keys[(a[1], i)] if t + 1 <= I.dl(k) and I.derivable(pubset, i, k)]
                if ks:
                    slots.append([None] + [(a, i, k) for k in ks])
        for choice in itertools.product(*slots):
            yield ps, [c for c in choice if c is not None]


def outcome(I, st):
    con, unl, pub, released, fwd, first = st
    unlocked = {(a, i) for (a, i, k) in unl}
    trig = {a for a in I.arcs if all((a, i) in unlocked for i in range(I.nl))}
    return trig


def underwater(I, trig, v):
    return any(a in trig for a in I.out[v]) and any(a not in trig for a in I.inn[v])


def search(I, want='underwater'):
    """DFS over adversary choices; return a trace leading to a conforming party Underwater."""
    seen = set()
    init = (frozenset(), frozenset(), frozenset(), frozenset(), frozenset(), {})

    def key(st, t):
        con, unl, pub, rel, fwd, first = st
        return (t, con, unl, pub, rel, fwd, tuple(sorted(first.items())))

    stack = [(init, 0, [])]
    while stack:
        st, t, tr = stack.pop()
        k = key(st, t)
        if k in seen:
            continue
        seen.add(k)
        if t >= I.H:
            trig = outcome(I, st)
            bad = [v for v in range(I.n) if v not in I.C and underwater(I, trig, v)]
            if bad:
                return tr, trig, bad
            continue
        cp, cc, rel2, fwd2, first2 = conf_actions(I, st, t)
        for ps, ac in adv_options(I, st, t, cp, cc):
            con2, unl2, pub2 = apply(I, st, t, set(cp) | ps, cc + ac)
            st2 = (con2, unl2, pub2, rel2, fwd2, first2)
            stack.append((st2, t + 1, tr + [(t, sorted(ps), ac)]))
        if len(seen) > 400_000:
            return 'limit'
    return None


def run_all_conforming(I):
    st = (frozenset(), frozenset(), frozenset(), frozenset(), frozenset(), {})
    last = None
    for t in range(I.H):
        cp, cc, rel2, fwd2, first2 = conf_actions(I, st, t)
        con2, unl2, pub2 = apply(I, st, t, cp, cc)
        st = (con2, unl2, pub2, rel2, fwd2, first2)
        if outcome(I, st) == set(I.arcs) and last is None:
            last = t + 1
    return outcome(I, st), last
