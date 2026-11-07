"""Simulator of the asynchronous unidirectional ring with mobile agents and tokens
(Shibata et al., Uniform deployment of mobile agents in asynchronous rings).

Model: nodes 0..n-1, agent moves v -> v+1.  Each node v has an incoming FIFO queue q[v]
and a set p[v] of staying agents.  Initially agent i is in q[home_i] (incoming buffer).
A step activates one agent: if it is staying at v, or at the head of q[v], it performs one
atomic action at v: receive all messages, compute, broadcast to the other agents staying at v,
release a token, and either stay or move (append to q[v+1]).  Otherwise the step is a no-op.

Agent programs are generators: `obs = yield decision`.
"""
import random
from collections import deque


class Obs:
    __slots__ = ("msgs", "tokens", "others")

    def __init__(self, msgs, tokens, others):
        self.msgs = msgs
        self.tokens = tokens
        self.others = others  # number of other agents staying at the node


class Dec:
    __slots__ = ("release", "msg", "move", "status")

    def __init__(self, release=False, msg=None, move=False, status="run"):
        self.release = release
        self.msg = msg
        self.move = move
        self.status = status  # "run", "halt", "susp"


class Sim:
    def __init__(self, n, homes, prog, rng=None):
        self.n = n
        self.k = len(homes)
        assert len(set(homes)) == self.k
        self.q = [deque() for _ in range(n)]
        self.p = [[] for _ in range(n)]
        self.tok = [0] * n
        self.mail = [[] for _ in range(self.k)]
        self.pos = list(homes)
        self.transit = [True] * self.k
        self.status = ["run"] * self.k
        self.moves = [0] * self.k
        self.gens = []
        for i, h in enumerate(homes):
            self.q[h].append(i)
            g = prog(i)
            next(g)
            self.gens.append(g)
        self.steps = 0

    def enabled(self, a):
        if self.status[a] == "halt":
            return False
        v = self.pos[a]
        if self.transit[a]:
            return self.q[v][0] == a
        # staying: suspended agents only do something if they have mail
        if self.status[a] == "susp" and not self.mail[a]:
            return False
        return True

    def step(self, a):
        if not self.enabled(a):
            return False
        self.steps += 1
        v = self.pos[a]
        if self.transit[a]:
            self.q[v].popleft()
            self.transit[a] = False
        else:
            self.p[v].remove(a)
        msgs = self.mail[a]
        self.mail[a] = []
        obs = Obs(msgs, self.tok[v], len(self.p[v]))
        d = self.gens[a].send(obs)
        if d.msg is not None:
            for b in self.p[v]:
                self.mail[b].append(d.msg)
        if d.release:
            self.tok[v] += 1
        self.status[a] = d.status
        if d.move:
            assert d.status == "run"
            nv = (v + 1) % self.n
            self.pos[a] = nv
            self.transit[a] = True
            self.q[nv].append(a)
            self.moves[a] += 1
        else:
            self.p[v].append(a)
        return True

    def quiescent(self):
        return not any(self.enabled(a) for a in range(self.k))

    def run(self, sched="random", rng=None, limit=10 ** 6, weights=None):
        rng = rng or random.Random()
        ks = list(range(self.k))
        while self.steps < limit:
            en = [a for a in ks if self.enabled(a)]
            if not en:
                return True
            if weights is None:
                a = rng.choice(en)
            else:
                a = rng.choices(en, [weights[b] for b in en])[0]
            self.step(a)
        return False

    def uniform(self):
        n, k = self.n, self.k
        if any(self.transit) or any(self.mail):
            return False, "transit/mail"
        ps = sorted(self.pos)
        if len(set(ps)) != k:
            return False, "collision %s" % ps
        lo, hi = n // k, -(-n // k)
        for i in range(k):
            d = (ps[(i + 1) % k] - ps[i]) % n
            if d not in (lo, hi):
                return False, "gap %d in %s" % (d, ps)
        return True, ps


# ---------- sequence helpers ----------

def shift(D, x):
    return D[x:] + D[:x]


def rank_of(D, kp):
    """rank = min{x | shift(D,x) = Dmin}, Dmin = lexicographic min over shifts 0..kp-1."""
    sh = [shift(D, x) for x in range(kp)]
    m = min(sh)
    return sh.index(m)


def min_period(D):
    k = len(D)
    for p in range(1, k + 1):
        if k % p == 0 and D == shift(D, p % k):
            return p
    return k


def offset(x, N, p):
    """position of the x-th target after a base, segment length N with p targets (Sec. 3.1.1)."""
    return x * (N // p) + min(x, N % p)
