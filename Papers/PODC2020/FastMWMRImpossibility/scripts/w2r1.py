"""Explicit-state model / random tester for the W2R1 MWMR register algorithm
(Algorithms 1 & 2 of Huang, Huang, Wei, PODC 2020, arXiv 2001.07855).

Model: asynchronous client-server message passing.  Each request message
(client -> server) is delivered at an arbitrary time (or never: models crashes
and arbitrary delays); the server processes it atomically and replies at once.
A client finishes a round as soon as it has S-t replies of the *current*
round; equivalently (and this is what we implement) at any moment when at
least S-t replies of the current round are available, the client may choose any
S-t of them and proceed.  Replies not chosen are dropped (late replies).

Values are pairs (ts, wid), ordered lexicographically; (0, 0) is the initial
value (0, bottom); writers have ids 1..W.

Interpretation knobs (see README in this folder):
  srv  = 'L'  : literal code: read handler does update(val, rj) for val in valQueue only
         'D'  : additionally adds rj to updated of the server's current value val_i
         'D2' : additionally adds rj to updated of every value in the valuevector
  wq   = 'A'  : writer's query (read, maxTS) does not change server state
         'B'  : writer's query is handled like a reader's read with an empty valQueue
                (i.e. marks per `srv` with the writer id)
  vq   = 'all': reader valQueue <- valQueue U {all values in rcvMsg}   (literal)
         'ret': reader valQueue <- valQueue U {returned value}
         'max': reader valQueue <- valQueue U {max value in rcvMsg}
"""
from itertools import combinations
import random

INIT = (0, 0)


class Config:
    def __init__(self, S, t, W, R, wops, rops, srv='D2', wq='A', vq='all'):
        self.S, self.t, self.W, self.R = S, t, W, R
        self.wops, self.rops = wops, rops  # ops per writer / per reader
        self.srv, self.wq, self.vq = srv, wq, vq
        self.bound_ok = R < S / t - 2  # paper's condition; outside it impossibility applies
        # client ids: writers 1..W, readers W+1..W+R
        self.writers = list(range(1, W + 1))
        self.readers = list(range(W + 1, W + R + 1))
        self.clients = self.writers + self.readers


# ---------------------------------------------------------------- server ---
# server state: dict value -> frozenset(updated)

def srv_update(vv, val, c):
    cur = max(vv)
    if val > cur:
        vv[val] = frozenset([c])
    else:
        vv[val] = vv.get(val, frozenset()) | {c}


def srv_mark(cfg, vv, c):
    if cfg.srv == 'D':
        cur = max(vv)
        vv[cur] = vv[cur] | {c}
    elif cfg.srv == 'D2':
        for v in list(vv):
            vv[v] = vv[v] | {c}


def srv_handle(cfg, vv, kind, c, payload):
    """Process one request atomically; return reply payload.  Mutates vv."""
    if kind == 'write':
        srv_update(vv, payload, c)
        return 'ack'
    if kind == 'query':  # writer first round
        if cfg.wq == 'B':
            srv_mark(cfg, vv, c)
        return max(vv)[0]
    if kind == 'read':
        for val in sorted(payload):
            srv_update(vv, val, c)
        srv_mark(cfg, vv, c)
        return tuple(sorted(vv.items()))  # snapshot of the valuevector
    raise ValueError(kind)


# ---------------------------------------------------------------- reader ---

def admissible(cfg, v, msgs, a):
    need = cfg.S - a * cfg.t
    having = [dict(m)[v] for m in msgs if v in dict(m)]
    if len(having) < need:
        return False
    for mu in combinations(having, need):
        inter = frozenset.intersection(*mu)
        if len(inter) >= a:
            return True
    return False


def adm_degree(cfg, v, msgs):
    for a in range(1, cfg.R + 2):
        if admissible(cfg, v, msgs, a):
            return a
    return None


def reader_decide(cfg, msgs):
    """Lines 23-31 of Algorithm 1.  msgs: list of valuevector snapshots.
    Returns (returned value, maxV, info)."""
    cur = [dict(m) for m in msgs]
    maxV0 = max(v for m in cur for v in m)
    while True:
        maxV = max(v for m in cur for v in m)
        frozen = [tuple(sorted(m.items())) for m in cur]
        if adm_degree(cfg, maxV, frozen) is not None:
            return maxV, maxV0
        for m in cur:
            m.pop(maxV, None)


def adm_set(cfg, msgs):
    vals = set(v for m in msgs for v in dict(m))
    return frozenset(v for v in vals if adm_degree(cfg, v, msgs) is not None)


# -------------------------------------------------------------- system -----

class Sys:
    """Mutable system state + history."""

    def __init__(self, cfg):
        self.cfg = cfg
        self.servers = [{INIT: frozenset()} for _ in range(cfg.S)]
        self.pending = []  # requests: (server, client, opno, rnd, kind, payload)
        self.avail = {c: {} for c in cfg.clients}  # server -> reply payload of current round
        self.cl = {}
        for c in cfg.clients:
            self.cl[c] = dict(opno=0, phase='idle', rnd=0, val=None,
                              vq=frozenset([INIT]) if c in cfg.readers else None)
        for c in cfg.clients:
            if self.nops(c) == 0:
                self.cl[c]['phase'] = 'done'
        self.time = 0
        self.late = 0
        self.ctr = [dict() for _ in range(cfg.S)]  # per server: last read counter per reader
        self.hist = []  # ops: dict(c, kind, val, inv, resp, extra)
        self.curop = {}
        self.trace = []

    def nops(self, c):
        cfg = self.cfg
        if c in cfg.writers:
            return cfg.wops if isinstance(cfg.wops, int) else cfg.wops[c - 1]
        return cfg.rops if isinstance(cfg.rops, int) else cfg.rops[c - cfg.W - 1]

    def enabled(self):
        ev = []
        for c in self.cfg.clients:
            st = self.cl[c]
            if st['phase'] == 'idle' and st['opno'] < self.nops(c):
                ev.append(('inv', c))
            if st['phase'] not in ('idle', 'done') and len(self.avail[c]) >= self.cfg.S - self.cfg.t:
                ev.append(('step', c))
        K = getattr(self.cfg, 'late_bound', None)
        for i, m in enumerate(self.pending):
            if K is not None and self.late >= K and self.is_late(m):
                continue
            ev.append(('deliver', i))
        return ev

    def _send_all(self, c, kind, payload):
        st = self.cl[c]
        st['rnd'] += 1
        self.avail[c] = {}
        for s in range(self.cfg.S):
            self.pending.append((s, c, st['opno'], st['rnd'], kind, payload))

    def invoke(self, c):
        st = self.cl[c]
        self.time += 1
        if c in self.cfg.writers:
            op = dict(c=c, kind='W', val=None, inv=self.time, resp=None)
            st['phase'] = 'q'
            if getattr(self.cfg, 'qabs', False) and self.cfg.wq == 'A':
                # abstract query round: remember, per server, every ts it had since invocation
                st['rnd'] += 1
                self.avail[c] = {s: frozenset([max(self.servers[s])[0]]) for s in range(self.cfg.S)}
            else:
                self._send_all(c, 'query', None)
        else:
            op = dict(c=c, kind='R', val=None, inv=self.time, resp=None)
            st['phase'] = 'r'
            op['vq_old'] = st['vq']
            self._send_all(c, 'read', st['vq'])
        self.hist.append(op)
        self.curop[c] = op
        self.trace.append(f"t{self.time}: {cname(self.cfg, c)} invokes {op['kind']}#{st['opno']}"
                          + (f" sending valQueue={fmtset(st['vq'])}" if op['kind'] == 'R' else " (query round)"))

    def is_late(self, m):
        st = self.cl[m[1]]
        return not (st['opno'] == m[2] and st['rnd'] == m[3] and st['phase'] not in ('idle', 'done'))

    def deliver(self, i):
        if self.is_late(self.pending[i]):
            self.late += 1
        s, c, opno, rnd, kind, payload = self.pending.pop(i)
        if getattr(self.cfg, 'ctr', False) and kind == 'read':
            # DGLV-style read counters: a server ignores a stale read request
            if opno < self.ctr[s].get(c, -1):
                self.trace.append(f"   s{s} ignores stale read request {cname(self.cfg, c)}#{opno}")
                return
            self.ctr[s][c] = opno
        rep = srv_handle(self.cfg, self.servers[s], kind, c, payload)
        st = self.cl[c]
        self.trace.append(f"   s{s} handles ({kind}{'' if payload is None else ' '+fmtpay(payload)}) from "
                          f"{cname(self.cfg, c)}#{opno}.{rnd} -> reply {fmtrep(rep)}; s{s} now {fmtvv(self.servers[s])}")
        if st['opno'] == opno and st['rnd'] == rnd and st['phase'] not in ('idle', 'done'):
            self.avail[c][s] = rep
        if getattr(self.cfg, 'qabs', False):
            ts = max(self.servers[s])[0]
            for c2 in self.cfg.writers:
                if self.cl[c2]['phase'] == 'q':
                    self.avail[c2][s] = self.avail[c2][s] | {ts}

    def qstep(self, c, mts):
        """Abstract query step: writer c obtained maximum timestamp mts."""
        st = self.cl[c]
        op = self.curop[c]
        val = (mts + 1, c)
        op['val'] = val
        st['phase'] = 'w'
        self.trace.append(f"   {cname(self.cfg, c)} query round done (abstract): maxTS={mts}, now writes {fmtv(val)}")
        self._send_all(c, 'write', val)

    def qstep_choices(self, c):
        """maxTS values obtainable from S-t servers, each reporting some ts it had
        during the query round."""
        seen = self.avail[c]
        out = []
        for m in sorted(set().union(*seen.values())):
            for s0 in seen:
                if m in seen[s0]:
                    others = sum(1 for s in seen if s != s0 and min(seen[s]) <= m)
                    if others >= self.cfg.S - self.cfg.t - 1:
                        out.append(m)
                        break
        return out

    def step(self, c, subset):
        """Client c proceeds using replies from servers in `subset` (size S-t)."""
        st = self.cl[c]
        op = self.curop[c]
        reps = [self.avail[c][s] for s in subset]
        tag = f"   {cname(self.cfg, c)} uses replies from {{{','.join('s%d' % s for s in subset)}}}"
        if st['phase'] == 'q':
            mts = max(reps)
            val = (mts + 1, c)
            op['val'] = val
            st['phase'] = 'w'
            self.trace.append(tag + f": maxTS={mts}, now writes {fmtv(val)}")
            if self.cfg.wq == 'A':  # late query requests have no effect: drop them
                self.pending = [m for m in self.pending if not (m[1] == c and m[4] == 'query')]
            self._send_all(c, 'write', val)
            return
        self.time += 1
        if st['phase'] == 'w':
            op['resp'] = self.time
            self.trace.append(tag + f"; t{self.time}: W {fmtv(op['val'])} returns OK")
        else:  # read
            ret, maxV = reader_decide(self.cfg, reps)
            op['val'] = ret
            op['maxV'] = maxV
            op['msgs'] = reps
            op['servers'] = tuple(subset)
            op['adm'] = adm_set(self.cfg, reps)
            op['resp'] = self.time
            allv = set(v for m in reps for v in dict(m))
            if self.cfg.vq == 'all':
                st['vq'] = st['vq'] | allv
            elif self.cfg.vq == 'ret':
                st['vq'] = st['vq'] | {ret}
            else:
                st['vq'] = st['vq'] | {maxV}
            self.trace.append(tag + f"; t{self.time}: R returns {fmtv(ret)} (maxV={fmtv(maxV)}, "
                              f"admissible={fmtset(op['adm'])})")
        st['phase'] = 'idle'
        st['opno'] += 1
        self.avail[c] = {}
        if st['opno'] >= self.nops(c):
            st['phase'] = 'done'

    def all_done(self):
        return all(self.cl[c]['phase'] == 'done' for c in self.cfg.clients)

    # canonical key up to server permutation (servers are symmetric)
    def sym_key(self):
        per = []
        for s in range(self.cfg.S):
            pend = tuple(sorted(m[1:] for m in self.pending if m[0] == s))
            av = tuple((c, self.avail[c].get(s, '-')) for c in self.cfg.clients)
            per.append((tuple(sorted(self.servers[s].items())), pend, av, tuple(sorted(self.ctr[s].items()))))
        cl = tuple((c, st['opno'], st['phase'], st['rnd'], st['vq']) for c, st in sorted(self.cl.items()))
        # history up to irrelevant interleavings: per op (identified by client and
        # per-client index) its value, completion, and the ops completed before
        # its invocation (this determines the real-time partial order)
        ids = {}
        cnt = {}
        for op in self.hist:
            cnt[op['c']] = cnt.get(op['c'], 0) + 1
            ids[id(op)] = (op['c'], cnt[op['c']])
        h = []
        for op in self.hist:
            before = frozenset(ids[id(o2)] for o2 in self.hist
                               if o2['resp'] is not None and o2['resp'] < op['inv'])
            h.append((ids[id(op)], op['val'], op['resp'] is not None, before))
        late = self.late if getattr(self.cfg, 'late_bound', None) is not None else 0
        return (tuple(sorted(per)), cl, tuple(sorted(h)), late)

    # canonical key for memoisation (DFS)
    def key(self):
        srv = tuple(tuple(sorted(vv.items())) for vv in self.servers)
        pend = tuple(sorted(self.pending))
        cl = tuple((c, st['opno'], st['phase'], st['rnd'], st['vq'],
                    tuple(sorted(self.avail[c].items()))) for c, st in sorted(self.cl.items()))
        # history abstraction: per op: (client, kind, val, done, set of ops completed before inv)
        h = []
        for i, op in enumerate(self.hist):
            before = frozenset(j for j, o2 in enumerate(self.hist)
                               if o2['resp'] is not None and o2['resp'] < op['inv'])
            h.append((op['c'], op['kind'], op['val'], op['resp'] is not None, before))
        return (srv, pend, cl, tuple(h))


# ---------------------------------------------------- linearizability -----

def linearizable(hist):
    """hist: list of complete ops (kind, val, inv, resp); distinct write values.
    Returns True iff an atomic-register linearization exists."""
    ops = [o for o in hist if o['resp'] is not None or o['kind'] == 'W']
    n = len(ops)
    INF = float('inf')
    inv = [o['inv'] for o in ops]
    resp = [o['resp'] if o['resp'] is not None else INF for o in ops]
    pred = [frozenset(j for j in range(n) if resp[j] < inv[i]) for i in range(n)]
    complete = frozenset(i for i in range(n) if resp[i] != INF)
    memo = set()

    def go(done, cur):
        if complete <= done:
            return True
        k = (done, cur)
        if k in memo:
            return False
        memo.add(k)
        for i in range(n):
            if i in done or not pred[i] <= done:
                continue
            o = ops[i]
            if o['kind'] == 'W':
                if o['val'] is None:
                    continue  # pending write that never chose a value
                if go(done | {i}, o['val']):
                    return True
            else:
                if o['val'] == cur and go(done | {i}, cur):
                    return True
        return False

    return go(frozenset(), INIT)


# ---------------------------------------------------- lemma checks --------

def lemma_checks(sysm):
    """Return list of strings describing failures of paper lemmas on a history."""
    out = []
    H = sysm.hist
    reads = [o for o in H if o['kind'] == 'R' and o['resp'] is not None]
    writes = [o for o in H if o['kind'] == 'W' and o['val'] is not None]
    for r in reads:
        # Lemma 2: return ts in {maxTS, maxTS-1}
        if r['val'][0] not in (r['maxV'][0], r['maxV'][0] - 1):
            out.append(f"Lemma2: read t{r['inv']}-{r['resp']} returns {fmtv(r['val'])}, maxV={fmtv(r['maxV'])}")
        # Lemma 6: maxV >= (k,wi) => rd does not precede wr_{k,i}
        for w in writes:
            if r['maxV'] >= w['val'] and r['resp'] < w['inv']:
                out.append(f"Lemma6: read t{r['inv']}-{r['resp']} maxV={fmtv(r['maxV'])} precedes write {fmtv(w['val'])}")
            # Corollary 1: maxV=(l,wj) > init => all writes with ts k<l complete before rd completes
            if r['maxV'] > INIT and w['val'][0] < r['maxV'][0] and (w['resp'] is None or w['resp'] > r['resp']):
                out.append(f"Cor1: read t{r['inv']}-{r['resp']} maxV={fmtv(r['maxV'])} but write {fmtv(w['val'])} not complete")
    # Lemma 8: rd1 precedes rd2 => Sad(rd1) subset Sad(rd2)
    for r1 in reads:
        for r2 in reads:
            if r1['resp'] < r2['inv'] and not r1['adm'] <= r2['adm']:
                out.append(f"Lemma8: Sad(read t{r1['inv']}-{r1['resp']})={fmtset(r1['adm'])} not in "
                           f"Sad(read t{r2['inv']}-{r2['resp']})={fmtset(r2['adm'])}")
    # Lemma 5 / MWA2 , MWA4 direct
    for r in reads:
        for w in writes:
            if w['resp'] is not None and w['resp'] < r['inv'] and r['val'] < w['val']:
                out.append(f"MWA2: read t{r['inv']}-{r['resp']} returns {fmtv(r['val'])} after write {fmtv(w['val'])} completed")
        for r2 in reads:
            if r['resp'] < r2['inv'] and r2['val'] < r['val']:
                out.append(f"MWA4: read returns {fmtv(r2['val'])} after earlier read returned {fmtv(r['val'])}")
    return out


# ---------------------------------------------------- formatting ----------

def cname(cfg, c):
    return f"w{c}" if c in cfg.writers else f"r{c - cfg.W}"


def fmtv(v):
    return "(0,_)" if v == INIT else f"({v[0]},w{v[1]})"


def fmtset(s):
    return "{" + ",".join(fmtv(v) for v in sorted(s)) + "}"


def fmtpay(p):
    if isinstance(p, frozenset):
        return fmtset(p)
    if isinstance(p, tuple) and len(p) == 2 and isinstance(p[0], int):
        return fmtv(p)
    return str(p)


def fmtvv(vv):
    items = vv.items() if isinstance(vv, dict) else vv
    return "[" + " ".join(f"{fmtv(v)}:{{{','.join(str(x) for x in sorted(u))}}}" for v, u in sorted(items)) + "]"


def fmtrep(r):
    if isinstance(r, tuple):
        return fmtvv(r)
    return str(r)


# ---------------------------------------------------- random runs ---------

def random_run(cfg, rng, p_deliver=0.6, slow_bias=True):
    sysm = Sys(cfg)
    # per server "slowness" so that some servers lag behind (models crashes/delays)
    slow = [rng.random() for _ in range(cfg.S)] if slow_bias else [0.5] * cfg.S
    steps = 0
    while not sysm.all_done():
        steps += 1
        if steps > 10000:
            raise RuntimeError("no progress")
        ev = sysm.enabled()
        dels = [e for e in ev if e[0] == 'deliver']
        others = [e for e in ev if e[0] != 'deliver']
        if dels and (not others or rng.random() < p_deliver):
            ws = [0.05 + (1 - slow[sysm.pending[e[1]][0]]) ** 3 for e in dels]
            e = rng.choices(dels, ws)[0]
            sysm.deliver(e[1])
        elif others:
            e = rng.choice(others)
            if e[0] == 'inv':
                sysm.invoke(e[1])
            else:
                c = e[1]
                srvs = sorted(sysm.avail[c])
                subset = sorted(rng.sample(srvs, cfg.S - cfg.t))
                sysm.step(c, subset)
        else:
            raise RuntimeError("deadlock")
    return sysm


def run_random(cfg, n, seed=0, stop_first=True, **kw):
    rng = random.Random(seed)
    bad = []
    for i in range(n):
        sysm = random_run(cfg, rng, **kw)
        if not linearizable(sysm.hist):
            bad.append(sysm)
            if stop_first:
                break
    return bad, i + 1


# ---------------------------------------------------- exhaustive DFS -----

def clone(sysm):
    n = Sys.__new__(Sys)
    n.cfg = sysm.cfg
    n.servers = [dict(vv) for vv in sysm.servers]
    n.pending = list(sysm.pending)
    n.avail = {c: dict(a) for c, a in sysm.avail.items()}
    n.cl = {c: dict(st) for c, st in sysm.cl.items()}
    n.time = sysm.time
    n.late = sysm.late
    n.ctr = [dict(d) for d in sysm.ctr]
    n.hist = [dict(o) for o in sysm.hist]
    n.curop = {}
    for o in n.hist:
        if o['resp'] is None:
            n.curop[o['c']] = o
    n.trace = sysm.trace  # shared (only extended along a path; rebuilt on report)
    return n


def successors(sysm):
    """Partial-order reduction.  Independence: deliver(m@s from c) commutes with
    deliver(m'@s') for s != s', with every inv, and with step(c') for c' != c
    (late replies are dropped in either order).  Fix the order
    inv/step < deliver, deliveries ordered by message tuple.  Every execution is
    equivalent (same history, same server states at every visible event) to its
    lexicographically least representative, in which no two adjacent events are
    independent and out of order; we only generate such sequences."""
    cfg = sysm.cfg
    last = getattr(sysm, 'last', None)
    for e in sysm.enabled():
        if e[0] == 'inv':
            if last is None:
                yield ('inv', e[1], None)
        elif e[0] == 'deliver':
            m = sysm.pending[e[1]]
            if last is not None and m[0] != last[0] and m < last:
                continue
            yield ('deliver', e[1], None)
        else:
            c = e[1]
            if last is not None and c != last[1]:
                continue
            if getattr(cfg, 'qabs', False) and sysm.cl[c]['phase'] == 'q':
                for m in sysm.qstep_choices(c):
                    yield ('qstep', c, m)
                continue
            for sub in combinations(sorted(sysm.avail[c]), cfg.S - cfg.t):
                yield ('step', c, sub)


def apply(sysm, ev):
    kind, x, sub = ev
    sysm.last = sysm.pending[x] if kind == 'deliver' else None
    if kind == 'inv':
        sysm.invoke(x)
    elif kind == 'deliver':
        sysm.deliver(x)
    elif kind == 'qstep':
        sysm.qstep(x, sub)
    else:
        sysm.step(x, list(sub))


def dfs(cfg, max_states=2_000_000, check_lemmas=False, por=False, time_limit=None):
    import time as _t
    t0 = _t.time()
    """Exhaustive search with memoisation on abstract states (lazy successor
    generation).  Returns (violation path or None, #states, complete?, lemma_fail)."""
    root = Sys(cfg)
    root.trace = []
    visited = {hash(root.key())}
    lemma_fail = {}
    path = []
    stack = [(root, successors(root))]
    while stack:
        sysm, it = stack[-1]
        ev = next(it, None)
        if ev is None:
            stack.pop()
            if path:
                path.pop()
            continue
        n = clone(sysm)
        n.trace = []
        apply(n, ev)
        if not por:
            n.last = None
        k = hash((n.key(), n.last)) if por else hash(n.sym_key())
        if k in visited:
            continue
        visited.add(k)
        if len(visited) > max_states or (time_limit and len(visited) % 1000 == 0
                                          and _t.time() - t0 > time_limit):
            return None, len(visited), False, lemma_fail
        if n.all_done():
            if not linearizable(n.hist):
                return path + [ev], len(visited), True, lemma_fail
            if check_lemmas:
                for f in lemma_checks(n):
                    lemma_fail.setdefault(f.split(':')[0], path + [ev])
            continue
        path.append(ev)
        stack.append((n, successors(n)))
    return None, len(visited), True, lemma_fail


def replay(cfg, path):
    s = Sys(cfg)
    for ev in path:
        apply(s, ev)
    return s


def random_run2(cfg, rng):
    """'Swarm' random scheduler: per-run random knobs, abstract writer queries
    (cfg.qabs must be True), random achievable maxTS (biased low), random
    eagerness of client steps and per-server delivery speeds."""
    sysm = Sys(cfg)
    p_del = rng.uniform(0.2, 0.95)
    speed = [rng.random() ** rng.choice([1, 3, 6]) for _ in range(cfg.S)]
    eager = {c: rng.uniform(0.1, 1.0) for c in cfg.clients}
    low_bias = rng.random()
    steps = 0
    while not sysm.all_done():
        steps += 1
        if steps > 20000:
            raise RuntimeError("no progress")
        ev = sysm.enabled()
        dels = [e for e in ev if e[0] == 'deliver']
        invs = [e for e in ev if e[0] == 'inv']
        stps = [e for e in ev if e[0] == 'step']
        # steps of clients
        r = rng.random()
        if stps and (not dels or r < 0.5):
            c = rng.choice(stps)[1]
            if rng.random() < eager[c] or not dels:
                if sysm.cl[c]['phase'] == 'q':
                    ch = sysm.qstep_choices(c)
                    m = ch[0] if rng.random() < low_bias else rng.choice(ch)
                    sysm.qstep(c, m)
                else:
                    subset = sorted(rng.sample(sorted(sysm.avail[c]), cfg.S - cfg.t))
                    sysm.step(c, subset)
                continue
        if invs and (not dels or rng.random() > p_del):
            sysm.invoke(rng.choice(invs)[1])
            continue
        if dels:
            ws = [0.01 + speed[sysm.pending[e[1]][0]] for e in dels]
            sysm.deliver(rng.choices(dels, ws)[0][1])
            continue
        if invs:
            sysm.invoke(rng.choice(invs)[1])
    return sysm


def random_run3(cfg, rng):
    """Event-driven asynchronous simulation with heavy-tailed random message
    delays (requests and replies) and random client think times.  A client uses
    exactly the first S-t replies of its current round (as in the pseudo-code).
    Uses real query messages (cfg.qabs must be False)."""
    import heapq
    sysm = Sys(cfg)
    alpha = rng.uniform(0.6, 2.0)
    p_inf = rng.uniform(0.0, 0.15)
    srv_scale = [rng.uniform(0.1, 3.0) for _ in range(cfg.S)]

    def delay(s):
        if rng.random() < p_inf:
            return None
        return srv_scale[s] * rng.paretovariate(alpha)

    ev = []  # (time, seq, kind, data)
    seq = [0]

    def push(tm, kind, data):
        seq[0] += 1
        heapq.heappush(ev, (tm, seq[0], kind, data))

    now = 0.0
    for c in cfg.clients:
        push(rng.uniform(0, 3), 'inv', c)
    arrived = {c: [] for c in cfg.clients}  # replies arrived in current round (server ids, in order)
    nsent = 0
    while ev:
        now, _, kind, data = heapq.heappop(ev)
        if kind == 'inv':
            c = data
            st = sysm.cl[c]
            if st['phase'] != 'idle':
                continue
            before = len(sysm.pending)
            sysm.invoke(c)
            arrived[c] = []
            for m in sysm.pending[before:]:
                d = delay(m[0])
                if d is not None:
                    push(now + d, 'req', m)
        elif kind == 'req':
            m = data
            if m not in sysm.pending:
                continue  # pruned late query request (no effect)
            i = sysm.pending.index(m)
            st = sysm.cl[m[1]]
            current = (st['opno'] == m[2] and st['rnd'] == m[3] and st['phase'] not in ('idle', 'done'))
            sysm.deliver(i)  # server processes; reply recorded in avail if current
            # model the reply's own delay: the client "receives" it later
            d = delay(m[0])
            if d is None:
                d = 1e9  # lost reply (crash after processing)
            push(now + d, 'rep', m)
        elif kind == 'rep':
            m = data
            c = m[1]
            st = sysm.cl[c]
            if not (st['opno'] == m[2] and st['rnd'] == m[3] and st['phase'] not in ('idle', 'done')):
                continue
            if m[0] in sysm.avail[c] and m[0] not in arrived[c]:
                arrived[c].append(m[0])
            if len(arrived[c]) == cfg.S - cfg.t:
                was = st['phase']
                before = len(sysm.pending)
                sysm.step(c, sorted(arrived[c]))
                arrived[c] = []
                for m2 in sysm.pending[before:]:
                    d = delay(m2[0])
                    if d is not None:
                        push(now + d, 'req', m2)
                if st['phase'] == 'idle':
                    push(now + rng.expovariate(1.0) * rng.choice([0.1, 1, 5]), 'inv', c)
    if not sysm.all_done():
        return None  # too many messages lost: some client blocked (more than t 'crashes')
    return sysm
