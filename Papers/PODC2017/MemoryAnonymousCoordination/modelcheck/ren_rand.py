"""Random testing of Fig. 3 (renaming) with adversarial-ish random schedules.
Fixed random permutation per process; random choices at lines 9/15; random scheduling with
bursts (to make solo runs and stale writes likely). Checks uniqueness and adaptivity."""
import sys, random
sys.path.insert(0, '.')
N = int(sys.argv[1]); RUNS = int(sys.argv[2]); SEED = int(sys.argv[3])
M = 2 * N - 1
rng = random.Random(SEED)
EMPTY = (0, 0, 0, frozenset())

def run_once():
    regs = [EMPTY] * M
    k = rng.randint(1, N)
    ids = list(range(1, k + 1))
    perms = {i: rng.sample(range(M), M) for i in ids}
    st = {i: dict(pc='S') for i in ids}
    outs = {}
    started = set()
    steps = 0
    while len(outs) < k and steps < 20000:
        steps += 1
        live = [i for i in ids if i not in outs]
        i = rng.choice(live)
        burst = rng.choice([1, 1, 1, 2, 5, 30])
        for _ in range(burst):
            if i in outs: break
            s = st[i]
            started.add(i)
            if s['pc'] == 'S':
                s.update(pc='R', pref=i, rnd=1, hist=frozenset(), view=[None]*M, j=0)
            elif s['pc'] == 'R':
                s['view'][s['j']] = regs[perms[i][s['j']]]
                s['j'] += 1
                if s['j'] == M:
                    view = s['view']
                    ret = None
                    for e in view:
                        for (a, v) in e[3]:
                            if a == i: ret = v
                    if ret is not None:
                        outs[i] = ret; check(outs, started); continue
                    mt = max(e[2] for e in view)
                    if mt > s['rnd']:
                        cand = [e for e in view if e[2] == mt]
                        e = rng.choice(cand)
                        s['pref'], s['hist'], s['rnd'] = e[1], e[3], e[2]
                    cnt = {}
                    for e in view:
                        if e[2] == s['rnd'] and e[1] != 0:
                            cnt[e[1]] = cnt.get(e[1], 0) + 1
                    for v, c in cnt.items():
                        if c >= N: s['pref'] = v
                    tup = (i, s['pref'], s['rnd'], s['hist'])
                    ks = [kk for kk in range(M) if view[kk] != tup] or list(range(M))
                    s['wk'] = rng.choice(ks); s['tup'] = tup; s['pc'] = 'W'
            elif s['pc'] == 'W':
                regs[perms[i][s['wk']]] = s['tup']
                if all(e == s['tup'] for e in s['view']):
                    if s['pref'] == i:
                        outs[i] = s['rnd']; check(outs, started); continue
                    s['hist'] = s['hist'] | {(s['pref'], s['rnd'])}
                    s['rnd'] += 1
                    if s['rnd'] == N:
                        outs[i] = N; check(outs, started); continue
                    s['pref'] = i
                s['pc'] = 'R'; s['view'] = [None]*M; s['j'] = 0
    return steps

def check(outs, started):
    vals = list(outs.values())
    if len(set(vals)) != len(vals) or any(not (1 <= v <= len(started)) for v in vals):
        print('VIOLATION', outs, len(started)); sys.exit(1)

for r in range(RUNS):
    run_once()
print('ok', RUNS)
