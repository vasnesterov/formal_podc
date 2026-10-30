# Explicit-state model checker for MemSnap (Algorithm 2 of Jayanti-Jayanti-Jayanti PODC'24).
# Tracks the paper's meta-configuration P exactly and checks I1 and I2 (literal and fixed).
import sys, itertools
from collections import deque

M = int(sys.argv[1]) if len(sys.argv) > 1 else 1      # components
NU = int(sys.argv[2]) if len(sys.argv) > 2 else 2     # updaters
OPS_PER_U = int(sys.argv[3]) if len(sys.argv) > 3 else 2
CLICKS = int(sys.argv[4]) if len(sys.argv) > 4 else 3
OBS = int(sys.argv[5]) if len(sys.argv) > 5 else 2
VMOD = 3
UOPS = [('write', 1), ('write', 2), ('faa', 1), ('cas', (0, 2)), ('read', None)]

def prim(v, uop):
    k, a = uop
    if k == 'write': return a, ('ok',)
    if k == 'faa': return (v + a) % VMOD, v
    if k == 'read': return v, v
    if k == 'cas': return (a[1], True) if v == a[0] else (v, False)

SIG = NU  # scanner index; updaters 0..NU-1
NP = NU + 1

# local state: (pc, op, xh, k, b, x, a, r, done)
# pc: 'idle','c1','c2','f9','f10','f11','f12','o4','o5','u7','u8'
# op: None | ('click',) | ('obs', i) | ('upd', i, uop)
IDLE = ('idle', None, 0, 1, None, 0, None, None, 0)

def opdelta(state, op):
    val, snap = state
    if op[0] == 'click': return (val, val), 'ack'
    if op[0] == 'obs': return (val, snap), snap[op[1]]
    i, uop = op[1], op[2]
    nv, r = prim(val[i], uop)
    val2 = val[:i] + (nv,) + val[i+1:]
    return (val2, snap), r

def trans(p, seq, locs):
    val, snap, fl = p
    for pi in seq:
        (val, snap), r = opdelta((val, snap), locs[pi][1])
        fl = fl[:pi] + (r,) + fl[pi+1:]
    return (val, snap, fl)

def unlin(p, locs):
    return [pi for pi in range(NU) if locs[pi][0] in ('f9', 'f10', 'f11', 'f12', 'u7', 'u8') and p[2][pi] is None]

def perms_of_subsets(xs):
    for r in range(len(xs) + 1):
        for sub in itertools.combinations(xs, r):
            for perm in itertools.permutations(sub):
                yield perm

def filt(P, pi, r):
    out = set()
    for (v, s, fl) in P:
        if fl[pi] == r:
            out.add((v, s, fl[:pi] + (None,) + fl[pi+1:]))
    return frozenset(out)

def succs(st):
    X, A, B, locs, P = st
    for pi in range(NP):
        l = locs[pi]
        pc, op, xh, k, b, x, a, r, done = l
        def upd(nl, X=X, A=A, B=B, P=P):
            nlocs = locs[:pi] + (nl,) + locs[pi+1:]
            return (X, A, B, nlocs, P)
        if pc == 'idle':
            if pi == SIG:
                clicks, obs = done // 10, done % 10
                if clicks < CLICKS:
                    yield upd(('c1', ('click',), xh, 1, None, 0, None, None, done + 10))
                if obs < OBS:
                    for i in range(M):
                        yield upd(('f9', ('obs', i), X, 1, None, 0, None, None, done + 1))
            else:
                if done < OPS_PER_U:
                    for i in range(M):
                        for u in UOPS:
                            yield upd(('f9', ('upd', i, u), X, 1, None, 0, None, None, done + 1))
        elif pc == 'c1':
            # line 1: X <- X+1, P update
            nlocs = locs[:pi] + (('c2', op, xh, k, b, x, a, r, done),) + locs[pi+1:]
            NPset = set()
            for p in P:
                if p[2][SIG] is not None: continue
                ul = unlin(p, locs)
                for perm in perms_of_subsets(ul):
                    NPset.add(trans(p, list(perm) + [SIG], locs))
            yield (X + 1, A, B, nlocs, frozenset(NPset))
        elif pc == 'c2':
            nlocs = locs[:pi] + (IDLE[:8] + (done,),) + locs[pi+1:]
            yield (X, A, B, nlocs, filt(P, pi, 'ack'))
        elif pc in ('f9', 'f10', 'f11', 'f12'):
            i = op[1]
            cont = 'o4' if op[0] == 'obs' else 'u7'
            if pc == 'f9':
                yield upd((('f10', op, xh, k, B[i], x, a, r, done)))
            elif pc == 'f10':
                if b[1] == X:
                    yield upd((cont, op, xh, k, b, X, a, r, done))
                else:
                    yield upd(('f11', op, xh, k, b, X, a, r, done))
            elif pc == 'f11':
                yield upd(('f12', op, xh, k, b, x, A[i], r, done))
            else:
                if B[i] == b:
                    nB = B[:i] + ((a, x),) + B[i+1:]
                    nlocs = locs[:pi] + ((cont, op, xh, k, b, x, a, r, done),) + locs[pi+1:]
                    yield (X, A, nB, nlocs, P)
                else:
                    if k == 1:
                        yield upd(('f9', op, xh, 2, b, x, a, r, done))
                    else:
                        yield upd((cont, op, xh, k, b, x, a, r, done))
        elif pc == 'o4':
            i = op[1]
            rr = B[i][0]
            nlocs = locs[:pi] + (('o5', op, xh, k, b, x, a, rr, done),) + locs[pi+1:]
            nlocs_t = locs[:pi] + (l[:1] + (op,) + l[2:],) + locs[pi+1:]
            NPset = set()
            for p in P:
                if p[2][pi] is None:
                    NPset.add(trans(p, [pi], locs))
            yield (X, A, B, nlocs, frozenset(NPset))
        elif pc == 'o5':
            nlocs = locs[:pi] + (IDLE[:8] + (done,),) + locs[pi+1:]
            yield (X, A, B, nlocs, filt(P, pi, r))
        elif pc == 'u7':
            i, u = op[1], op[2]
            nv, rr = prim(A[i], u)
            nA = A[:i] + (nv,) + A[i+1:]
            nlocs = locs[:pi] + (('u8', op, xh, k, b, x, a, rr, done),) + locs[pi+1:]
            NPset = set(P)
            for p in P:
                if p[2][pi] is None:
                    NPset.add(trans(p, [pi], locs))
            yield (X, nA, B, nlocs, frozenset(NPset))
        elif pc == 'u8':
            nlocs = locs[:pi] + (IDLE[:8] + (done,),) + locs[pi+1:]
            yield (X, A, B, nlocs, filt(P, pi, r))

def pstar(st):
    X, A, B, locs, P = st
    fl = []
    for pi in range(NP):
        pc = locs[pi][0]
        if pc == 'c2': fl.append('ack')
        elif pc in ('o5', 'u8'): fl.append(locs[pi][7])
        else: fl.append(None)
    return (A, tuple(b[0] for b in B), tuple(fl))

def Qset(st, fixed):
    X, A, B, locs, P = st
    ps = pstar(st)
    ul = [pi for pi in range(NU) if locs[pi][0] in ('f9', 'f10', 'f11', 'f12', 'u7', 'u8') and ps[2][pi] is None and locs[pi][2] < X]
    out = set()
    for perm in perms_of_subsets(ul):
        q = trans(ps, list(perm), locs)
        comps = {locs[pi][1][1] for pi in perm}
        choices = []
        for j in range(M):
            cj = set()
            if B[j][1] == X and j not in comps: cj.add(B[j][0])
            if B[j][1] != X: cj.add(q[0][j])
            if B[j][1] != X and j not in comps:
                for mu in range(NP):
                    lm = locs[mu]
                    if lm[0] == 'f12' and lm[1][1] == j and lm[4] == B[j] and (not fixed or lm[5] == X):
                        cj.add(lm[6])
            choices.append(sorted(cj))
        for snap in itertools.product(*choices):
            out.add((q[0], tuple(snap), q[2]))
    return out

def I1(st):
    X, A, B, locs, P = st
    errs = []
    for j in range(M):
        if not X >= B[j][1]: errs.append(1)
    for mu in range(NP):
        pc, op, xh, k, b, x, a, r, done = locs[mu]
        if mu == SIG and pc in ('f9', 'f10', 'f11', 'f12', 'o4', 'o5') and X != xh: errs.append(2)
        if mu < NU and pc in ('f9', 'f10', 'f11', 'f12', 'u7', 'u8') and not X >= xh: errs.append(3)
        if pc in ('f11', 'f12') and not (X >= x > b[1]): errs.append(4)
        if pc in ('f10', 'f11', 'f12'):
            i = op[1]
            if B[i] != b and not B[i][1] > b[1]: errs.append(5)
            if B[i] != b and k == 2 and not B[i][1] >= xh: errs.append(7)
        if (pc in ('f10', 'f11', 'f12') and op is not None and B[op[1]] != b and k == 1) or (pc == 'f9' and k == 2):
            i = op[1]
            if not (B[i][1] >= xh or all(not (locs[m2][0] in ('f11', 'f12') and locs[m2][1][1] == i and B[i] == locs[m2][4]) or locs[m2][5] >= xh for m2 in range(NP))):
                errs.append(6)
        if mu == SIG and pc == 'o4' and B[op[1]][1] != X: errs.append(8)
        if mu < NU and pc == 'u7' and not B[op[1]][1] >= xh: errs.append(9)
    return errs

def main():
    p0 = (tuple([0] * M), tuple([0] * M), tuple([None] * NP))
    init = (0, tuple([0] * M), tuple([(0, 0)] * M), tuple([IDLE] * NP), frozenset([p0]))
    seen = {init: None}
    dq = deque([init])
    bad_lit = None; bad_fix = None; n = 0
    while dq:
        st = dq.popleft(); n += 1
        e = I1(st)
        if e:
            print('I1 violated', e, st); return
        if not st[4]:
            print('P empty', st); return
        Qf = Qset(st, True)
        if not Qf or not Qf <= st[4]:
            if bad_fix is None:
                bad_fix = st
                print('FIXED I2 violated', st, Qf - st[4])
        if bad_lit is None:
            Ql = Qset(st, False)
            if not Ql <= st[4]:
                bad_lit = st
                # trace
                tr = []; s = st
                while s is not None:
                    tr.append(s); s = seen[s]
                print('LITERAL I2 violated after', len(tr) - 1, 'steps; extra', Ql - st[4])
                for s in reversed(tr):
                    print('  X=%d A=%s B=%s locs=%s |P|=%d' % (s[0], s[1], s[2], [l[:8] for l in s[3]], len(s[4])))
        for s2 in succs(st):
            if s2 not in seen:
                seen[s2] = st; dq.append(s2)
    print('states', n, 'literal ok' if bad_lit is None else 'literal FAILS', 'fixed ok' if bad_fix is None else 'fixed FAILS')

main()
