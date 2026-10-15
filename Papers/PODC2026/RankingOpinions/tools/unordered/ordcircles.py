import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from itertools import product
from mc2 import check2
from protos import W, exch
U, I, CL, CLW = 'U', 'I', 'CL', 'CLW'
# state: (ic, ld, os, i, j, out)
def ordcircles(k, skip_after_reinit=True, sym=False, pend5=False):
    def half(a, b):
        # steps (1)-(4) from the point of view of initiator a; returns (a, b, skip)
        ica, lda, osa, ia, ja, outa = a
        icb, ldb, osb, ib, jb, outb = b
        # (1)
        if ica == icb and lda and ldb: lda = 0
        if ica == icb and ldb and not lda and ia != ib and osa != CL: osa = CLW
        if ica != icb and lda and ldb and ia == ib and osb == U: osa = I
        skip = False
        # (2)
        if osa == CL or osb == CL:
            if osa == CL and ica == icb and ldb:
                ia, ja, osa, outa = ib, ib, U, ica
            skip = True
        a = (ica, lda, osa, ia, ja, outa); b = (icb, ldb, osb, ib, jb, outb)
        return a, b, skip
    def d(p, q):
        a, b, skip = half(p, q)
        if sym:
            b, a, skip2 = half(b, a)
            skip = skip or skip2
        if skip and skip_after_reinit:
            return a, b
        ica, lda, osa, ia, ja, outa = a
        icb, ldb, osb, ib, jb, outb = b
        if osa == CL or osb == CL:
            return a, b
        # (3)
        if osa in (I, CLW) and ia != ja and jb == ia:
            ja, jb = jb, ja
        # (4)
        if osa in (I, CLW) and ia == ja:
            if osa == I:
                ia = ja = (ia + 1) % k; osa = U; outa = ica
            else:
                osa = CL
        if sym:
            if osb in (I, CLW) and ib != jb and ja == ib and osa != CL:
                ja, jb = jb, ja
            if osb in (I, CLW) and ib == jb and osa != CL:
                if osb == I:
                    ib = jb = (ib + 1) % k; osb = U; outb = icb
                else:
                    osb = CL
        if (osa == CL or osb == CL) and not pend5:
            return (ica, lda, osa, ia, ja, outa), (icb, ldb, osb, ib, jb, outb)
        # (5) Circles with out := ic of diagonal agent
        e, f, _ = exch(k, (ia, ja), (ib, jb))
        da, db = e[0] == e[1], f[0] == f[1]
        if da and not db: outa = outb = ica
        elif db and not da: outa = outb = icb
        return (ica, lda, osa, e[0], e[1], outa), (icb, ldb, osb, f[0], f[1], outb)
    return d
def inputs(n, k):
    res = []
    for seq in product(range(k), repeat=n):
        if list(seq) != sorted(seq): continue
        used = sorted(set(seq))
        if used != list(range(len(used))): continue
        res.append(seq)
    return res
def majority(inp):
    cnt = {}
    for c in inp: cnt[c] = cnt.get(c, 0) + 1
    m = max(cnt.values()); w = [c for c in cnt if cnt[c] == m]
    return w[0] if len(w) == 1 else None
STRONG = os.environ.get('STRONG') == '1'
def run(ks, ns, fair, **kw):
    for k in ks:
        for n in ns:
            for inp in inputs(n, k):
                mu = majority(inp)
                init = tuple((c, 1, U, 0, 0, c) for c in inp)
                def bad(c):
                    if mu is not None and any(s[5] != mu for s in c): return True
                    if STRONG:
                        if any(s[2] != U for s in c): return True
                        if any((s[0]==t[0]) != (s[3]==t[3]) for s in c for t in c): return True
                        if any(sum(1 for t in c if t[0]==s[0] and t[1]) != 1 for s in c): return True
                    return False
                ok, b, N, confs, edges = check2(init, ordcircles(k, **kw), n, bad, fair)
                print(k, n, inp, ok, N, b if not ok else "", flush=True)
if __name__ == "__main__":
    fair = sys.argv[1]
    kw = eval(sys.argv[2]) if len(sys.argv) > 2 else {}
    ks = eval(sys.argv[3]) if len(sys.argv) > 3 else [2,3]
    ns = eval(sys.argv[4]) if len(sys.argv) > 4 else [2,3,4]
    run(ks, ns, fair, **kw)
