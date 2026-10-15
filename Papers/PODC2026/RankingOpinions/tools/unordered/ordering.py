import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import sys
from itertools import product
from mc2 import check2
# state: (ic, ld, d)
def ordering(k, sym=False):
    def d(p, q):
        ica, lda, da = p; icb, ldb, db = q
        if ica == icb:
            if lda and ldb: lda = 0
            if not lda and ldb and da != db: da = db
            if sym and not ldb and lda and da != db: db = da
        else:
            if da == db and lda and ldb: da = (da + 1) % k
        return (ica, lda, da), (icb, ldb, db)
    return d
def good(c):
    cols = set(s[0] for s in c)
    for col in cols:
        if sum(1 for s in c if s[0]==col and s[1]) != 1: return False
    for s in c:
        for t in c:
            if (s[0]==t[0]) != (s[2]==t[2]): return False
    return True
def inputs(n, k):
    # nondecreasing color sequences with colors used in order (up to symmetry)
    res = []
    for seq in product(range(k), repeat=n):
        if list(seq) != sorted(seq): continue
        used = sorted(set(seq))
        if used != list(range(len(used))): continue
        res.append(seq)
    return res
if __name__ == "__main__":
    for sym in [False, True]:
        for fair in ["ordered", "unordered"]:
            for k in [1,2,3]:
                for n in range(2, 6):
                    for inp in inputs(n, k):
                        init = tuple((c, 1, 0) for c in inp)
                        ok, bad, N, confs, edges = check2(init, ordering(k, sym), n, lambda c: not good(c), fair)
                        if not ok:
                            print("FAIL sym=%s fair=%s k=%d n=%d inp=%s bad=%s N=%d" % (sym, fair, k, n, inp, bad, N))
                            break
                    else: continue
                    break
            print("done sym=%s fair=%s" % (sym, fair))
