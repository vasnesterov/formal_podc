import itertools, sys
def est(D, i):
    k = len(D)
    w = [D[(i + j) % k] for j in range(4 * k)]
    for q in range(1, k + 1):
        if all(w[x] == w[x + q] == w[x + 2*q] == w[x + 3*q] for x in range(q)):
            return q
def primitive(D):
    k = len(D)
    return all(D != D[p:] + D[:p] for p in range(1, k) if k % p == 0)
alph = int(sys.argv[1]); K = int(sys.argv[2])
for k in range(1, K + 1):
    cnt = 0; worst = None
    for D in itertools.product(range(1, alph + 1), repeat=k):
        D = list(D)
        if not primitive(D): continue
        es = [est(D, i) for i in range(k)]
        if k not in es:
            print("COUNTEREXAMPLE Lemma 4", D, es); sys.exit()
        for i, e in enumerate(es):
            if e < k and 2 * sum(D[(i + j) % k] for j in range(e)) > sum(D):
                print("COUNTEREXAMPLE Lemma 3", D, i, e); sys.exit()
            if e < k and 3 * e >= k: print("3e>=k", D, i, e)
        cnt += 1
    print(k, cnt, "ok")
