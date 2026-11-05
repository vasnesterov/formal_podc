import sys, random
N = sys.argv[1]; steps = int(sys.argv[2]); seed = int(sys.argv[3])
sys.argv = ["mc.py", N]
src = open("lemmas.py").read()
exec(open("mc.py").read().split('if __name__')[0])
# pull definitions from lemmas.py without running its bfs
defs = src.split("R = bfs()")[1].split("bad = 0")[0]
exec(defs)
exec(src.split("# amortized costs")[1].split("mx = {}")[0])
random.seed(seed)
bad = 0
for run in range(steps // 2000):
    s = init
    for _ in range(2000):
        e = checkI(s, True)
        if e: print("VIOL", e, s); sys.exit()
        moves = list(succs(s))
        # bias: busy-waiters on go false rarely chosen
        (p, ab), t = random.choice(moves)
        for q in range(n):
            if s[0][q] in (3,4,5,6):
                d, psi = delta(s, q)
                if q == p and ab: continue
                d2, psi2 = delta(t, q)
                ok = d2 < d if p in psi else (d2 < d or (d2 == d and psi2 == psi))
                if not ok:
                    bad += 1; print("L44", s, q, (p, ab), d, d2, psi, psi2)
        s = t
print("done, L44 failures", bad)
