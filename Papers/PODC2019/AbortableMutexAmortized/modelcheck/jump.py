import sys
sys.argv = ["mc.py", "2"]
exec(open("mc.py").read().split('if __name__')[0])
def succs(s):
    pc = s[0]
    for p in range(n):
        yield (p, False), step(s, p)
        if pc[p] in (4,5,6):
            yield (p, True), (setv(pc, p, 9),) + s[1:]
R = bfs()
src = open("lemmas.py").read()
exec(src.split("R = bfs()")[1].split("bad = 0")[0])
bad = 0
for s in R:
    for p in range(n):
        if s[0][p] not in (3,4,5,6): continue
        d, psi = delta(s, p)
        for (pi, ab), t in succs(s):
            if pi == p and ab: continue
            d2, psi2 = delta(t, p)
            ok = d2 < d if pi in psi else (d2 < d or (d2 == d and psi2 == psi))
            if not ok:
                bad += 1
                if bad < 3: print("fail", s, p, (pi, ab), d, d2)
print("jump-model L44 failures", bad)
