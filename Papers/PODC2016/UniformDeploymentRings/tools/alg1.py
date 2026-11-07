from sim import *

def alg1(k):
    def prog(i):
        obs = yield
        D = []
        dis = 0
        obs = yield Dec(release=True, move=True)
        while True:
            dis += 1
            if obs.tokens > 0:
                D.append(dis); dis = 0
                if len(D) == k:
                    break
            obs = yield Dec(move=True)
        p = min_period(D)
        N = sum(D[:p])
        r = rank_of(D, k)
        disBase = sum(D[:r])
        m = disBase + offset(r, N, p)
        while m > 0:
            m -= 1
            if m == 0 and False:
                pass
            obs = yield Dec(move=True)
        yield Dec(status="halt")
    return prog
