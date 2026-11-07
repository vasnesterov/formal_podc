from sim import *

LOG = []
REJ = []

def check(D, kp, nodes, msg, cyclic):
    nl, kl, nodesl, Dl = msg
    L = len(Dl)
    diff = nodesl - nodes
    if diff < 0:
        return None
    if cyclic:
        # t ranges over naturals; indices mod len(Dl)
        t = 0; s = 0
        while s < diff:
            s += Dl[t % L]; t += 1
        if s != diff: return None
        if all(D[j] == Dl[(j + t) % L] for j in range(4 * kp)):
            return t
        return None
    else:
        s = 0
        for t in range(0, L - 4 * kp + 1):
            if s == diff and all(D[j] == Dl[j + t] for j in range(4 * kp)):
                return t
            if t < L: s += Dl[t]
        return None


def alg456(cyclic=False):
    def prog(i):
        obs = yield
        D = []
        dis = 0
        obs = yield Dec(release=True, move=True)
        nodes = 1
        # estimating
        while True:
            dis += 1
            if obs.tokens > 0:
                D.append(dis); dis = 0
                j = len(D)
                if j % 4 == 0:
                    q = j // 4
                    if all(D[x] == D[x + q] == D[x + 2*q] == D[x + 3*q] for x in range(q)):
                        kp = q; np_ = sum(D[:kp]); break
            obs = yield Dec(move=True); nodes += 1
        assert nodes == 4 * np_
        # patrolling: at this point we are inside an action at a node (arrival)
        while True:
            # patrol until nodes == 12 np_
            msg = None
            while nodes != 12 * np_:
                obs = yield Dec(move=True, msg=msg); nodes += 1
                msg = (np_, kp, nodes, list(D)) if obs.others > 0 else None
            # deployment
            p = min_period(D[:kp])
            r = rank_of(D[:kp], kp)
            disBase = sum(D[:r])
            m = disBase + offset(r, np_, p)
            for _ in range(m):
                obs = yield Dec(move=True, msg=msg); msg = None; nodes += 1
            # suspended
            dec = Dec(status='susp', msg=msg)
            while True:
                obs = yield dec
                dec = Dec(status='susp')
                best = None
                for mm in obs.msgs:
                    if np_ <= mm[0] / 2:
                        t = check(D, kp, nodes, mm, cyclic)
                        if t is None: REJ.append((i, np_, mm[0], nodes, mm[2]))
                        if t is not None and (best is None or mm[0] > best[0][0]):
                            best = (mm, t)
                if best is not None:
                    mm, t = best
                    LOG.append((i, np_, mm[0], nodes, mm[2], t))
                    np_, kp, Dl = mm[0], mm[1], mm[3]
                    D = shift(Dl, t % len(Dl))
                    assert 12 * np_ - nodes > 0, (12*np_, nodes)
                    break
            # move 12 np_ - nodes (msg already none); continue patrol loop which is a no-op since nodes==12np_ after moves
            cnt = 12 * np_ - nodes
            for _ in range(cnt):
                obs = yield Dec(move=True); nodes += 1
            # back at loop: nodes == 12 np_, go to deployment (line 2)
    return prog
