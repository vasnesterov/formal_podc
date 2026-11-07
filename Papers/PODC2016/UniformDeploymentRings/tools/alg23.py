from sim import *
import math

STATS = {}

def alg23(k, fixed_loop=True):
    def prog(i):
        obs = yield
        # first action at home: release token and start sub-phase 1
        n = None
        phase = 1
        role = None
        first = True
        # helper state: we are at home at the start of each sub-phase, inside an action.
        release = True
        while True:
            if not fixed_loop and phase == math.ceil(math.log2(k)):
                role = 'stuck'; break
            # --- move to next active node, get own ID ---
            tcount = 0; dist_total = 0
            d = 0; f = 0
            obs = yield Dec(release=release, move=True); release = False
            while True:
                d += 1; dist_total += 1
                if obs.tokens > 0:
                    tcount += 1
                    if obs.others > 0 and tcount < k:
                        f += 1
                    else:
                        break
                obs = yield Dec(move=True)
            myID = (d, f)
            if tcount == k:  # back at home: only ai is active
                if first: n = dist_total
                role = 'leader'; fNum = f; break
            # --- ID of next active ---
            def seg():
                nonlocal obs, tcount, dist_total
                d = 0; f = 0
                obs = yield Dec(move=True)
                while True:
                    d += 1; dist_total += 1
                    if obs.tokens > 0:
                        tcount += 1
                        if obs.others > 0 and tcount < k:
                            f += 1
                        else:
                            break
                    obs = yield Dec(move=True)
                return (d, f)
            nextID = yield from seg()
            identical = (myID == nextID)
            mn = not (myID > nextID)
            while tcount < k:
                o = yield from seg()
                if o != myID: identical = False
                if myID > o: mn = False
            if first: n = dist_total; first = False
            STATS[i] = phase
            if identical:
                role = 'leader'; fNum = f; break
            if (not mn) or myID == nextID:
                role = 'follower'; break
            phase += 1
        STATS[i] = phase
        if role == 'stuck':
            while True:
                obs = yield Dec(status='susp')
        if role == 'leader':
            t = 0
            # we are at home inside an action
            msg = None
            while t != fNum:
                obs = yield Dec(move=True, msg=msg); msg = None
                while obs.tokens == 0:
                    obs = yield Dec(move=True)
                msg = ('tBase', fNum - t)
                t += 1
            obs = yield Dec(move=True, msg=msg)
            while obs.tokens == 0:
                obs = yield Dec(move=True)
            yield Dec(status='halt')
            return
        # follower: wait at home
        tb = None
        dec = Dec(status='susp')
        while tb is None:
            obs = yield dec
            for m in obs.msgs:
                if m[0] == 'tBase': tb = m[1]
        c = 0
        obs = yield Dec(move=True)
        while True:
            if obs.tokens > 0:
                c += 1
                if c == tb: break
            obs = yield Dec(move=True)
        step = n // k
        while True:
            for _ in range(step):
                obs = yield Dec(move=True)
            if obs.others == 0:
                yield Dec(status='halt'); return
    return prog
