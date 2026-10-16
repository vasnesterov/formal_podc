# Pseudo-code of Chalopin, Chang, Di Luna, Zhou (arXiv 2603.28260), as generators.
ANY = (0, 1)

def send(p, k=1):
    for _ in range(k):
        yield ('send', p)

def recv(ports=ANY):
    q = yield ('recv', tuple(ports) if not isinstance(ports, int) else (ports,))
    return q

# ---------------- Algorithm 9: ComputeOR ----------------
def compute_or(leader, b):
    ans = True
    if leader:
        yield from send(1 if b else 0)
    q = yield from recv()
    if leader:
        if q == 1:
            yield from send(0)
            yield from recv(1)
            ans = False
        else:
            if b:
                yield from send(0)
            else:
                yield from send(1)
            yield from recv(1)
    else:
        if b:
            yield from send(1)
            yield from recv(1 - q)
            yield from send(0)
        else:
            yield from send(1 - q)
            u = yield from recv()
            yield from send(1 - u)
            if u == 1 and q == 1:
                ans = False
    # barrier
    if leader:
        yield from send(1)
        yield from recv(0)
    else:
        yield from recv(0)
        yield from send(1)
    return ans

# ---------------- Algorithm 7: CCWBitSending; mirror flips ports ----------------
def kappa(bit):
    return {None: 0, 0: 1, 1: 2}[bit]

def ccw_bit_sending(leader, bit, m=0):
    # m = 0: CCW version (as in the paper); m = 1: CW mirror (port p -> 1-p)
    P0, P1 = 0 ^ m, 1 ^ m
    cnt = kappa(bit)
    yield from send(P0, cnt)
    if leader:
        yield from send(P1)
    inn = 0
    while cnt >= 0:
        q = yield from recv()
        if q == P0:
            cnt -= 1
        else:
            yield from send(P1)
            inn += 1
    yield from send(P1)
    if leader:
        yield from recv(P0)
    else:
        while True:
            q = yield from recv()
            if q == P1:
                inn += 1
                yield from send(q)
            else:
                yield from send(P1)  # 1 - q
                break
    return {0: None, 1: 0, 2: 1}.get(inn, ('bad', inn))

def ccw_bit_relay(leader, m=0):
    P0, P1 = 0 ^ m, 1 ^ m
    cnt = 0
    if leader:
        yield from send(P1)
    while cnt >= -1:
        q = yield from recv()
        if not (leader and q == P0 and cnt == -1):
            yield from send(1 - q)
        if q == P1:
            cnt += 1
        else:
            cnt -= 1
    return None

# ---------------- Algorithms 5, 6: MsgExchange / MsgRelay ----------------
def msg_exchange(leader, msgcw, msgccw):
    phase = 0
    rcvdcw, rcvdccw = [], []
    get = lambda msg, i: msg[i] if i < len(msg) else None
    bp, bm = get(msgcw, 0), get(msgccw, 0)
    active = bp is not None or bm is not None
    while (yield from compute_or(leader, active)):
        rcvdccw.append((yield from ccw_bit_sending(leader, bp, m=1)))
        rcvdcw.append((yield from ccw_bit_sending(leader, bm, m=0)))
        phase += 1
        bp, bm = get(msgcw, phase), get(msgccw, phase)
        active = bp is not None or bm is not None
    return (tuple(x for x in rcvdcw if x is not None), tuple(x for x in rcvdccw if x is not None))

def msg_relay(leader):
    while (yield from compute_or(leader, False)):
        yield from ccw_bit_relay(leader, m=1)
        yield from ccw_bit_relay(leader, m=0)
    return 'relay'

# ---------------- Algorithms 1-4: anonymous counting ----------------
class G:  # per-process globals
    pass

def snd_count(count):
    bits = []
    c = count
    while c > 0:
        bits.append(c & 1); c >>= 1
    for b in bits:
        if b == 0:
            yield from send(0, 2)
            for _ in range(2): yield from recv(1)
        else:
            yield from send(1, 2)
            for _ in range(2): yield from recv(0)
    yield from send(1); yield from recv(0)
    yield from send(0); yield from recv(1)
    return bits

def rcv_count():
    L = []
    while True:
        q = yield from recv()
        yield from send(1 - q)
        u = yield from recv()
        yield from send(1 - u)
        if (q, u) == (1, 1): L.append(0)
        elif (q, u) == (0, 0): L.append(1)
        if (q, u) == (0, 1): break
    return L

def leader_proc(g, phase):
    count = 0
    while True:
        yield from send(1)
        q = yield from recv()
        if q == 1:
            count += 1
        else:
            yield from send(0, 3)
            for _ in range(3): yield from recv(1)
            bits = yield from snd_count(count)
            return ('L', phase, count, bits, g)
        if count == phase: break
    yield from send(0)
    yield from recv(1)
    yield from recv(0)
    yield from send(1)
    phase += 1
    return (yield from nonleader_proc(g, phase, True, 0))

def nonleader_proc(g, phase, counted, relayed):
    while True:
        q = yield from recv()
        if not counted and q == 0:
            yield from send(0)
            counted = True
            g.myPhase = phase
        elif counted and q == 0:
            relayed += 1
            yield from send(1)
            yield from recv(1)
            yield from send(0)
        elif q == 1:
            yield from send(0)
            if phase == getattr(g, 'myPhase', None) and relayed == 0:
                yield from send(1)
                yield from recv(0)
                phase += 1
                return (yield from leader_proc(g, phase))
            else:
                q = yield from recv()
                if q == 0:
                    yield from send(1)
                    phase += 1
                    continue
                else:
                    yield from send(0)
                    bits = yield from rcv_count()
                    return ('N', phase, relayed, bits, g)

def counting(is_leader):
    g = G()
    if is_leader:
        return (yield from leader_proc(g, 1))
    return (yield from nonleader_proc(g, 1, False, 0))
