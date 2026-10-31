"""Model checker for Fig. 1 (two-process memory-anonymous mutex) of Taubenfeld PODC'17.
Process 1 uses the identity order, process 2 a given permutation (all are tried).
Checks mutual exclusion (BFS) and deadlock-freedom (fair SCC without CS entry)."""
import sys, itertools
sys.setrecursionlimit(1000000)

m = int(sys.argv[1])
H = (m + 1) // 2
IDS = (1, 2)

def steps(state, perms):
    regs, locs = state
    for idx in range(2):
        i = IDS[idx]
        pi = perms[idx]
        loc = locs[idx]
        pc = loc[0]
        def mk(nl, nr=regs):
            return (nr, locs[:idx] + (nl,) + locs[idx + 1:])
        if pc == 'REM':
            yield idx, 'start', mk(('L2', 0))
        elif pc == 'L2':
            j = loc[1]
            if regs[pi[j]] == 0:
                yield idx, 'r', mk(('L2W', j))
            else:
                yield idx, 'r', mk(('L2', j + 1) if j + 1 < m else ('L3', 0, 0))
        elif pc == 'L2W':
            j = loc[1]
            nr = regs[:pi[j]] + (i,) + regs[pi[j] + 1:]
            yield idx, 'w', mk(('L2', j + 1) if j + 1 < m else ('L3', 0, 0), nr)
        elif pc == 'L3':
            j, c = loc[1], loc[2]
            c2 = c + (1 if regs[pi[j]] == i else 0)
            if j + 1 < m:
                yield idx, 'r', mk(('L3', j + 1, c2))
            elif c2 < H:
                yield idx, 'r', mk(('L5', 0))
            elif c2 == m:
                yield idx, 'enter', mk(('CS',))
            else:
                yield idx, 'r', mk(('L2', 0))
        elif pc == 'L5':
            j = loc[1]
            if regs[pi[j]] == i:
                yield idx, 'r', mk(('L5W', j))
            else:
                yield idx, 'r', mk(('L5', j + 1) if j + 1 < m else ('L7', 0, True))
        elif pc == 'L5W':
            j = loc[1]
            nr = regs[:pi[j]] + (0,) + regs[pi[j] + 1:]
            yield idx, 'w', mk(('L5', j + 1) if j + 1 < m else ('L7', 0, True), nr)
        elif pc == 'L7':
            j, z = loc[1], loc[2]
            z2 = z and regs[pi[j]] == 0
            if j + 1 < m:
                yield idx, 'r', mk(('L7', j + 1, z2))
            elif z2:
                yield idx, 'r', mk(('L2', 0))
            else:
                yield idx, 'r', mk(('L7', 0, True))
        elif pc == 'CS':
            yield idx, 'exit', mk(('L12', 0))
        elif pc == 'L12':
            j = loc[1]
            nr = regs[:pi[j]] + (0,) + regs[pi[j] + 1:]
            yield idx, 'w', mk(('L12', j + 1) if j + 1 < m else ('REM',), nr)

def check(perms):
    s0 = (tuple([0] * m), (('REM',), ('REM',)))
    seen = {s0: None}
    stack = [s0]
    edges = {}
    while stack:
        s = stack.pop()
        if s[1][0][0] == 'CS' and s[1][1][0] == 'CS':
            tr = []
            while s is not None:
                tr.append(s); s = seen[s]
            return 'ME violated', list(reversed(tr))
        out = []
        for idx, kind, t in steps(s, perms):
            out.append((idx, kind, t))
            if t not in seen:
                seen[t] = s
                stack.append(t)
        edges[s] = out
    # DF: subgraph: no one in CS, exclude 'enter' edges
    nodes = [s for s in edges if s[1][0][0] != 'CS' and s[1][1][0] != 'CS']
    nodeset = set(nodes)
    adj = {s: [(idx, t) for idx, k, t in edges[s] if k != 'enter' and t in nodeset] for s in nodes}
    # Tarjan iterative
    index = {}; low = {}; onst = set(); st = []; comps = []; cnt = [0]
    for root in nodes:
        if root in index: continue
        work = [(root, 0)]
        index[root] = low[root] = cnt[0]; cnt[0] += 1; st.append(root); onst.add(root)
        while work:
            v, pi_ = work[-1]
            if pi_ < len(adj[v]):
                work[-1] = (v, pi_ + 1)
                w = adj[v][pi_][1]
                if w not in index:
                    index[w] = low[w] = cnt[0]; cnt[0] += 1; st.append(w); onst.add(w)
                    work.append((w, 0))
                elif w in onst:
                    low[v] = min(low[v], index[w])
            else:
                work.pop()
                if work:
                    u = work[-1][0]; low[u] = min(low[u], low[v])
                if low[v] == index[v]:
                    comp = []
                    while True:
                        w = st.pop(); onst.discard(w); comp.append(w)
                        if w == v: break
                    comps.append(comp)
    for comp in comps:
        cs = set(comp)
        stepping = set()
        for s in comp:
            for idx, t in adj[s]:
                if t in cs: stepping.add(idx)
        if not stepping: continue
        active = set()
        for s in comp:
            for idx in range(2):
                if s[1][idx][0] != 'REM': active.add(idx)
        if active and active <= stepping:
            return 'DF violated (fair cycle)', comp[:5]
    return None, len(seen)

for p2 in itertools.permutations(range(m)):
    res = check((tuple(range(m)), p2))
    if res[0]:
        print(p2, res[0]);
        for x in res[1]: print(x)
        break
else:
    print('all perms ok for m =', m)
