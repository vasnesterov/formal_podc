"""SAT encoding of forwarding patterns on the Figure 3 network (Feigenbaum et al., PODC 2012).

One Boolean variable per (node, live-link view, incoming link, outgoing link); used by scenarios.py.
Node 0 is the destination d; the edge list is the same graph as Fig3.lean.
"""
import itertools
from pysat.solvers import Cadical153 as Solver

D = 0  # node 0 = d
EDGES = [(1,2),(1,3),(1,4),(1,5),(2,6),(6,3),(2,9),(9,5),(3,7),(7,4),(5,8),(8,4),
         (0,9),(0,8),(5,11),(0,10),(0,6),(0,7),(2,10),(10,4),(3,11),(11,0)]
def setup(edges):
    n = 1+max(max(e) for e in edges)
    inc = {v: [k for k,e in enumerate(edges) if v in e] for v in range(n)}
    return n, inc
N, INC = setup(EDGES)
def other(k, v):
    a,b = EDGES[k]; return b if a==v else a

class Pool:
    def __init__(self): self.n=0; self.names={}
    def new(self, name=None):
        self.n+=1
        if name is not None: self.names[name]=self.n
        return self.n
pool = Pool()
# fvar[(v, A, e, o)] : node v, alive-mask A over INC[v] (tuple of bools), inport edge e in A, output edge o in INC[v]
fvar = {}
def views(v):
    return list(itertools.product([False,True], repeat=len(INC[v])))
for v in range(N):
    if v==D: continue
    for A in views(v):
        for ie,e in enumerate(INC[v]):
            if not A[ie]: continue
            for o in INC[v]:
                fvar[(v,A,e,o)] = pool.new()
clauses = []
for v in range(N):
    if v==D: continue
    for A in views(v):
        for ie,e in enumerate(INC[v]):
            if not A[ie]: continue
            lits = [fvar[(v,A,e,o)] for o in INC[v]]
            clauses.append(lits)
            for a,b in itertools.combinations(lits,2): clauses.append([-a,-b])

def view_of(v, F):
    return tuple(k not in F for k in INC[v])

def connected_to_d(F):
    adj = {v: [] for v in range(N)}
    for k,(a,b) in enumerate(EDGES):
        if k in F: continue
        adj[a].append(b); adj[b].append(a)
    seen={D}; st=[D]
    while st:
        x=st.pop()
        for y in adj[x]:
            if y not in seen: seen.add(y); st.append(y)
    return seen

def scenario_clauses(F):
    """returns clauses encoding (1)+(2) for failure set F (set of edge indices)."""
    cl=[]
    alive = [k for k in range(len(EDGES)) if k not in F]
    darts = [(k,a,b) for k in alive for (a,b) in [EDGES[k], EDGES[k][::-1]]]  # a->b via edge k
    L = len(darts)
    idx = {(k,a):i for i,(k,a,b) in enumerate(darts)}
    # succ[i][j] : dart i's successor is dart j  (expressed via f vars)
    # rank order-encoding: r[i][t] = rank(i) >= t, t=1..L
    reach = [pool.new() for _ in darts]
    r = [[pool.new() for t in range(L)] for _ in darts]  # r[i][t] : rank >= t+1
    for i in range(L):
        for t in range(L-1): cl.append([-r[i][t+1], r[i][t]])
    for i,(k,a,b) in enumerate(darts):
        if b==D:
            cl.append([reach[i]]); continue
        A = view_of(b, F)
        succ_lits=[]
        for o in INC[b]:
            fv = fvar[(b,A,k,o)]
            if o in F:
                cl.append([-fv, -reach[i]])  # drop
            else:
                j = idx[(o,b)]
                # fv -> (reach i <-> reach j), rank(i) > rank(j)
                cl.append([-fv, -reach[i], reach[j]]); cl.append([-fv, reach[i], -reach[j]])
                cl.append([-fv, r[i][0]])
                for t in range(L-1): cl.append([-fv, -r[j][t], r[i][t+1]])
                cl.append([-fv, -r[j][L-1]])
    conn = connected_to_d(F)
    for v in conn:
        if v==D: continue
        cl.append([reach[idx[(k,v)]] for k in INC[v] if k not in F])
    return cl
