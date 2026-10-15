import sys, os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from mc2 import explore_o
from ordcircles import ordcircles, U, I
for k, inp in [(2,(0,0,1)),(3,(0,0,1)),(3,(0,0,1,1)),(3,(0,0,1,2))]:
    init = tuple((c, 1, U, 0, 0, c) for c in inp)
    confs, edges = explore_o(init, ordcircles(k), len(inp))
    found = None
    for c in confs:
        leaders = [s for s in c if s[1]]
        if len(set(s[0] for s in leaders)) != len(leaders): continue  # not leader-unique
        for d in range(k):
            users = [s for s in leaders if s[3]==d]
            if users and all(s[2]==I for s in users):
                found = c; break
        if found: break
    print(k, inp, found)
