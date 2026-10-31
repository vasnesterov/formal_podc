# Builds the case trees of FourTreeA/B.lean: a memoised search for a small certified case tree
# (certificates on populations of at most NMAX agents, default 5). Writes tree2_<case>.pkl; then
#   python3 emit.py <case>  prints the Lean term of `treeA` / `treeB`.
# Usage (from this directory): python3 gen2.py A 7 ; python3 gen2.py B
# (these exact commands reproduce FourTreeA.lean and FourTreeB.lean; `gen2.py A` gives a larger tree)
import sys, itertools, pickle
from functools import lru_cache
sys.path.insert(0,'.')
from gen import *
case=sys.argv[1]
G=[0,1,0,1] if case=='A' else [0,1,1,0]
same=[k for k in UPAIRS if G[k[0]]==G[k[1]]]
cross=[k for k in UPAIRS if G[k[0]]!=G[k[1]]]
base={k:k for k in same}
memo={}
def best(tbl_items):
    if tbl_items in memo: return memo[tbl_items]
    tbl=dict(tbl_items)
    c=find_cert(tbl,G)
    if c is not None:
        r=(1,('leaf',c)); memo[tbl_items]=r; return r
    rest=[k for k in cross if k not in tbl]
    if not rest:
        assert inv_ok(tbl), tbl
        r=(1,('inv',tbl)); memo[tbl_items]=r; return r
    bestr=None
    for k in rest:
        tot=0; ch=[]
        for o in UPAIRS:
            t2=dict(tbl); t2[k]=o
            s,sub=best(tuple(sorted(t2.items())))
            tot+=s; ch.append((o,sub))
        if bestr is None or tot<bestr[0]: bestr=(tot,('split',k,ch))
    memo[tbl_items]=bestr; return bestr
s,tree=best(tuple(sorted(base.items())))
print(case,'leaves',s)
pickle.dump(tree,open('tree2_%s.pkl'%case,'wb'))
