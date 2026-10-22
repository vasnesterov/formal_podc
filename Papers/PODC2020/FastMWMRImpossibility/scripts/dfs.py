"""Exhaustive bounded DFS.
usage: python3 dfs.py S t R wops rops srv wq vq [max_states] [time_limit_s] [late_bound, -1 = unbounded]
wops/rops: int (per client) or comma list per client
"""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from w2r1 import Config, dfs, replay, lemma_checks

S, t, R = map(int, sys.argv[1:4])
def ops(x):
    return int(x) if ',' not in x else [int(y) for y in x.split(',')]
wops, rops = ops(sys.argv[4]), ops(sys.argv[5])
srv, wq, vq = sys.argv[6:9]
ctr = srv.endswith('c')
srv = srv.rstrip('c')
ms = int(sys.argv[9]) if len(sys.argv) > 9 else 2_000_000
tl = float(sys.argv[10]) if len(sys.argv) > 10 else 540
K = int(sys.argv[11]) if len(sys.argv) > 11 else -1
cfg = Config(S, t, 2, R, wops, rops, srv=srv, wq=wq, vq=vq)
cfg.ctr = ctr
cfg.late_bound = None if K < 0 else K
cfg.qabs = (wq == 'A')
path, n, complete, lf = dfs(cfg, ms, check_lemmas=True, time_limit=tl)
print(f"S={S} t={t} R={R} wops={wops} rops={rops} srv={srv}{'c' if ctr else ''} wq={wq} vq={vq} late_bound={cfg.late_bound}: states={n} "
      f"{'EXHAUSTED' if complete else 'BUDGET HIT'}; {'VIOLATION' if path else 'no violation'}; "
      f"lemma failures seen: {sorted(lf)}")
if path:
    s = replay(cfg, path)
    print("\n".join(s.trace))
    print(*lemma_checks(s), sep="\n")
