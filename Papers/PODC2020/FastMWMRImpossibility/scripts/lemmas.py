"""Random runs, tallying failures of the paper's intermediate lemmas (even in
linearizable executions) and linearizability violations.
usage: python3 lemmas.py S t R wops rops srv wq vq N [seed] [show]
"""
import sys
import os
import random
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from w2r1 import Config, random_run, linearizable, lemma_checks

S, t, R = map(int, sys.argv[1:4])
def ops(x):
    return int(x) if "," not in x else [int(y) for y in x.split(",")]
wops, rops = ops(sys.argv[4]), ops(sys.argv[5])
srv, wq, vq = sys.argv[6:9]
N = int(sys.argv[9])
seed = int(sys.argv[10]) if len(sys.argv) > 10 else 0
show = sys.argv[11].split(',') if len(sys.argv) > 11 else []
cfg = Config(S, t, 2, R, wops, rops, srv=srv, wq=wq, vq=vq)
rng = random.Random(seed)
cnt = {}
first = {}
for i in range(N):
    s = random_run(cfg, rng)
    fails = lemma_checks(s)
    if not linearizable(s.hist):
        fails.append("NONLIN")
    for f in set(x.split(':')[0] for x in fails):
        cnt[f] = cnt.get(f, 0) + 1
        if f not in first or len(s.trace) < len(first[f][0].trace):
            first[f] = (s, [x for x in fails if x.startswith(f)])
print(f"S={S} t={t} R={R} wops={wops} rops={rops} srv={srv} wq={wq} vq={vq}: {N} runs; failures: {cnt}")
for f in show:
    if f in first:
        s, msgs = first[f]
        print(f"--- shortest example for {f}:")
        print("\n".join(s.trace))
        print(*msgs, sep="\n")
