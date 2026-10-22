"""Scripted counterexample: late (stale) read request marks a reader in an
`updated` set without that reader ever learning the value.
usage: python3 scenario_late.py [srv-reading]   (default D2; try D, L)
Parameters: S=5, t=1, R=2 (R < S/t - 2 = 3), writers w1 (1 write), w2 (idle),
readers r1 (1 read), r2 (3 reads)."""
import sys
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from w2r1 import Config, Sys, linearizable, lemma_checks

srv = sys.argv[1] if len(sys.argv) > 1 else 'D2'
ctr = srv.endswith('c')
srv = srv.rstrip('c')
cfg = Config(5, 1, 2, 2, [1, 0], [1, 3], srv=srv, wq='A', vq='all')
cfg.ctr = ctr
W1, R1, R2 = 1, 3, 4
s = Sys(cfg)


def dl(c, srv_id, kind=None, old=False):
    """deliver c's request to server srv_id: the current-round one, or with
    old=True the oldest one still in transit"""
    cands = [(m[2], m[3], i) for i, m in enumerate(s.pending)
             if m[0] == srv_id and m[1] == c and (kind is None or m[4] == kind)]
    if not cands:
        raise KeyError((c, srv_id, kind))
    s.deliver((min(cands) if old else max(cands))[2])


# r2: first read rho1, its request to s1 stays in transit
s.invoke(R2)
for x in (0, 2, 3, 4):
    dl(R2, x)
s.step(R2, [0, 2, 3, 4])
# w1: query round, then its write reaches s0 only (for now)
s.invoke(W1)
for x in (2, 3, 4):
    dl(W1, x, 'query')
s.step(W1, [2, 3, 4])
dl(W1, 0, 'write')
# r2: second read rho2; s1 answers before the write arrives there
s.invoke(R2)
for x in (1, 2, 3, 4):
    dl(R2, x)
s.step(R2, [1, 2, 3, 4])
dl(R2, 0)          # rho2's request reaches s0 late: r2 marked on (1,w1) at s0
dl(W1, 1, 'write')  # write reaches s1
dl(R2, 1, old=True)  # rho1's request (still in transit) reaches s1: r2 marked at s1
# r1 reads s0..s3
s.invoke(R1)
for x in (0, 1, 2, 3):
    dl(R1, x)
s.step(R1, [0, 1, 2, 3])
# r2 reads s0, s2, s3, s4
s.invoke(R2)
for x in (0, 2, 3, 4):
    dl(R2, x)
s.step(R2, [0, 2, 3, 4])
print("\n".join(s.trace))
print("linearizable:", linearizable(s.hist))
print(*lemma_checks(s), sep="\n")
