# Bounded model checkers (not part of the Lean development)

Run each under `(ulimit -v 4000000; timeout 600 python3 -I <script> ...)`.

* `mutex.py m` — Figure 1 (two processes, `m` registers; process 1 identity order, process 2 every
  permutation). Checks mutual exclusion (reachability) and deadlock-freedom (fair SCCs without a
  critical-section entry). `m = 3, 5`: no violation.
* `cons.py N inputs any|fixed skip|write` — Figure 2. `cons.py 2 1,2 any skip`: no violation
  (any read order). `cons.py 2 0,1 any skip`: agreement fails when an input equals the initial
  value `0` of the `val` fields (the formalization types inputs apart from `⊥`).
* `ren.py N` — Figure 3, exhaustive with any read order: `N = 2` no violation (`N = 3` too large
  for this script).
* `ren_rand.py N RUNS SEED` — Figure 3, random adversarial schedules (random permutations, bursts,
  random choices at lines 9/15): `3 100000 1` and `4 30000 2`, no violation.
* `mutex_scenario.py 3 0,1,2` (uses `mutex_model.py`) — Figure 1: a schedule in which both
  processes give up (line 4) with no CS entry in between, refuting the claim in the proof of
  Theorem 3.3 that exactly one process gives up and the other then enters.
