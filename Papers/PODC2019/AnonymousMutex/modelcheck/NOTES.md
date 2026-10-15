# Bounded model checkers (not part of the Lean development)

* `alg1s.cpp` — Algorithm 1 with any register choice at line 6 and any shrink order, register and
  process symmetry reduction; reports reachable non-trivial SCCs (without completions) that contain
  an empty-memory state and lifts a cycle to a concrete trace. `./alg1s 4 5` finds the livelock
  formalized in `Alg1Livelock.lean`; `n = 2, m ≤ 7` and `n = 3, m ∈ {5,7}`: none.
* `alg2.cpp` / `alg2f.cpp` — Algorithm 2 (any scan order / fixed local orders), fair-SCC search for
  deadlocks: none for `n = 2, m ≤ 7`, `n = 3, m = 1`, `n = 3, m = 5` (6 order assignments).
Build: `g++ -O2 -o alg1s alg1s.cpp`; run under `ulimit -v 4000000; timeout 600`.
* `replay.py` — replays the 28-step schedule of `Alg1Livelock.lean` for the "first ⊥" rule and for the "last ⊥" rule with reversed permutations (both periodic, no completion). Run with `python3 -I replay.py`.
