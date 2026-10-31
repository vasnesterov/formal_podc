# Random-testing scripts (not part of the Lean development)

Python 3, no dependencies. Run from this folder (the scripts import `mc.py` from the current
directory), e.g. `python3 -I mc.py` (Figure 5 example), `python3 -I mc2.py . full <seed> <trials>`,
`python3 -I lem4.py <seed> <trials> <runs>`, `python3 -I c1drive.py <seed> <trials> <runs>`.

* `mc.py` — computes the timestamp graphs `E_i` (Definitions 6–7) by enumerating simple loops, and
  simulates the algorithm of Section 3.2 on random schedules (non-FIFO, random delays), checking
  safety and that every update is eventually applied.
* `mc2.py` — the same with adversarial "held-back" messages; `full` mode tests the algorithm on
  random share graphs (no violation found), `minimal` mode removes single edges from `E_i`.
* `lem4.py` — checks Lemma 4 at every issue event; finds violations both for `e_ki ∉ E_j`
  (where `T[e_ki]` is undefined) and for `e_ki ∈ E_j` (formalized in `Lemma4.lean`).
* `c1.py`, `c1drive.py` — search for two executions in which a replica has the same causal past
  but different timestamps (refutes footnote 2; formalized in `Footnote2.lean`).
