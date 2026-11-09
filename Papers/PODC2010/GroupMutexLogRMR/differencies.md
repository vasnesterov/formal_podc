# Differences between the formalization and the paper

Paper: Bhatt, Huang. *Group Mutual Exclusion in O(log n) RMR.* PODC 2010 (authors' copy, 10 pages).

## Mistakes (with labels)

- ❌ **Theorem 1 (P2) / Lemma 3** — starvation freedom is false: a fair execution with 2 processes and 2 sessions
  deadlocks (`starvationFree_false`, `Deadlock.lean`). The proof of Claim 4 overlooks a line-10 `SC(Ex,false)` of a
  fellow process between `q[16.3]` and `q[16.6]` (a fellow's successful `SC(Ex,false)` at line 16.2 in that window
  has the same effect; in `deadSched` both happen).
- ❌ **Lemma 2 (P4) as stated, Claim 3** — false in the paper's formulation "no conflicting process active at time
  `t`" (`concurrentEnteringPaper_false`, `claim3_false`). In the strict reading (no conflicting process during the
  whole attempt) P4 is unchecked (exhaustive model checking with 2 processes found no violation), but its proof via
  Claim 3 is broken either way.
- ❌ **Invariant 8** — false (`invariant8_false`).
- ❌ **Theorem 1 / Lemma 5 (RMR)** — the RMRs of one attempt are unbounded for `n = 4` (`rmr_unbounded`,
  `not_bounded_rmr`, `RMR.lean`); line 7 rewrites `Out[s]` repeatedly while a process of the other side spins on it.
- ✏️ **Invariant 1** — false for processes at lines 1.2–1.3 (counted, no side); replaced by the exact count
  `Inv.gC`.
- ✏️ **Invariant 6** — the winner may be at line 16.14 (range 16.10–16.13 too small); our `LI.win`.
- ✏️ **Invariant 7** — false for processes in `LE` but not in `LS` (S may have been switched by Promote-Try);
  correct with `p ∈ LS` (`LI.e1`, `LI.e2`).
- 🛠️ **Theorem 1 (P1)** — "follows easily from Invariant 5", but the invariants are unproved; proved with a new
  inductive invariant `Inv` (`mutual_exclusion`).

## Modelling choices

- Processes `Fin n`, sessions an arbitrary type `J` with decidable equality (the paper's bound `m` on the number of
  sessions is not needed for P1/P3; counterexamples use `J = Fin 2`).
- One atomic step per numbered line; line 1.8 (`return d`) merged with line 1.7; the CS is one step `cs`.
- `G`, `C[s,d]`, `Q` are atomic objects; the f-array implementations (Theorems 2–3) are not modelled. `C[s,d] ∈ ℕ`
  with truncated decrement (never truncates in reachable states, by `Inv.gC`).
- `Q` is one slot per process holding `(s, d, tm)`; `Min(Q)` is computed by a scan keeping the element with
  strictly smaller time-stamp, so ties go to the smaller process index, as in the paper's order `(tm, p)`.
- LL/SC: per-process link bits set by `LL` and cleared for all processes by every successful `SC` — equivalent to
  the paper's definition. Line 16.12 is a plain read of `S`. Lines 9 and 11 are `LL(Ex)` (as written).
- `Ex = false` is `none`; `Exclear[false]` is never read (line 12 is only reached with `se ≠ false`).
- Waiting (lines 8, 12) is a read that leaves the configuration unchanged when the condition fails.
- A process in the remainder section that takes a step starts an attempt with an adversary-chosen session.
- Initial `S = (s₀, 0, s₀)` for a parameter `s₀`.
- Fairness (for P2): every process takes infinitely many steps or stays in the remainder section from some time on
  (`Sched.Fair`). Starvation freedom is stated for fair executions in which no process stays in the CS forever.
- Lemma 2 is formalized in the paper's wording (a process in the trying section, no active conflicting process,
  takes at most `b` steps); we refute it with a solo run.
- RMRs: write-invalidate cache-coherent model restricted to reads of `Out` at line 8 by one process and to writes
  of `Out` (lines 5.5, 7, 16.11, 16.13); this is a lower bound on the process's RMRs. The counter is reset when the
  process starts an attempt, so it counts the RMRs of the current attempt.
- P3 is stated as: 17 own steps of a process in the exit section bring it back to the remainder section, whatever
  the other processes do.

## Not formalized

- P5' (relaxed FCFS) — the paper gives no proof.
- P6 (pulling, Lemma 4, Claims 9–10) — unchecked; random simulation (3–4 processes, ~2.5M premise instances) found
  no violation.
- Concurrent entering in the strict sense (no conflicting process during the whole attempt) — unchecked; exhaustive
  model checking with 2 processes found no violation.
- Invariants 2 and 4 are not stated separately; they follow from clauses of `Inv` (`a3`, `e2`, `e3`, `g7`; `p5`,
  `p11`, and for line 16.13 the weaker `p13`). The model checker confirms Invariants 2–5 and Lemma 1 on all
  reachable configurations with 3 processes and 2 sessions.
- The f-array implementations of Theorems 2–3 and their RMR bounds.
- The first two "attempts" (Figures 1–2) and their failure scenarios.
