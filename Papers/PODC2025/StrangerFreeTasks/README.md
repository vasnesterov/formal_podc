# Stranger-Free Tasks

Eli Gafni, Giuliano Losa, Michel Raynal, Gadi Taubenfeld.
*Brief Announcement: Stranger-Free Tasks.* PODC 2025, pp. 203–206.
DOI [10.1145/3732772.3733545](https://doi.org/10.1145/3732772.3733545) (local PDF:
`papers/2025/3732772.3733545_Brief_Announcement_Stranger_Free_Tasks.pdf`).

## Model

Asynchronous shared memory, CSLib `Cslib.SharedMemory`:

* processes `P` (any type with decidable equality; finite with `|P| = n` for Theorem 2.1, arbitrary —
  possibly infinite — for Algorithm 1), deterministic programs, any interleaving, no crashes (a
  process may simply stop taking steps); progress: wait-freedom / obstruction-freedom as in CSLib
  (infinite executions / solo runs);
* atomic multi-writer multi-reader read/write registers `RegFamily ι V v₀`, not pre-allocated;
* tasks (`Cslib/Computability/Distributed/SharedMemory/Task.lean`): one-shot, `Impl.Solves T` = the input/output relation holds
  on every finite one-shot execution; participation = invocation;
* full-information versions and views (`Cslib/Computability/Distributed/SharedMemory/FullInfo.lean`).

## Main results ↔ Lean

| Paper | Lean | File | Status |
|---|---|---|---|
| Def. full-information version | `Impl.fullInfo`, `View`, `View.Mentions` | `Cslib/Computability/Distributed/SharedMemory/FullInfo.lean` | def |
| "an algorithm and its full-information version solve the same tasks, same registers" | `fullInfo_solves`, `fullInfo_waitFree`, `fullInfo_obstructionFree`, `fullInfo_run`, `fullInfo_covers` | same | proved |
| Def. stranger-free task | `Task.StrangerFree T prog` (`prog = .waitFree` = paper) | `StrangerFree.lean` | def |
| Thm. 2.1 | `theorem_2_1` (`n ≤ #registers`), covering form `covering_of_strangerFree` | `StrangerFree.lean` | proved |
| remark after Thm. 2.1 (obstruction-free) | `theorem_2_1_obstructionFree` (needs `StrangerFree .obstructionFree`) | `StrangerFree.lean` | proved |
| Def. `k`-bounded lattice agreement | `boundedLA P k` | `BoundedLA.lean` | def |
| §3.2: `k`-LA for `k+1` processes is stranger-free | `boundedLA_strangerFree` (any progress condition), via `mentions_of_mem_output` | `LowerBound.lean` | proved (omitted routine step formalized) |
| Thm. 3.1, lower bound | `theorem_3_1_lowerBound` (wait-free), `boundedLA_lowerBound` (obstruction-free) | `Main.lean`, `LowerBound.lean` | proved |
| Algorithm 1 | `alg1 k` | `Alg1.lean` | def |
| §3.1 safety of Alg. 1 (any number of processes) | `alg1_solves`, `alg1_containment`, `card_union_of_obliterate` | `Alg1Safety*.lean` | proved (gap in the paper's argument repaired) |
| §3.1 wait-freedom of Alg. 1 | **false for `k ≥ 2`**: `alg1_not_waitFree`, `exists_livelock`, `theorem_3_1_alg1_not_waitFree` | `Alg1Livelock.lean`, `Main.lean` | **refuted** |
| (what holds) Alg. 1 obstruction-free | `alg1_obstructionFree` | `Alg1OF.lean` | proved |
| Thm. 3.1 (corrected: obstruction-free hierarchy) | `theorem_3_1_obstructionFree` | `Main.lean` | proved |
| Thm. 3.1, `k = 1` (wait-free, as stated) | `theorem_3_1_k1`, `alg1_waitFree_one`, `alg1_one_finite_steps` | `Main.lean`, `Alg1WaitFreeK1*.lean` | proved |
| non-vacuity / tightness of Thm. 2.1 (`n = 2`) | `theorem_2_1_tight` (`boundedLA (Fin 2) 1` stranger-free and solved wait-free with 2 registers by `twoAlg`) | `TwoProcess.lean` | proved |

All theorems above are checked with `lean_verify` (axioms: `propext`, `Classical.choice`,
`Quot.sound` only).

## Status

* Theorem 2.1 (both variants) and the lower bound of Theorem 3.1: **proved**; the full-information
  reduction is made precise; the stranger-freedom of `k`-bounded lattice agreement needs a
  causal-erasure argument for a step the paper omits as routine. Stranger-freedom quantifies over
  algorithms accepting every input at every process.
* Upper bound of Theorem 3.1: **the paper's Algorithm 1 is not wait-free for `k ≥ 2`** (Lean
  counterexample with two processes). It is safe and obstruction-free for every `k` and any (also
  infinite) set of processes. So Theorem 3.1 holds in the obstruction-free sense for every `k`; in the wait-free
  sense it holds for `k = 1` and is open for `k ≥ 2`.
* `k = 1`: **Theorem 3.1 holds as stated**: Algorithm 1 is wait-free for `k = 1` and any (also infinite)
  set of processes (`alg1_waitFree_one`; even every process takes finitely many steps in every infinite
  execution, `alg1_one_finite_steps`), packaged as `theorem_3_1_k1`. The proof is ours (the paper's
  sketch does not apply): a "doomed" potential, the fact that a process other than `p` can write `A[1]`
  only as its 2nd write, and that only processes that read `⊥` from `A[1]` (finitely many) can do so.
* No `sorry`, no axioms.

## Infrastructure (now in CSLib, `Cslib/Computability/Distributed/SharedMemory/`)

* `Task.lean` — tasks, `Solves`, one-shot executions, `OneShotOF`, `proc_ne_of_opsOf_eq_nil`.
* `Covering.lean` — covering / block-write lemmas: `Overwrites`, `Covers`, `AgreeOn`,
  `runFrom_agreeOn`, `step_local`, `blockWrite_agreeOn` (indistinguishability after a block write),
  `blockWrite_run`, `exists_solo_until`, solo-run memory/locality lemmas.
* `FullInfo.lean` — views, full-information versions, transfer lemmas, `FIClean` taint invariant,
  causal erasure `fullInfo_exists_erase`.
* In this folder, generic and CSLib-worthy: `run_induction` (`Alg1SafetyBasic.lean`),
  `Impl.run_induction'` (`TwoProcess.lean`). `TwoProcess.lean` uses `Impl.waitFree_of_potential` from
  `Papers/PODC2024/HistoryIndependent/Alg4WaitFree.lean` (also a CSLib candidate).

## Files

`BoundedLA.lean` (task), `StrangerFree.lean` (definition, Thm 2.1), `LowerBound.lean` (§3.2),
`Alg1.lean` (Algorithm 1), `Alg1SafetyBasic/Snapshot/Obliterate.lean`, `Alg1Safety.lean` (safety),
`Alg1OF.lean` (obstruction-freedom), `Alg1Livelock.lean` (counterexample, `k ≥ 2`),
`Alg1WaitFreeK1Inv/Doomed.lean`, `Alg1WaitFreeK1.lean` (wait-freedom for `k = 1`), `TwoProcess.lean`
(tightness), `Main.lean` (summary theorems).

## Effort

Roughly 1.5M tokens in total (paper agent + 4 subagents: livelock/k = 1 wait-freedom, safety,
obstruction-freedom, two-process algorithm). Model checking (explicit-state, token
canonicalization) found the livelock: k = 1 is wait-free for n ≤ 3, k = 2, n = 2 livelocks.
