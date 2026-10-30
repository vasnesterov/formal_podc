# Recoverable Mutual Exclusion with Constant Amortized RMR Complexity — PODC 2020

David Yu Cheng Chan, Philipp Woelfel. *Recoverable Mutual Exclusion with Constant Amortized RMR
Complexity from Standard Primitives.* PODC 2020. DOI
[10.1145/3382734.3405736](https://doi.org/10.1145/3382734.3405736). Formalized version: the
conference version (10 pages); proofs deferred to the full version were not used.

**Verdict: ⚠️ Minor statement issues.** The algorithm of Figure 1 is correct: mutual exclusion,
critical-section re-entry (wait-free), starvation freedom, wait-free recovery and wait-free
recovery to exit are all proved, as is the constant amortized RMR bound in the DSM model. Two
statements are wrong as written, both with evident intent. The RMR bound "`O(m)` when `m`
passages begin" fails under the paper's literal definition of a passage, but holds when every
crash also starts a passage. Lemma 2.1 (19) (and Lemmas 2.4–2.6) omit the fairness hypothesis.

## Mistakes in the paper

* **The RMR bound needs crashes to start passages (Theorems 1–2, definitional slip).** The paper
  says a passage "begins when [the process] calls `Enter()` and ends when the process crashes or
  when it finishes its following `Exit()` call". Read literally, the steps of `Recover()` belong
  to no passage. Take one process: it calls `Enter()` once and reaches the critical section. It
  then crashes in the critical section over and over, and each time `Recover()` line 20 sends it
  straight back in. Every round executes `D.FAI()` (line 15). This is an RMR in the CC model
  (a non-read operation), and in the DSM model for every process whose segment does not hold `D`
  (with `n ≥ 2`, pick such a process and keep the others idle). So one passage begins but there
  are unboundedly many RMRs
  (`Literal.rmr_literal_unbounded`). The fix is the usual RME convention: a crash ends a passage
  and the recovery starts a new one. With it the claim holds. We prove at most
  `25·#Enter() + 76·#crashes` RMRs in the DSM model, counting only crashes outside the remainder
  section (`rmr_bound`).
* **Lemma 2.1 (19) and Lemmas 2.4–2.6 need fairness.** Lemma 2.1 is stated for "any run", and
  (19) assumes only finitely many crashes. Without fairness it fails. Take two processes and no
  crash. Process `false` gets ticket 1 and grants it to itself (`W = (1,true)`), then stops taking
  steps. Process `true` gets ticket 2 and busy-waits forever. `Token` stays 0
  (`Lemma2_1_19.lemma2_1_19_false`). These lemmas are only used in the starvation-freedom proof,
  where fairness holds. There the paper's argument goes through.
* **Omitted proofs.** Lemma 2.1 (19 items), Lemmas 2.2, 2.4, 2.6, 2.7, 2.10 and all RMR claims come
  without proof. We prove all items we need, using a single inductive invariant (see below).
  Lemma 2.3's proof argues backwards in time. We made it inductive, and the argument is sound.
  Section 3.1 claims that skipped tickets are at most twice the number of crashes. This is true
  (`skipped_le_two_mul_crashes`) and gives Lemma 2.10.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Asynchronous shared memory, deterministic algorithm, processes of any finite type. Shared
  objects: FAI counters `C`, `D`; CAS objects (with read/write) `A[1..∞]`, `W[p]`, `Exit[p]`,
  `Token`. `A[c]` is `empty` / `claimed q` / `skipped` (0 / `q` / −1).
* One shared-memory operation per step. The local code after it is merged into that step, and the
  recursive `Move_Token()` calls are tail calls (a jump to line 34). The program counter carries
  the local variables.
* Individual crash–recovery. Any process may crash at any time. Outside the remainder section a
  crash resets its local state and starts `Recover()`; in the remainder section it does nothing.
  Shared memory (NVM) is never lost.
* Executions are arbitrary schedules `ℕ → {step p, crash p}` (an adversarial scheduler, no
  randomness). Liveness assumes finitely many crashes and fairness: a process outside the
  remainder section keeps taking steps. A step in the CS is the call of `Exit()`.
* RMRs (DSM only): `W[p]` and `Exit[p]` live in `p`'s segment. Every access to `C`, `D`, `Token`
  or `A` is charged as an RMR, which is an upper bound for every placement.
* Ghost state (ticket owners, `c_{p,t}`, crash credits, lost tickets) is computed alongside the
  execution and never read by the algorithm.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Lemma 2.1 (strengthened state form) | `Inv`, `inv_exec` | `InvDefs.lean`, `Invariant.lean` |
| Lemma 2.1 (3), (4), (7)–(11), (16) | `lemma2_1_3`, `lemma2_1_4`, `lemma2_1_7`, `lemma2_1_8`, `lemma2_1_9`, `lemma2_1_10`, `lemma2_1_11`, `lemma2_1_16` | `Skips.lean`, `Safety.lean` |
| Lemma 2.1 (19) without fairness: **false** | `Lemma2_1_19.lemma2_1_19_false` | `Lemma2_1_19.lean` |
| Lemma 2.3 (`D + \|I\| − C ≥ 0`) | `lemma2_3` | `Safety.lean` |
| §3.1: skipped tickets ≤ 2·crashes; Lemma 2.10 | `skipped_le_two_mul_crashes`, `lemma2_10` | `Skips.lean` |
| Lemma 2.11 (mutual exclusion) | `mutual_exclusion` | `Safety.lean` |
| Critical-section re-entry | `cs_reentry` | `Safety.lean` |
| Lemma 2.12 (wait-free recovery, bound 3) | `wait_free_recovery` | `WaitFree.lean` |
| Lemma 2.13 (starvation freedom) | `eventually_rem_or_cs`, `enter_reaches_cs`, `exit_reaches_rem`, `recover_terminates` | `Liveness.lean` (+ `Liveness*.lean`) |
| Lemma 2.14 (wait-free CS re-entry, bound 3) | `cs_reentry_waitfree` | `Safety.lean` |
| Lemma 2.15 (wait-free recovery to exit, bound 2) | `wait_free_recovery_to_exit` | `WaitFree.lean` |
| Theorems 1–2, RMRs `O(m)` (DSM; crashes start passages) | `rmr_bound` | `RMR.lean` |
| Theorems 1–2 under the literal passage definition: **false** | `Literal.rmr_literal_unbounded` | `RMRLiteral.lean` |
| Theorem 2 (summary) | `theorem2` | `Main.lean` |

**Not formalized.** The CC-model RMR bound, the worst-case `O(1+f)` RMRs per passage, FCFS without
crashes (all proved only in the full version), and the wait-free `Exit()` variant of Section 3.4.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Self-contained model (Mathlib + CSLib's `SumUpdate` and `Nat.Descent`); CSLib's generic
crash-recovery model (`SharedMemory/Recoverable.lean`) is not used, since the algorithm needs an
explicit program-counter model. The invariant was first checked exhaustively by an explicit-state
model checker on small instances. Non-vacuity: the hypotheses `Fair ∧ FinCrashes` hold for the
round-robin schedule (example in `Spec.lean`); the counterexample executions show that processes
do enter the critical section and that crashes and recoveries happen in the model. CSLib candidates: the generic fairness helpers `Live.NoCrash`,
`Live.follow`, `Live.descent_false` (`LivenessTrace.lean`) and `card_filter_update`
(`InvBasic.lean`).
