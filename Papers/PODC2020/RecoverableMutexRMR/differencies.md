# Differences between the formalization and the paper

Paper: D. Y. C. Chan, P. Woelfel, *Recoverable Mutual Exclusion with Constant Amortized RMR
Complexity from Standard Primitives*, PODC 2020 (DOI 10.1145/3382734.3405736), conference version
(10 pages; proofs of several lemmas and of the RMR bounds are deferred to a full version that we
did not use).

## Statement-level issues in the paper

1. **Theorems 1–2 (RMR bound) are false under the paper's literal definition of a passage
   (⚠️, R3).** The paper defines: "A passage of a process begins when it calls `Enter()` and ends
   when the process crashes or when it finishes its following `Exit()` call", and claims that "in
   any execution in which `m` passages begin" the total number of RMRs is `O(m)`. Read literally,
   the steps of `Recover()` belong to no passage. A single process that calls `Enter()` once,
   reaches the critical section and then crashes in the critical section again and again re-enters
   it through `Recover()` line 20 each time, executing `D.FAI()` (line 15) every time: one passage, unboundedly
   many RMRs (`Literal.rmr_literal_unbounded`, `RMRLiteral.lean`). Line 15 is an RMR in the CC
   model (a non-read operation) for any `n`. The Lean execution has one process and uses our DSM
   charging rule (item 9), which is only an upper bound: with `n = 1` all of memory could sit in
   the process's segment. For the DSM model with `n ≥ 2` the same execution works for any process
   whose segment does not hold `D` (the other processes stay in the remainder section); this
   variant and the CC model are not mechanized. The intended reading is the standard one of
   the RME literature (and the one suggested by the paper's own remark that passages and
   super-passages coincide only in the absence of crashes): every crash ends a passage and the
   recovery starts a new one. With this reading the bound holds; we prove `≤ 25·#Enter() + 76·#crashes`
   in the DSM model (`rmr_bound`), where `#crashes` counts only crashes outside the remainder
   section (a crash in the remainder section has no effect and starts no passage). Decided by R3: the fix is local (the definition of a passage)
   and recoverable from the paper.
2. **Lemma 2.1 (19) (and Lemmas 2.4–2.6) omit the fairness hypothesis (⚠️, R4).** Lemma 2.1 is
   stated for "any run `E`", and (19) only assumes finitely many crashes. Without fairness it is
   false: two processes, no crash; process `false` obtains ticket 1 and grants it to itself
   (`W[false] = (1,true)`), then stops taking steps; process `true` takes ticket 2 and busy-waits
   forever; `Token` stays 0 (`Lemma2_1_19.lemma2_1_19_false`, `Lemma2_1_19.lean`). Lemmas 2.4–2.6
   have the same omission. All of them are used only inside the starvation-freedom proof, where
   fairness holds, so this is a missing implied assumption (R4).

No other statement of the paper that we checked is false.

## Proof-level differences

3. **Lemma 2.1 has no proof in the paper** ("For brevity, some proofs have been omitted"). We prove
   it via a single inductive invariant `Inv` (`InvDefs.lean`, proof in `Inv*.lean`,
   `inv_exec`). The temporal items of Lemma 2.1 are replaced by state predicates:
   * (15)+(6) "`Token` moves past `w` only after the owner of `w` left `(w,true)`" becomes `done`:
     for every `x ≤ Token` claimed by `q`, `W[q]` no longer holds ticket `x`;
   * (16) follows from `grant`: `W[q] = (−,true)` implies `W[q] = (Token+1,true)` and
     `A[Token+1] = q`;
   * (14) becomes `future`: a claimed ticket beyond `Token` is the owner's current ticket, or
     `Token+1` and the owner is in `Exit()` after line 10 on its way to move `Token` (`OnTrack`);
   * the remaining items are local invariants per program counter (`LI`) or follow from them.
   The invariant was first validated by exhaustive explicit-state model checking (2 processes with
   ≤ 4 tickets and ≤ 2 crashes; 3 processes with ≤ 3 tickets and 1 crash).
4. **Lemma 2.3** (`D + |I| − C ≥ 0`): the paper's proof argues backwards in time (no successful
   line-46 CAS between the reading of `C` and the skip). We make it inductive with a per-process
   local invariant at lines 38/46 (`c ≤ d` and `A[ℓ+1] = 0` and the owner of `ℓ+1` in `I` imply
   `Φ ≥ 1`); same argument.
5. **Lemma 2.10** (finitely many `−1` entries; proof omitted in the paper) and the claim of
   Section 3.1 that the number of skipped tickets is at most twice the number of crashes: proved
   through a second potential `Ψ = Φ + #(crash credits) + #(lost tickets)` with ghost variables
   (`psi_bound`, `skipped_le_two_mul_crashes`, `lemma2_10`). Each skip decreases `Ψ` by 1, each
   execution of line 15 increases it by at most 2, and `Ψ ≥ Φ ≥ 0`.
6. **Starvation freedom (Lemma 2.13) and Lemmas 2.4–2.6, 2.8**: the paper's proof structure is
   kept (finitely many skips; a process avoiding rem/cs is eventually stuck at line 31, so Token is
   bounded, hence eventually constant; then the "last `Move_Token()` call" argument). Differences:
   finiteness of the number of calls uses a per-process call potential (needs only Token constant
   and nobody in the CS); the last call may precede the last crash, so the argument starts from the
   last event that is a call or an effective crash; the case `A[L+1] = q` uses a progress lemma for
   the owner of slot `L+1`. Lemmas 2.4–2.6 are not stated separately. See `Liveness*.lean`.
7. **RMR complexity**: the paper defers all RMR proofs to the full version. We give our own proof
   in the DSM model (item 9) by a potential function.

## Modelling choices

8. **Granularity.** One shared-memory operation per step; the local computations following it
   (lines 6–7, 13, 17, 19–21, 27, 32, 37, 39, 43–45, 49, 50) are merged into that step. The
   recursive calls of `Move_Token()` (lines 43, 49) are tail calls and are modelled as a jump back
   to line 34 with the same return address. The invocation of `Enter()` (from the remainder
   section) and of `Exit()` (from the critical section) are separate steps without memory access.
   Merging line 13 into line 12 means a crash between them is not modelled (it would only send the
   process to `Recover()` and then `Enter()`, which is harmless).
9. **RMR model.** Only the DSM model: `W[p]` and `Exit[p]` are in `p`'s segment, every access to
   `C`, `D`, `Token` and `A[·]` counts as an RMR (an upper bound for every placement), invocations
   and crashes cost nothing. The CC model (cache invalidation by the CAS operations of line 40) is
   not formalized. Constants: 25 per `Enter()` invocation, 76 per crash outside the remainder
   section (not optimized). `numCrashes` (also used for the Section 3.1 bound
   `skipped_le_two_mul_crashes`) counts only those crashes.
10. **Crashes.** Any process may crash at any time; a crash outside the remainder section resets
    the program counter (all local variables) and starts `Recover()`; a crash in the remainder
    section has no effect. Shared memory is never affected.
11. **Processes** are an arbitrary finite type `P` with decidable equality (the paper's
    `{1,…,n}`); `A[c]` holds `Slot.empty` (0), `Slot.claimed q` (`q > 0`) or `Slot.skipped` (−1);
    the condition "`p' > 0`" of line 39 is "`A[ℓ+1]` is claimed".
12. **Liveness assumptions.** "Finitely many crashes" = no crash event after some time.
    "Fair" = every process that is outside the remainder section at time `t` takes a step at some
    time `≥ t` (`Fair`); a step in the critical section is the call of `Exit()`. Both hypotheses
    hold for the round-robin schedule (non-vacuity example in `Spec.lean`). Starvation freedom is
    stated as: a process in `Enter()` (resp. `Exit()`, `Recover()`) that does not crash any more
    reaches the CS (resp. the remainder section, leaves `Recover()`); a call interrupted by a
    crash counts as finished, as in the paper's definition of wait-freedom.
13. **Wait-freedom bounds** are stated with explicit constants and own-step counting: critical
    section re-entry within 3 own steps (paper: "4 consecutive shared memory steps"), recovery
    within 3, recovery to `Exit()` within 2 own steps (paper: 3). The "first and last shared memory
    operation of `Exit()`" are lines 9 and 12.
14. **Ghost state** (`Ghost`: ticket owners, `c_{p,t}`, the "has not incremented `D`" flag, crash
    credits, lost tickets, crash counter) is updated alongside the configuration and never read by
    the algorithm (`ghost e t` is defined from `exec e t`).

## Not formalized

* The CC-model RMR bound, the worst-case `O(1 + f)` RMRs per passage, FCFS for crash-free
  executions (all proved only in the paper's full version).
* Section 3.4 (wait-free `Exit()` variant).
* Lemma 2.1 items are not all restated one by one; (3), (4), (7), (8), (9), (10), (11), (16) and
  Lemma 2.3 have separate Lean statements (`Safety.lean`, `Skips.lean`), the others are part of `Inv`.
