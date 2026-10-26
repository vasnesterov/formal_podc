# All Byzantine Agreement Problems Are Expensive — PODC 2024

Pierre Civit, Seth Gilbert, Rachid Guerraoui, Jovan Komatovic, Anton Paramonov, Manuel Vidigueira. *All Byzantine
Agreement Problems Are Expensive.* PODC 2024. DOI [10.1145/3662158.3662780](https://doi.org/10.1145/3662158.3662780).
Formalized version: arXiv:2311.08060v2 (numbering follows it). Companion of *On the Validity of Consensus* (PODC 2023,
[ValidityConsensus](../../PODC2023/ValidityConsensus)).
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: ⚠️ Minor statement issues.** The main result holds: every non-trivial Byzantine agreement problem needs
`Ω(t²)` messages, even in synchrony (the paper proves the weak-consensus bound even against omission faults; we
also get the omission version for every non-trivial problem). We prove it for every `t < n` with the
explicit bound `t² ≤ 32 · #messages`, with or without signatures. The solvability characterization (Theorem 4) is
proved too, but **Lemma 10 and the unauthenticated half of Theorem 4 are false in the degenerate case `n = 2,
t = 1`**. We prove corrected versions.

## Mistakes in the paper

- **Lemma 10 and Theorem 4 (unauthenticated) fail for `n = 2`, `t = 1` (false in a degenerate case).** Lemma 10
  says an unauthenticated-solvable problem with `n ≤ 3t` is trivial. Theorem 4 says a non-trivial problem is
  unauthenticated-solvable iff CC holds and `n > 3t`. Both rest on the cited FLM-style fact that weak consensus needs
  `n > 3t`. With two processes and one fault, every faulty execution has a single correct process, so Agreement
  constrains only fault-free executions. "Exchange proposals; decide the common value if they agree, a default
  otherwise" therefore solves weak consensus, a non-trivial problem, and the same idea solves interactive
  consistency. The FLM argument needs three non-empty groups of size `≤ t`, i.e. `n ≥ 3`. Corrected statements:
  Lemma 10 holds for `3 ≤ n ≤ 3t`. A non-trivial problem is unauthenticated-solvable iff CC holds and (`n > 3t` or
  `n ≤ 2`). The lower bound and the authenticated half of Theorem 4 are unaffected. (`lemma10_counterexample`,
  `theorem4_unauth_as_stated_false`, `trivial_of_solvableSync`, `theorem4_unauth'`)
- **Lemma 1 is proved only for `t ≥ 8` divisible by 8** (the "without loss of generality" step). For other `t`, the
  group sizes `t/4` and `t/2` must be rounded, and `t = 1` admits no group of size `≥ 1` of the required kind. We
  prove a parametric bound (`⌈β/2⌉·σ` messages) and choose parameters for every `t`. For `t = 1` we add a separate
  zero-message argument: without any messages each process decides as in isolation, which contradicts Agreement in
  a mixed fault-free execution. (`omission_lower_bound`, `omission_lower_bound_sq`, `one_message`)
- **Algorithm 1 (Lemma 6) needs lock-step rounds.** It assumes that a fault-free execution is determined by the
  proposals. That fails if the adversary may choose delays in `[0, δ]` with `δ > 0`. This is harmless: the paper's
  model is lock-step, and we prove Theorem 3 directly in the omission model for every `δ`.
- **Minor.**
  - The proof of Theorem 5 assumes "without loss of generality `n = 2t`"; we prove it for every `n ≤ 2t`.
  - "Without loss of generality, the default is 1" before Lemma 4 is made explicit.
  - As in the 2023 paper, "Γ is computable" requires the algorithm to be computable.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- **Synchrony.** The shared partially synchronous Byzantine model, restricted to runs with `gst = 0`. Delays lie in
  `[0, δ]`; `δ = 0` is the paper's lock-step round model.
  - `n` deterministic processes, at most `t < n` statically Byzantine, authenticated links.
  - Optional ideal signatures (unforgeable tokens). Every lower bound is proved with signatures.
  - The lower bounds hold for every `δ`; Algorithm 1 is stated for `δ = 0`.
- **Omission model.** A lock-step execution is the inputs plus a set of omitted message batches. A fault set is
  admissible if every omitted batch has an endpoint in it, so the paper's `swap_omission` (Lemma 15) is just
  another admissible fault set for the same execution. Omission executions are simulated by Byzantine runs, so the
  omission lower bounds transfer.
- **Message complexity.** Messages sent by correct processes to *others* from time 0. Omitted messages count, and
  self-messages do not. Results are stated as "some valid run has `≥ …` messages within finite time".

**Main results in Lean** (namespace `AllBAExpensive`).

| Paper | Lean | File |
|---|---|---|
| Lemmas 2–5, 16 (isolation, merging, chain) | `lemma2`, `lemma3`, `chain`, `merge_st` | `WeakLowerBound.lean` |
| **Lemma 1 / Theorem 2** (weak consensus, `t² ≤ 32·msgs`) | `omission_lower_bound_sq`, `weak_consensus_lower_bound_auth` | `LowerBound.lean` |
| Lemma 7 (containment) | `containment_auth` | `Containment.lean` |
| Algorithm 1, Lemma 6 (reduction to weak consensus) | `weakReduction_solves` | `Reduction.lean` |
| **Theorems 1 and 3** (every non-trivial problem) | `message_lower_bound_auth`, `message_complexity_lower_bound_auth`, `message_lower_bound_om` | `LowerBound.lean` |
| Corollary 1 (External Validity) | `external_validity_lower_bound` | `LowerBound.lean` |
| Lemma 8, Algorithm 2, Lemma 9 (CC necessary and sufficient) | `containmentCondition_of_solvesConsensusAuthSync`, `solvesConsensusAuthSync_reduction` | `Solvability.lean` |
| **Lemma 10** (corrected); counterexample | `trivial_of_solvableSync`; `lemma10_counterexample`, `ic2_solves` | `Theorem4.lean`, `Solvability.lean` |
| **Theorem 4** (auth; corrected unauth; refutation) | `theorem4_auth'`, `theorem4_unauth'`, `theorem4_unauth_as_stated_false` | `Theorem4.lean` |
| Theorem 5 (strong consensus, `n ≤ 2t`) | `strongValidity_not_solvableAuthSync` | `Solvability.lean` |
| PODC 2023 Thm. 4 follows (up to the constant) | `message_lower_bound_psync` | `Theorem4.lean` |

**Cited results proved, not assumed.** Theorem 4 is unconditional because the cited ingredients are proved:
- FLM impossibility of weak consensus for `3 ≤ n ≤ 3t` (`Cslib.Byzantine.PartialSync.weakValidity_not_solvableSync`);
- interactive consistency with signatures for every `t`, via parallel Dolev–Strong broadcasts
  (`icSolvableAuthSync_dolevStrong`);
- interactive consistency without signatures for `n > 3t`, via the verified vector consensus of the 2023
  formalization (`icSolvableSync_of_three_t_lt`).

These protocols are not the cited ones, and their message complexity is not analysed.

**Not formalized.** Related work and the conclusion; the randomized-setting remarks; the complexity of the cited
protocols.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`. The
synchronous and omission models, FLM, Dolev–Strong and IC live in CSLib,
`Cslib/Computability/Distributed/Byzantine/PartialSync/`. Shared library (`Cslib/Computability/Distributed/Byzantine/PartialSync/`): Algorithms 1 and 2 are
input/decision maps `Algorithm.comapInput`/`Algorithm.mapDecide` (`Map.lean`); Definition 3 and Lemma 9 are
`ValidityProperty.ContainmentCondition` and `.solvableSync`/`.solvableAuthSync` (`Containment.lean`, also used by
*BA with Predictions*); the fault-free executions `ffExec`/`ffRun` are `OmExec.ff`/`Run.quiet ∅` (`Omission.lean`,
`Runs.lean`; `isoExec_empty` relates `ffExec` to `isoExec`); the computable `Γ` comes from `Computable.lean`.
