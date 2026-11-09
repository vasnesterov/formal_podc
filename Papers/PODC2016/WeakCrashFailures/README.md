# Weak Crash Failures — PODC 2016

Gadi Taubenfeld. *Brief Announcement: Computing in the Presence of Weak Crash Failures.* PODC 2016. DOI
[10.1145/2933057.2933058](https://doi.org/10.1145/2933057.2933058). Formalized version: the author's full version
*Weak Failures: Definitions, Algorithms and Impossibility Results* (2018, 15 pp.,
faculty.runi.ac.il/gadi/MyPapers/2018T-WeakFailures.pdf); no open copy of the 3-page brief announcement was found. The
full version states the announcement's results (consensus with one `(n−1)`-failure, k-set consensus with `ℓ+k−2`
`(n−ℓ)`-failures, the matching impossibilities) with full proofs; numbering and the quoted text below follow it.

**Verdict: ✏️ Slip.** All results hold. The consensus algorithm of Fig. 1 tolerates one crash `(n−1)`-failure for
every `n ≥ 2`. The k-set consensus algorithm of Fig. 2 tolerates `ℓ+k−2` crash `(n−ℓ)`-failures. Theorem 7 and its
corollaries hold. The only problems are degenerate cases (`n = 1`) and a carelessly worded definition in the
appendix. Some hypotheses are stronger than needed.

## Mistakes in the paper

### ✏️ Slips
- **Theorem 1 at `n = 1`.** Theorem 1 says "for every `n ≥ 1`", but the algorithm of Fig. 1 violates validity at
  `n = 1`. The single process passes the line-7 test `counter = n−1 = 0` at once and decides the initial value `0`
  of `max`, whatever its input (`fig1_invalid_n1`). §1.3 states the result for `n > 1`, and for `n = 1` the
  statement itself is trivially true by "decide your own input" (`selfDecide_wSolves`).
- **Corollary 2 at `n = 1`.** Corollary 2 ("for every `0 ≤ ℓ < n/2`") is false for `n = 1`, `ℓ = 0`: one process
  deciding its own input tolerates one crash 1-failure (`corollary2_false_n1`). It holds for `n ≥ 2`
  (`corollary2_paper`).
- **Two `(n−1)`-failures at `n = 2`.** The sentence after Corollary 2 ("no consensus algorithm can tolerate two
  crash `(n−1)`-failures") needs the bound `n > 2` given in §1.3. For `n = 2` both processes cannot be faulty, so two
  1-failures are the same failure pattern as one (`weakAdmissible_iff_of_card_two`), which Fig. 1 tolerates.
- **Appendix, k-deadlock-freedom.** The literal definition ("if fewer than `k` processes fail, then if a process is
  trying, some process eventually enters") cannot be met if the only trying process then crashes. The intended
  reading, used in our model, requires the trying process itself not to be delayed (`Fig2.DF`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- *Executions and failures* (`Failures.lean`). An execution is an infinite schedule `σ : ℕ → P` (`σ t` takes step
  `t`), as in CSLib's SWMR model. A process is correct iff it takes infinitely many steps. A process that decided
  keeps taking no-op steps, so participation is required.
- *Weak failures.* The point contention at time `t` is the number of processes that have taken a step before `t`;
  it never decreases. An *m-failure (type 1)* (`WeakFailure m σ p`) is a process that stops at a time when the
  contention is `≤ m`. "At most `f` crash m-failures" is `WeakAdmissible m f σ`. With `m ≥ n` these are ordinary
  crashes (`weakFailure_iff_faulty`). An initial failure is an m-failure for every `m`. Type-2 failures are not used
  by the paper's results and are not modelled.
- *Fig. 1* (`Fig1Model.lean`). Asynchronous, `n` processes, atomic multi-writer registers `state`, `input` (with
  arbitrary initial values) and `decision`, inputs in `ℕ`. One shared access per step. Two consecutive reads of
  `decision` (lines 13–14, 22–23) are merged into one; this only removes stuttering. Safety holds for every schedule
  and every failure pattern. Termination is proved under `WeakAdmissible (n−1) 1`.
- *Fig. 2* (`Fig2.lean`). The atomic snapshot `Flag` and the register `decision` are atomic objects. The cited
  exclusion objects `EX[1]` (mutex) and `EX[2]` (`(k−1)`-exclusion) are modelled by their specification: at most
  `cap` entries is built into the step, and deadlock-freedom is a hypothesis `DF` on executions. The two parallel
  threads of line 7 (entry code and the `decision` check) are scheduled fairly (`Fair`). So Theorem 4 holds for any
  exclusion objects meeting the specification. Their register implementations and the snapshot construction are
  cited, not formalized.
- *Section 5* (`Impossibility.lean`). The model is CSLib's asynchronous read/write SWMR model `Cslib.SWMR` (any
  deterministic algorithm, single-writer registers). Since multi-writer registers can be built from single-writer
  ones, this matches "using registers" up to that classical simulation, which is not formalized. The
  Borowsky–Gafni / Herlihy–Shavit / Saks–Zaharoglou k-set impossibility is a hypothesis (`KSetImpossible`), stated
  for the value set `V` at hand. It holds classically when `V` has more than `k` values (the paper's "some domain");
  for `|V| ≤ k` it is false (decide your own input), so Theorem 7 and Corollary 1 are meant for such `V`. For
  `k = 1` it is proved from the FLP/Loui–Abu-Amara theorem in `Podc/.../SWMR/FLP.lean`, so Corollary 2 is
  unconditional.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (`n ≥ 2`) | `Fig1.theorem1` | `Fig1Main.lean` |
| Lemmas 3, 4, Theorem 2 (agreement, validity) | `Fig1.theorem2_agreement`, `Fig1.theorem2_validity` (invariant `Fig1.Inv`, `Fig1.inv_exec`) | `Fig1Safety.lean` |
| Lemmas 1, 2 | `Fig1.lemma2` | `Fig1Live.lean` |
| Theorem 3 (termination) | `Fig1.theorem3` | `Fig1Live.lean` |
| Theorem 1 fails for Fig. 1 at `n = 1` | `Fig1.fig1_invalid_n1` | `Fig1Safety.lean` |
| Lemma 5, 6, 7, 8 | `Fig2.lemma5`, `Fig2.lemma6`, `Fig2.lemma7`, `Fig2.lemma8` | `Fig2.lean` |
| Theorem 5 (termination) | `Fig2.theorem5` | `Fig2.lean` |
| Theorem 6 (k-agreement, validity) | `Fig2.theorem6` | `Fig2.lean` |
| Theorem 4 | `Fig2.theorem4` (paper's hypotheses), `Fig2.theorem4'` (weaker) | `Fig2.lean` |
| Theorem 7 | `theorem7` | `Impossibility.lean` |
| Corollary 1 | `corollary1` | `Impossibility.lean` |
| Corollary 2 | `corollary2`, `corollary2_paper`, `no_consensus_two_failures` | `Impossibility.lean` |
| Corollary 2 fails at `n = 1` | `corollary2_false_n1` | `Impossibility.lean` |

*Remarks (not mistakes).*
- Theorem 3 holds for every `n`.
- Theorem 4 does not need `n ≥ 2ℓ+k−2`, nor `ℓ ≥ 1`: termination needs only `ℓ + k ≥ 2` and k-agreement needs `k ≥ 1`
  (`Fig2.theorem4'`). The bound is used only in Lemma 8, which the termination proof does not need.
- Corollary 1 holds for `n > ℓ + k` instead of `n > 2ℓ + k`, because initial failures are `(n−ℓ)`-failures. Theorem 7
  does not need `k ≥ 1`.
- Both readings of "participating" (a terminated process stays participating, or stops) give the same results for
  Fig. 1. Once a process terminates, `decision ≠ ⊥`, and every correct process then decides
  (`Fig1.eventually_done_of_dec`).
- Termination proofs, beyond the paper's sketches. The Fig. 1 proof uses levels and ranks in the code
  (`Fig1Ranks.lean`) and a "doomed process" invariant (`DoomedR`), which also gives Lemma 1. For Fig. 2,
  deadlock-freedom of `EX[2]` only yields "some process enters". The step "a correct process enters" needs a repeated
  application: entrants that crash are delayed forever, there are fewer than `k−1` of them, so infinitely many entries
  would follow.

**Not formalized.** The cited register implementations of atomic snapshots and of `ℓ`-exclusion; the k-set
consensus impossibility for `k ≥ 2` (hypothesis); the simulation of multi-writer by single-writer registers; the
motivation in §1 and the open problems in §7.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `Fig1.skipZero_admissible` gives a schedule with exactly one crash `(n−1)`-failure (an initial failure).
`Fig2.df_of_eager` shows eager exclusion objects satisfy `DF`. `Fig2.roundRobin_hyps` gives a fair failure-free
execution satisfying all hypotheses of Theorem 5. Section 5 builds on CSLib's SWMR model (`Podc/.../SWMR/`,
`Restrict.lean`, `FLP.lean`). The Fig. 1 invariant and termination claim were first validated with an exhaustive
model checker for `n ≤ 3`.
