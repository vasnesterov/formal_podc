# Message Adversaries vs Failure Detectors — PODC 2013

Michel Raynal, Julien Stainer. *Synchrony Weakened by Message Adversaries vs Asynchrony Restricted by
Failure Detectors.* PODC 2013. DOI [10.1145/2484239.2484249](https://doi.org/10.1145/2484239.2484249).
Formalized version: the full version, IRISA research report PI 2002 (*Round-based Synchrony Weakened by
Message Adversaries vs Asynchrony Enriched with Failure Detectors*, hal-00787978v2, Feb. 2013); numbering
follows it. Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🚨 Headline claim false.** With the paper's own definition of solving a task in the synchronous
model (every process outputs), the QUORUM characterization of Σ is false: a three-process task is solvable
in `AMP[fd: Σ]` but not in `SMP[adv: QUORUM]` (Theorem 4, Lemma 6, Theorem 5). The SOURCE + TOUR
characterization of Ω (Theorem 2, Lemma 2, Corollary 1) fails in the same way. The simulations of the
asynchronous models in the synchronous ones leave weakly correct processes without output, and the
converse simulations need exactly those outputs, so no reading of "solve" saves all lemmas. Theorem 1,
Theorem 6 and the facts about strongly correct processes hold.

## Mistakes in the paper

### 🚨 Theorem 4 and Lemma 6 (QUORUM characterizes Σ)
The task `Tseen` ("of `p₁, p₂` each outputs `alone` or both inputs, and at least one outputs both") is
solvable in `AMP_{3,2}[fd: Σ]` but not in `SMP_3[adv: QUORUM]` (`lemma6_false`, `theorem4_false`).

**Impact.** One of the paper's two new characterizations is false, and so is Theorem 5 (`SOURCE, QUORUM ≃
Σ, Ω`, `theorem5_false`). Lemma 5 (the other inclusion, not formalized) is not affected.

**Details.** In `SMP_3`, let only `p₃`'s messages be delivered, every round, to everybody. Every two
in-neighbourhoods contain `p₃` and `p₃` is strongly correct, so QUORUM holds (SOURCE too). The processes are
reliable, so `p₁` and `p₂` must output (Section 2.4: "if no value is computed by `p_j`, it is because
`p_j` has crashed"; Section 2.3: `SMP_n` is "made up of reliable processes"); neither ever learns the other's input, so both must answer `alone`
(`tseen_not_solvable`). In `AMP_{3,2}[fd: Σ]`, `p₁` and `p₂` write their input to a Σ-quorum and then read
from a Σ-quorum (ABD); quorum intersection makes one of them see the other (`tseen_solvable_amp_sigma`,
a complete proof in the CHT model).

The proof of Lemma 6 fails at its last step: the simulation of Figure 7 stops the weakly correct
simulators, which are reliable synchronous processes that must output. Here `p₁` and `p₂` are weakly
correct and the simulation never gives them an output.

### 🚨 Theorem 2 and Lemma 2 (SOURCE + TOUR characterizes Ω in ARW)
Consensus between `p₁` and `p₂`, with `p₃` as a helper whose output is free (`Tcons`), is solvable in
`ARW_{3,2}[fd: Ω]` but not in `SMP_3[adv: SOURCE, TOUR]` (`lemma2_false`, `theorem2_false`).

**Impact.** The SOURCE + TOUR characterization of `ARW[Ω]` is false, and so is Corollary 1 (which adds
the TP and PAIRS variants via Theorem 6; `corollary1_false`). The other inclusion (Lemma 1, not formalized) is not affected.

**Details.** Take the patterns in which `p₃` sends to everybody and hears nobody, while between `p₁` and
`p₂` the adversary delivers one or both messages each round. They satisfy SOURCE (`p₃`), TOUR and even
QUORUM. `p₃` never learns anything, so `p₁` and `p₂` are in a two-process TOUR system. A Santoro–Widmayer
bivalence argument then shows they cannot agree (`tcons_not_solvable`). In `ARW[Ω]` all three processes run
an Ω-based consensus with commit-adopt rounds; `p₃` proposes an input it has read (`tcons_solvable_arw_omega`).

As for Lemma 6, the proof of Lemma 2 says weakly correct simulators "simulate a faulty process", which is
not allowed for reliable synchronous processes.

### ❌ Figure 1 and Conclusion (hierarchy of adversaries)
The arrows `SMP[adv: QUORUM] → SMP[adv: TOUR]` and `SMP[adv: SOURCE, QUORUM] → SMP[adv: SOURCE, TOUR]` ("the
first model is stronger"), the first of which the Conclusion repeats, are false.

**Impact.** `Tseen` is solvable in `SMP_3[adv: TOUR]` in one round but not in `SMP_3[adv: SOURCE, QUORUM]`
(`not_quorum_stronger_than_tour`, `not_source_quorum_stronger_than_source_tour`). This is a purely
synchronous fact, independent of any failure-detector model.

### ⚠️ Theorem 3 (SOURCE characterizes Ω in AMP)
Unestablished: Lemma 4's simulation (Figure 5) never gives an output to weakly correct processes, and under
the other reading of "solve" (only strongly correct processes must output) Lemma 3's simulation (Figure 4)
breaks instead, since it deletes every message except the leader's, making every other process weakly
correct.

**Impact.** We found no counterexample (the counterexamples above do not apply, since `Tseen` and `Tcons`
are not solvable in `AMP[Ω]`); the statement is neither proved nor refuted.

**Details.** The same inconsistency affects all six lemmas. Lemmas 2, 4 and 6 (asynchronous → synchronous)
treat weakly correct processes as crashed. That is valid only if they need not output. Lemmas 1, 3 and 5
(synchronous → asynchronous) need correct asynchronous processes to output, and their simulated
processes may be weakly correct (Figures 2, 4, 6: for instance with Σ constantly `{ℓ}` in Figure 6). The
paper never defines task solvability in `SMP` other than in Section 2.4, where only crashed processes may
lack an output. For `SMP[adv: ∞]` both readings agree (`solvable_inf_iff_local`, `solvableSC_inf_iff_local`).

### ⚠️ Theorem 3 and Lemma 6 (the property FAIR)
Theorem 3 is stated for `SMP[adv: SOURCE, FAIR]` and Lemma 6 for `SMP[adv: FAIR, QUORUM]`, but FAIR is
defined nowhere.

**Impact.** A leftover from an earlier version: the titles, Figure 1, the introduction, Lemmas 3 and 4,
and Theorem 4 all use SOURCE and QUORUM alone. We read the statements without FAIR.

### Typos and slips
- Figures 4 and 6, line 5: `r ← r_i + 1` should be `r_i ← r_i + 1`. Figure 7, line 9: `∈` should be `⊆`.
- Lemma 2, Part 4: `(r, s)`, `(r, j)` for the pairs `(s, r)`, `(j, r)` of `missed_i`. The proof of Lemma 4
  stops mid-sentence ("It follows that").
- Appendix A.3, Part 2: the heading "The source of SMP[SOURCE_pairs, PAIRS]…" should read SOURCE_tp, TP.
- QUORUM's liveness part `SC ≠ ∅` follows from its intersection part (`SC_nonempty_of_inter`), as the
  proof of Lemma 5 shows.

## Proof gaps (statements true)

### 🛠️ Theorem 6, Part 2 (2n−3 rounds of TP simulate one round of TOUR)
The counting chain ends with "`|K_i ∩ K_j| ≥ n−1`, hence `{i, j} ∩ K_i ∩ K_j ≠ ∅`", which skips the key step.

**Impact.** Statement true (`theorem6`).

**Repair.** If neither process knows the other's message, `K_i ∩ K_j ⊆ Π ∖ {i, j}`, which has `n − 2`
elements: a contradiction (`card_fwd_add_card_fwd`, `tp_journey`).

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
- `SMP_n[adv: AD]` (`Model.lean`): CSLib's heard-of model. `n` reliable processes run synchronous rounds.
  An adversary is a set of patterns `p : ℕ → Graph P`, so eventual properties are allowed, and properties
  combine by intersection. TOUR, SOURCE, QUORUM, TP, SOURCE_tp, PAIRS and SOURCE_pairs are taken literally.
  Algorithms are deterministic and full-information, with write-once outputs; this is no loss for
  solvability.
- Strongly correct processes `SC` are literally Section 2.2's definition (the unique source component of
  `⇝∞`, else `∅`).
- Tasks follow Section 2.4. `Solvable`: every process outputs, which is the paper's definition.
  `SolvableSC`: only strongly correct processes must output; this is the reading the proofs of Lemmas 2,
  4 and 6 use.
- `AMP_{n,n−1}[fd: D]` (`Async.lean`) is the staged CHT model (crash failures, at least one correct
  process, reliable non-FIFO links, broadcast steps) with inputs in the initial state. Σ is
  `Cslib.FailureDetectors.SigmaFD` (`Podc/…/FailureDetectors/Sigma.lean`), and `(Σ, Ω)` is a pair of
  histories.
- `ARW_{n,n−1}[fd: Ω]` (`ArwOmega.lean`) has SWMR atomic registers, an infinite schedule (correct = steps
  infinitely often) and an Ω history that is arbitrary until it stabilizes on a correct leader.
- Deterministic algorithms, no randomness; the synchronous adversary is non-oblivious.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Section 2.2: `⇝∞` preorder; `SC` = processes reaching everybody | `InfReach.trans`, `SC_eq` | `StronglyCorrect.lean` |
| Lemma 2, Part 2 / Lemma 4 / Lemma 5 / Lemma 6 (A), (B): facts on `SC` | `SC_nonempty_of_tour`, `mem_SC_of_source`, `SC_nonempty_of_inter`, `eventually_no_edge_into_SC`, `exists_SC_hears_of_quorum` | `StronglyCorrect.lean` |
| Theorem 1 (holds) | `theorem1` (= `solvable_inf_iff_local` + `amp_solvable_iff_local`); weak reading `solvableSC_inf_iff_local` | `Refutations.lean`, `Theorem1.lean`, `AsyncLocal.lean` |
| Lemma 2 / Theorem 2 / Corollary 1 (false) | `tcons_not_solvable`, `tcons_solvable_arw_omega`, `lemma2_false`, `theorem2_false`, `corollary1_false` | `Counterexample.lean`, `ArwOmegaCons.lean`, `Refutations.lean` |
| Lemma 6 / Theorem 4 (false) | `tseen_not_solvable`, `tseen_solvable_amp_sigma`, `lemma6_false`, `theorem4_false` | `Counterexample.lean`, `SigmaSeen.lean`, `Refutations.lean` |
| Theorem 5 (false) | `theorem5_false` | `Refutations.lean` |
| Figure 1 / Conclusion hierarchy (false) | `not_quorum_stronger_than_tour`, `not_source_quorum_stronger_than_source_tour` | `Counterexample.lean` |
| Theorem 6 (holds), Afek–Gafni variants | `theorem6`, `solvable_sourceTour_iff_tp`, `solvable_sourceTour_iff_pairs`, `solvable_tour_iff_tp`, `solvable_tour_iff_pairs` | `TourVariants.lean` |
| Block simulation of synchronous models | `solvable_of_blockPat` | `BlockSim.lean` |

**Not formalized.** Lemmas 1, 3 and 5 (the simulations of Figures 2, 4 and 6; their proofs look right
under the paper's reading of "solve"), Theorem 3, Appendix B (Ω_k), and the Remark after Theorem 2.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`, `Quot.sound`.
Non-vacuity: `tcons_solvable_none` (`Tcons` is solvable without an adversary), `const_mem_SigmaFD`,
`tseen_amp_sigma_nonvacuous` (the `Σ` algorithm for `Tseen` has admissible runs with a valid `Σ` history,
via the generic `AlgAMP.exists_admissible_const`), and
the counterexample patterns are shown to satisfy the adversary properties (`pat_N3_subset`, `pSrc_mem`).
Builds on CSLib's heard-of model and journeys (`Cslib.HeardOf`, `Cslib.DynNet.Journey`, `Chain`) and the
staged CHT failure-detector model. `AsyncLocal.lean` imports the run-construction tools
`Papers/PODC2015/WeakestFDEventualConsistency/RunTools.lean` (`policyRun`, `sim`) of another paper; these,
together with `sim2` and the fair schedules `schedRun` of `AsyncLocal.lean`, are generic facts about the
staged CHT model and would be better placed in `Podc/Computability/Distributed/MessagePassing/FailureDetectors/`.

**CSLib candidates.** `Cslib.FailureDetectors.SigmaFD` / `trivialFD` (staged in
`Podc/Computability/Distributed/MessagePassing/FailureDetectors/Sigma.lean`); the non-oblivious adversary
layer with strongly correct processes (`Model.lean`, `StronglyCorrect.lean`); the generic block simulation
`solvable_of_blockPat` (`BlockSim.lean`); `SolvableAMP.of_map` (`Refutations.lean`).
