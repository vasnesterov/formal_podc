# Composable CRN computation — PODC 2019

Eric E. Severson, David Haley, David Doty. *Composable computation in discrete chemical reaction
networks.* PODC 2019. DOI [10.1145/3293611.3331615](https://doi.org/10.1145/3293611.3331615).
Formalized version: arXiv [1903.02637](https://arxiv.org/abs/1903.02637) v2 (numbering follows it).

**Verdict: ✅ Correct.** Every checked statement holds as written. This covers the 1D
characterization (Theorem 3.1), the impossibility tool (Lemma 4.1) and `max`, the whole sufficiency
direction of the main Theorem 5.2 (Lemmas 6.1, 6.2 with closure under composition), Observations
2.1, 5.3, 9.1 and the leaderless 1D characterization (Theorem 9.2). Two parts are cited or left
unformalized and enter only as hypotheses: Lemma 2.7 (stably computable ⇒ semilinear, cited from
[10]) and the necessity of the eventually-min condition (Theorem 7.1, the long geometric §7).
So the headline Theorem 5.2 is verified only in its "⇐" direction (plus conditions (i) and (iii)
of "⇒"); its hardest part, the necessity of condition (ii), is not checked.

## Mistakes in the paper

No mistakes in the statements.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* Discrete CRNs (`Basic.lean`): finite species type `S`, finite set of reactions `(R, P)`,
  configurations `S → ℕ`, reachability = reflexive–transitive closure of reaction steps. No
  kinetics, no probabilities: stable computation is the paper's reachability definition (from every
  configuration reachable from `I_x`, a stable configuration with output `f x` is reachable).
* A function-computing CRN has distinct input species `X_i` (`i : ι`, any finite index type; the
  paper's `d` is `ι = Fin d`), an output `Y` and a leader `L` (an `Option`: present in the main
  model, absent in §9). `I_x` has `x i` copies of `X_i`, one `L`, nothing else.
* Output-oblivious: `Y` is never a reactant. `ObliviouslyComputable f` quantifies over all
  output-oblivious CRNs with a leader.
* Semilinear function: the graph is a semilinear set in Mathlib's sense (finite union of linear
  sets), equivalent to the paper's Definitions 2.5/2.6.
* Composition (Observation 2.2) uses a transfer reaction `Y^{(k)} → X^{(g)}_k` instead of renaming
  species; this delays the hand-over and changes nothing computed.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Observation 2.1 (oblivious ⇒ nondecreasing) | `ObliviouslyComputable.monotone` | `Impossibility.lean` |
| Observation 2.2 (+ multi-input remark) | `ObliviouslyComputable.comp`, `StablyComputable.comp_oblivious` | `Composition.lean` |
| Theorem 3.1 (1D: oblivious ⇔ semilinear ∧ nondecreasing) | `theorem_3_1` (needs Lemma 2.7 for ⇒), `theorem_3_1_mpr` | `OneDim.lean` |
| Lemma 4.1 (contradiction sequences) | `not_obliviouslyComputable_of_seq` | `Impossibility.lean` |
| `max` semilinear, nondecreasing, not obliviously-computable (§1.2, §4) | `max_isSemilinearFun`, `max_not_obliviouslyComputable` | `Impossibility.lean` |
| Definition 5.1, example `⌊3x/2⌋` (Fig. 3a) | `IsQuiltAffine`, `floor_three_halves_obliviouslyComputable` | `Basic.lean`, `QuiltAffine.lean` |
| Theorem 5.2 (⇐ proved; ⇒ (ii) assumed as Theorem 7.1) | `theorem_5_2` (hypothesis `Theorem71`) | `MainTheorem.lean` |
| Observation 5.3 | `observation_5_3` | `MainTheorem.lean` |
| Lemma 6.1 (quilt-affine ⇒ oblivious) | `lemma_6_1` | `QuiltAffine.lean` |
| Lemma 6.2 (Theorem 5.2 "⇐") | `lemma_6_2` | `MainTheorem.lean` |
| §6 gadgets: `min`, `c(a,b,w)`, `(x−n)⁺`, constants, projections | `obliviouslyComputable_min`, `_add_ite`, `_sub_const`, `_const`, `_proj` | `Gadgets.lean` |
| Observation 9.1 (leaderless ⇒ superadditive) | `LeaderlessObliviouslyComputable.superadditive` | `Impossibility.lean` |
| Theorem 9.2 (1D leaderless: ⇔ semilinear ∧ superadditive) | `theorem_9_2` (needs Lemma 2.7 for ⇒), `theorem_9_2_mpr` | `Leaderless.lean` |

The constructions of Theorem 3.1 and Lemma 6.1 are instances of one generic, once-proved
leader-automaton CRN (`obliviouslyComputable_of_automaton`, `Automaton.lean`). It covers any
function whose finite differences and next state are determined by a finite abstraction of the
input consumed so far.

**Proof remarks.**
* Lemma 4.1 assumes the sequence `(aᵢ)` is increasing; the proof never uses this, and we prove the
  lemma without it.
* Observation 2.2 is stated for one upstream module; Lemma 6.2 needs the "more generally, g can take
  any number of inputs" remark (with fan-out of inputs and one leader per module). We prove that
  general form.

**Not formalized.** Lemma 2.7 (cited), Lemma 2.3, Observation 2.4, Theorem 5.4, §7 (Theorem 7.1)
and §8 (scaling limits); the equivalent fairness/probability-1 semantics of footnote 2.

**Trust.** No `sorry`; the listed theorems use only the axioms `propext`, `Classical.choice`,
`Quot.sound`. Hypotheses are satisfiable: the gadgets, `⌊3x/2⌋` and Lemma 6.1 give concrete
obliviously-computable functions, and `max` is a concrete semilinear nondecreasing function that is
not. The CRN model is paper-local (CSLib candidate); it
does not reuse CSLib's population-protocol framework, which has two-agent interactions and labelled
agents. It overlaps with the vector Petri nets already in the project (`Cslib.PetriNet` in
`Podc/Computability/PetriNets/Rackoff.lean`, the `P → ℕ` nets of `Papers/PODC2022/PPLeadersStateComplexity/`)
and its `Reach` is a plain `Relation.ReflTransGen` rather than `Cslib.TransitionSystem.Reach`; these
should be unified when upstreaming. Mathlib's `IsSemilinearSet` (`Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear`)
provides semilinear sets.

**CSLib candidates.** `Basic.lean` (CRN model and stable function computation), `Automaton.lean`
(leader-automaton construction), `Composition.lean` (composition of output-oblivious CRNs).
