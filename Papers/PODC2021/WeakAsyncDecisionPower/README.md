# Decision Power of Weak Asynchronous Models — PODC 2021

Philipp Czerner, Roland Guttenberg, Martin Helfrich, Javier Esparza. *Decision Power of Weak Asynchronous
Models of Distributed Computing.* PODC 2021. DOI
[10.1145/3465084.3467918](https://doi.org/10.1145/3465084.3467918). Formalized version: arXiv
[2102.11630](https://arxiv.org/abs/2102.11630) v2 (full version with appendix); numbering follows it.
Copy of the paper: [paper.pdf](paper.pdf).

**Verdict: 🛠️ Proof repaired.** All the impossibility results of Section 3 hold: Lemmas 3.1, 3.2, 3.4 and
3.5 and Corollaries 3.3 and 3.6. We prove each of them directly for all three selection constraints
(liberal, exclusive, synchronous). The paper's proofs of 3.1, 3.2 and 3.4 do not work for exclusive
selection as written, and fall back on the selection-independence theorem of Esparza–Reiter. The explicit cutoff in the proof of Lemma 3.5 is not
justified by the argument (the lemma only claims existence). The rest is small slips. Sections 4–6 (the expressiveness characterization) are not formalized.

## Mistakes in the paper

No statement is wrong. Points worth knowing:

* **Exclusive selection is handled by citation, not by the proofs (Lemmas 3.1, 3.2, 3.4).** The paper
  says it "generally assumes exclusive selection". Yet:
  * the proofs of Lemmas 3.2 and 3.4 run the automaton synchronously (as a `DA$` automaton);
  * the proof of Lemma 3.1 selects all copies of the nodes chosen by ρ_G and ρ_H at the same time.

  None of these is an exclusive schedule. For exclusive selection the proofs therefore rely on the
  theorem of [16] that the selection constraint does not affect decision power. That theorem relates
  classes of automata, so on its own it does not give the explicit cutoff `β + 1` of Lemma 3.4 for an
  exclusive automaton. We prove all three lemmas directly for every selection constraint:
  * Lemma 3.1 alternates G-steps and H-steps. Every lifted selection is then the set of copies of a
    single node, which is independent and can be executed one node at a time. Sequentialising the
    paper's simultaneous selection would also work, since it only changes states at the junction
    nodes, which the distance argument already discards.
  * Lemma 3.2 executes the fibre `f⁻¹(v)` one node at a time.
  * Lemma 3.4 uses stars instead of cliques, with the schedule "all leaves (one at a time), then the
    centre".

  This gives Lemma 3.4 with the cutoff `β + 1` for exclusive selection too.
  (`lemma_3_1`, `lemma_3_2`, `lemma_3_4`)
* **Lemma 3.5: unjustified explicit constant.** The proof shows that adding a leaf with label `q` preserves
  acceptance when `L_G(q) ≥ (m−1)|Q| + 2`, which is what the pigeonhole step needs. It then concludes
  that "`K := m(|Q|−1) + 2` is a valid cutoff". This value is smaller than `(m−1)|Q| + 2` whenever
  `m > |Q|`, so the argument does not justify it. The lemma only claims that some `K` exists, so it
  is unaffected. We use `K = B + 3` with `B = max(m_Y, m_N)·|Q| + 1` (`lemma_3_5`).
* **Lemma 3.5 needs stable *acceptance* as well.** "An analogous argument shows that the same holds
  for acceptance" requires a second cutoff `m'`, for the set of configurations that can reach a
  non-accepting configuration. We take `max(m, m')`.
* Typos and small slips:
  * In Lemma 3.4's induction step, "`⌈Q_{G(t+1)}⌉_β`" should be `⌈·⌉_{β+1}`.
  * In Lemma 3.2's proof, "`C_t(v) = C_t(f(v))`" should be `C'_t(v) = C_t(f(v))`.
  * In Lemma 3.5's proof, "the fact that `MinPre*(C)` is upward-closed" should read `Pre*(C)`.
  * In Lemma 3.5's proof, states and labels are identified ("`L_G(q)`" for a state `q`).
  * The definition of a covering does not say that `H` must be connected and have at least three
    nodes. This is implicit in the graph convention.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model** (`Podc/Computability/Distributed/DistributedAutomata/`, staged for CSLib).
* **Input graphs.** `LGraph Λ` is a finite labelled simple graph. `Admissible k` encodes the paper's
  convention (connected, at least 3 nodes) plus a degree bound `k : ℕ∞`, where `k = ⊤` means
  arbitrary graphs.
* **Machines.** A `Machine` has a counting bound `β ≥ 1`. Its transition function `δ q N` is applied
  to neighbourhood counts cut off at `β` (`view`). It has accepting and rejecting states `Y`, `N`.
  `Halting` means that `Y ∪ N` is absorbing.
* **Steps and schedules.** In `step`, the selected nodes move simultaneously. A schedule is
  `ℕ → Set V`.
* **Selection and fairness.** The selection constraint is liberal, exclusive or synchronous. Fairness
  is adversarial or pseudo-stochastic, exactly as in §2: every node is selected infinitely often, and
  under pseudo-stochastic fairness every finite sequence of permitted selections occurs infinitely
  often.
* **Acceptance.** Acceptance is by stable consensus. `Consistent k` is the consistency condition on
  admissible graphs. `Accepts` means that some fair run accepts. `IsLabelling` means that the decided
  property depends only on label counts.
* **Classes.** The classes `xyz` appear as hypotheses: `M.β = 1` (d), `M.Halting` (a),
  `A.fair = .adversarial` (f). Where the proof allows it, a theorem is stated without the
  hypothesis, which makes it stronger:
  * Lemma 3.1 holds for every halting automaton (any `β`, any fairness), which covers `DaF`.
  * Lemma 3.5 holds for every non-counting automaton (any fairness), which covers `dAF` and `dAf`.
  * Every result holds for all three selection constraints.

  The paper's reduction to one selection type ([16]) is not needed and not formalized.
* **States.** `Q` need not be finite except in Lemma 3.5 and Corollary 3.6. There it must be finite,
  and a `Type`.

**Main results in Lean** (namespace `Podc.WeakAsyncDecisionPower`).

| Paper | Lean | File |
|---|---|---|
| Lemma 3.1 (halting ⇒ all cyclic graphs alike) | `lemma_3_1` | `Halting.lean` |
| Lemma 3.2 (adversarial ⇒ coverings alike) | `lemma_3_2`, `IsCovering` | `Covering.lean` |
| Corollary 3.3 (`L` vs `λL`, also for degree `≤ k`, `k ≥ 2`) | `corollary_3_3` | `Covering.lean` |
| Lemma 3.4 (DAf: cutoff `β + 1`) | `lemma_3_4` (via `star_cutoff`) | `Cutoff.lean` |
| Lemma 3.5 (dAF: some cutoff) | `lemma_3_5` (via `star_add_leaf`, `reach_stable_extend`) | `NonCounting.lean` |
| Lemma 3.5, claim (2) (Dickson, finitely many minimal elements) | `exists_cutoff_of_upward_closed`, `starLE_pwo` | `Dickson.lean` |
| Lemma 3.5, "rejects iff a stably rejecting configuration is reachable" | `accepts_iff_reach_stablyIn`, `not_accepts_iff_reach_stablyIn` | `NonCounting.lean` |
| Corollary 3.6 (no DAf/dAF automaton decides majority) | `corollary_3_6` | `Majority.lean` |

**Shared infrastructure** (`Podc/Computability/Distributed/DistributedAutomata/{Basic,Simulation,Fairness}.lean`,
namespace `Cslib.DistributedAutomata`, CSLib candidate):
* Simulation and covering:
  * `sim` (runs lift along a map on a shrinking set of nodes whose views are preserved) and
    `sim_global`;
  * `view_comp_of_bijOn` (coverings) and `view_one_comp_of_image_eq` (non-counting views).
* Independent selections:
  * `step_step_of_indep` (independent selections can be executed one node at a time);
  * `Selection.Liftable` and `reach_step_of_liftable`;
  * `exists_fair_of_liftable` (adversarial schedules realising liberal schedules of independent
    sets).
* Fair schedules:
  * `exists_fair`;
  * `IsFair.prepend` (fairness ignores finite prefixes);
  * `exists_fair_frequently` (a fair run visiting a co-reachable predicate infinitely often).
* `Automaton.accepts_iff`: acceptance can be read off any fair run.
* Bridge to CSLib's daemon / stone-age framework: `step_eq_stepSet` (a step is a
  `Cslib.SelfStabilization.stepSet` step), `IsFair.stoneAgeFair` (fair schedules are
  `Cslib.StoneAge.Fair`). CSLib's stone-age model (sensing the set of states in the closed
  neighbourhood) is a special case of a non-counting machine.

**Not formalized.** Sections 4–6: simulations of weak broadcast, absence detection and rendez-vous;
the characterizations Trivial, Cutoff(1), Cutoff and NL; the bounded-degree results. Also not
formalized: the bounded-degree variant of Lemma 3.1 (used in Appendix C), and the selection-independence
theorem of [16].

**Trust.** No `sorry`. The listed theorems use only the axioms `propext`, `Classical.choice` and
`Quot.sound`. Non-vacuity (`NonVacuity.lean`): the flooding automaton `flood κ φ` is non-counting
and not halting. For every selection, fairness and degree bound it satisfies the consistency
condition and decides the non-trivial labelling property "some node is labelled `a`"
(`flood_decides`, `flood_isLabelling`). So the hypotheses of Lemmas 3.2–3.5 are met by
non-trivial automata. The hypotheses of Lemma 3.1 are met by the constant accepting automaton
(`acceptAll_halting`, `acceptAll_consistent`). The model is staged in `Podc/` (CSLib candidate). It uses CSLib's
`ωSequence.flatten` and Mathlib's `Set.PartiallyWellOrderedOn` (Dickson's lemma).
