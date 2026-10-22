# Differences between the formalization and the paper

Paper: Czerner, Guttenberg, Helfrich, Esparza, *Decision Power of Weak Asynchronous Models of Distributed
Computing*, PODC 2021, arXiv 2102.11630v2. Scope: Section 3 (Lemmas 3.1–3.5, Corollaries 3.3, 3.6).

## Model

1. **Transition function.** The paper's `δ : Q × [β]^Q → Q` becomes `δ : Q → (Q → ℕ) → Q`. It is only
   ever applied to counts cut off at `β` (`view`), so the two are equivalent: values on other inputs
   are irrelevant. `Machine.Halting` asks `δ q P = q` for all `P : Q → ℕ`, not only `P ∈ [β]^Q`; a paper
   machine is represented by `δ' q P := δ q ⌈P⌉_β`, which has the same runs and is halting in this sense
   iff the paper's machine is halting.
2. **States.** `Q` is an arbitrary type. Finiteness (`[Finite Q]`, with `Q : Type`) is assumed only
   in Lemma 3.5 and Corollary 3.6, the only places where the proofs use it. Allowing infinite `Q`
   elsewhere enlarges the class of automata, so those impossibility results become stronger. Likewise,
   the label alphabet `Λ` is an arbitrary type (the paper: a finite set).
3. **Graphs.** Graphs are bundled (`LGraph Λ` with `V : Type`, `Finite V`). The convention
   "connected, at least 3 nodes" is the predicate `Admissible k`, together with an optional degree
   bound `k : ℕ∞`. The consistency condition (`Consistent k`) and the labelling property
   (`IsLabelling k`) are only required on admissible graphs, as in the paper.
4. **Schedules.**
   * A schedule is `ℕ → Set V` of permitted selections, and every node must be selected infinitely
     often (as in the paper's definition of a schedule).
   * Pseudo-stochastic fairness requires every finite list of permitted selections to occur
     infinitely often as a contiguous block, exactly as in §2.
   * Liberal selection permits `∅`, as the paper's `2^V` does.
5. **Classes.** The classes `xyz` are not separate types. They are hypotheses: `M.β = 1` (d),
   `M.Halting` (a), `A.fair = .adversarial` (f). Every theorem is proved for all three selection
   constraints, so the paper's appeal to [16] (decision power is independent of the selection) is
   neither needed nor formalized.
6. **Acceptance.** "`A` accepts `G`" means that some fair run is accepting, as in the paper. Under
   the consistency condition this is equivalent to every fair run accepting (`Automaton.accepts_iff`).
7. **Majority.** Labels are `Bool`: `true` is `a`, `false` is `b`. Majority is `#b < #a`.

## Statements

8. **Lemma 3.1.**
   * The paper states it for `DaF`. We prove it for every halting automaton, with any counting bound,
     fairness and selection. This covers `Daf` and `DaF`.
   * "Contains a cycle" is formalized as `¬ G.graph.IsAcyclic`.
   * Only the class of all graphs (`k = ⊤`) is covered. The bounded-degree remark (Appendix C, "the
     graph constructed in the proof of Lemma 3.1 is k-degree-bounded") is not formalized.
9. **Lemma 3.2.**
   * Stated for automata with adversarial fairness and any selection constraint; the paper's proof
     handles only synchronous selection.
   * `IsCovering H G f` is a surjective, label-preserving map that is a bijection from `N_H(v)` onto
     `N_G(f v)`, as in the paper. Both graphs must be admissible.
10. **Corollary 3.3.**
    * Stated for every degree bound `k ≥ 2`, including `k = ⊤`. This covers both the main statement
      and "this also holds when restricting to k-degree-bounded graphs".
    * The scaling factor is `l > 0`. `H.count = l • G.count` replaces `L_H = λ L_G`.
11. **Lemma 3.4.** Stated with the cutoff `β + 1` for every selection constraint. For exclusive
    selection this is new: the paper's clique proof needs the synchronous schedule.
12. **Lemma 3.5.**
    * Proved for every non-counting automaton (`β = 1`) with any fairness and any selection; the
      paper states `dAF` and uses exclusive selection.
    * The cutoff is existential, as in the paper. Our `K` differs from the paper's explicit
      `m(|Q|−1)+2`, which the argument does not justify (see below).
13. **Corollary 3.6.** "No `DAf` or `dAF` automaton decides majority" becomes
    `A.fair = .adversarial ∨ A.M.β = 1 → ¬ A.Decides ⊤ majority`, with finite `Q` and any selection.

## Proofs

14. **Lemma 3.1.** We follow the cut-and-paste construction, with these changes.
    * Both graphs get `2T + 1` copies, where `T` is the length of the simulated prefix. The paper uses
      `2g + 1` copies of `G` and `2h + 1` copies of `H`.
    * The chain is a voltage graph over `G ⊕ H`, with the same shape as the paper's `GH`.
    * The distance argument uses a position function that changes by at most 1 along an edge.
    * The reference run on `G ⊕ H` interleaves G-steps and H-steps (liberal and exclusive
      selection), or runs both synchronously (synchronous selection). The paper selects the copies of
      both selections at once. That is not an exclusive selection: the paper relies on [16] here. A
      sequentialisation within one step would also work, because it changes states only at the
      special junction nodes.
15. **Lemma 3.2.** For exclusive selection, the fibre `f⁻¹(v)` of the selected node is executed one
    node at a time. The fibre is independent because `f` is a covering. CSLib's `ωSequence.flatten`
    turns this into an exclusive fair schedule with the same eventual behaviour
    (`exists_fair_of_liftable`).
16. **Corollary 3.3.** The labelled cycles are graphs on `ZMod m`. The `λ`-fold covering is the
    projection `ZMod (λn) → ZMod n`. Its fibres have size `λ` (`ncard_preimage_castHom`). The
    labelling property moves between `G`, `H` and the two cycles.
17. **Lemma 3.4.** We use stars instead of cliques.
    * The schedule is "all leaves, then the centre" (one node at a time for exclusive selection), or
      the synchronous schedule.
    * Leaves with equal labels always share a state (`hinv`).
    * The centre sees the leaf counts per label cut off at `β`, and these agree for the two graphs
      (`min_ncard_preimage_eq`).
    * The paper's clique argument with synchronous runs does not apply to exclusive selection.
18. **Lemma 3.5.** We follow the paper. The parts are:
    * Stars are represented by their abstraction (centre state, leaf counts), with the order
      `StarLE` (same centre, pointwise `≤`, same support).
    * Claim (1) is `reach_lift`: new leaves copy old ones, along any surjection of leaves; for
      exclusive selection a fibre is executed one node at a time.
    * Claim (2): Dickson's lemma (`starLE_pwo`) and finiteness of antichains give a uniform bound on
      the minimal elements, hence the cutoff `m` (`exists_cutoff_of_upward_closed`).
    * The pigeonhole and copying step is `reach_stable_extend`.
    * "Rejects iff a stably rejecting configuration is reachable" holds for both fairness notions
      (`accepts_iff_reach_stablyIn`, using the construction `exists_fair_frequently`).

    Points where we differ:
    * The final cutoff is `K = max(m_Y, m_N)·|Q| + 4`. The paper's `K := m(|Q|−1)+2` is smaller than
      the bound `(m−1)|Q|+2` that its own argument needs whenever `m > |Q|`.
    * Acceptance needs its own `m` (for configurations that can escape `Y`). The paper only says "an
      analogous argument".
    * From cutoff-equal label counts to equal acceptance, we remove nodes whose label occurs more than
      `K` times, one at a time, using stars and the labelling property (`hremove`, `hred`).
19. **Corollary 3.6.** The witnesses are two stars with label counts `(a, b) = (K+2, K+1)` and
    `(K+2, K+2)`. They agree after cutting off at `K` but differ on majority.

## Typos and slips in the paper (no effect on results)

* Lemma 3.4 proof: "`⌈Q_{G(t+1)}⌉_β = ⌈Q_{H(t+1)}⌉_β`" should use `β + 1`.
* Lemma 3.2 proof: "`C_t(v) = C_t(f(v))`" should be `C'_t(v) = C_t(f(v))` (two different runs).
* Lemma 3.5 proof: "`MinPre*(C)` is upward-closed" should be `Pre*(C)`. States and labels are
  conflated (`L_G(q)` for a state `q`).
* Covering maps: the paper does not say that `H` must satisfy the graph convention. We assume both
  graphs are admissible.

## Not formalized

* Sections 4–6: extensions, simulations, the characterizations of the decision power, and bounded
  degree.
* The selection-independence theorem of [16]. It is not needed, because every lemma is proved for
  all three selection constraints.
