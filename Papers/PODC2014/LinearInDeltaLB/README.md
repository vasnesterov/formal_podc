# Linear-in-Δ lower bounds in the LOCAL model — PODC 2014

Mika Göös, Juho Hirvonen, Jukka Suomela. *Linear-in-Δ lower bounds in the LOCAL model.* PODC 2014. DOI
[10.1145/2611462.2611467](https://doi.org/10.1145/2611462.2611467). Formalized version: arXiv
[1304.1007](https://arxiv.org/abs/1304.1007) v1; numbering follows it.

**Verdict: 🛠️ Proof repaired.** Theorem 1 is proved for deterministic LOCAL algorithms: no algorithm
finds a maximal fractional matching in `o(Δ)` rounds. Explicitly, `t ≥ ⌊Δ/2⌋ − 1`. The whole chain is
formalized: the unfold-and-mix lower bound in the EC model, the homogeneous order on the free group,
the Ramsey step, and the identifier-elimination Lemmas 6–7. Every checked statement is true. One step
of the Section 4 proof (equation (3)) is justified by an induction hypothesis that does not apply as
stated and needs a separate nested induction. The randomized extension (Appendix B) is not formalized.

## Mistakes in the paper

No mistakes in the statements.

### Typos and slips
- In the proof of Lemma 6, "`τ_t(U_G, ≺, v) ≅ τ_t(U_G, ≺, v)`" should end with `u`.

## Proof gaps (statements true)

### 🛠️ Equation (3) (Section 4.3, unfold-and-mix step)
The paper justifies `τ_i(GG, ĝ) ≅ τ_i(GH, h)` "by our induction assumption" `τ_i(G, g) ≅ τ_i(H, h)`,
which does not apply because `GH` is not a lift of `H`.

**Impact.** Statement true; repaired by a nested induction (`Inv.step_core`). The paper's idea is right,
but the step as written is a gap a careful referee would flag.

**Details.** The paper reduces (3) to the "critical case" `g* = g`. `GG` is a lift of `G`, but in `GH`
the colour-`c` edge at `h` leads into the copy of `G − e`, and walks can cross that edge several times by
going around loops. So `τ_i(GH, h) ≅ τ_i(H, h)` needs its own argument.

**Repair.** The formal proof inducts on the radius `r ≤ i + 1`, simultaneously for all nodes of the
`G`-half (`GG` vs `GH`) and of the `H`-half (`HH` vs `GH`). (`Inv.step_core`)

### 🛠️ Section 4 base case and proof of Lemma 7 (implicit details)
The base case of Section 4 leaves the choice of the loop colour `c_0` implicit, and the radius `2t + 1`
in the proof of Lemma 7 is too small for `t = 0`.

**Impact.** Statements true; routine details (`exists_inv_zero`, `not_hasRunTime_zero`).

**Details.**
* *Base case.* (P1) needs a loop colour `c_0` present in both `G_0` and `H_0 = G_0 − e`, so `c_0`
  cannot be the colour of `e` (Figure 5 shows the intended choice). Such a `c_0` exists because `H_0`
  is loopy (`Δ ≥ 2`), hence saturated, and `y(e) ≠ 0`. (`exists_inv_zero`)
* *Radius in Lemma 7.* The radius occurs only inside the proof, not in the statement of Lemma 7. For
  `t ≥ 1` the neighbours of the nodes of `B_{t+1}(v)` lie in `B_{2t+1}(v)` and the argument works. For
  `t = 0` they do not, and the saturation indicator `A*` needs radius `≥ 1` to see its own edges. But
  for `t = 0` the hypothesis of the lemma (a 0-round algorithm finding a maximal FM) cannot hold: such
  an algorithm already fails on a 3-node path (`not_hasRunTime_zero`). We use radius `2t + 2`
  throughout.

Full list of differences (including modelling choices and minor imprecisions): [differencies.md](differencies.md).

## The formalization

**Model.**
* **Deterministic LOCAL with unique identifiers.** Graphs are `SimpleGraph ℕ` with finitely many
  edges; identifiers are arbitrary naturals. `A G v u` is the weight `v` outputs for its edge to `u`.
  Run-time `t` means the output of `v` depends only on `τ_t(G, v)`, the edges at nodes of distance
  `< t` (CSLib `Cslib.Local.GAgree`). `A.Solves Δ` asks for a maximal fractional matching (consistent,
  nonnegative, loads `≤ 1`, every edge has a saturated endpoint) on every finite graph of maximum
  degree `≤ Δ`. The algorithm may depend on `Δ`.
* **EC model** (intermediate): algorithms are functions of the view, a colour system of CSLib's
  `Cslib.ColourSystem`, so lift-invariance holds by construction. Multigraph outputs are read through
  the universal cover, and a loop counts once. "Loopy" means every node carries a loop. This is a
  sufficient form of Definition 1.
* **PO / OI** (intermediate): PO-views are subsets of the Cayley tree of the free group `F_k`, ordered
  by a left-invariant linear order (Lemma 4). ID-instances are finite pieces of PO-views labelled
  order-preservingly by identifiers.
* Lemma 5 is used in a finite-Ramsey form. Lemma 7 compares labellings of one ball of radius `2t + 2`
  instead of extending labellings from a sparse set `J`. This changes no statement used in Section 5.5.

**Main results in Lean.**

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (deterministic): `t ≥ ⌊Δ/2⌋ − 1` | `theorem1` | `Main.lean` |
| Step 1 / Section 4: EC lower bound `t ≥ k − 1` on loopy EC-graphs | `ECAlg.le_runTime`, `ECAlg.exists_pair` | `ECLowerBound.lean` |
| Lemma 2 (loopy ⇒ saturated; multigraph semantics, for the graphs of Section 4) | `Cfg.Good.load_eq_one` | `ECConfig.lean` |
| Fact 3 (propagation), base case, unfold-and-mix | `propagation`, `exists_inv_zero`, `Inv.step` | `ECLowerBound.lean` |
| Lemma 4 (homogeneous order = left-invariant order on `F_k`) | `Cslib.FreeGroupOrder.lt_mul_left_iff`, `instIsStrictTotalOrder` | `Podc/Foundations/GroupTheory/FreeGroupLeftOrder.lean` |
| Lemma 5 (Naor–Stockmeyer, finite form) | `exists_homog` | `Ramsey.lean` |
| Lemma 6 | `Setup.sat_of_loopy` | `OrderInvariance.lean` |
| Lemma 7 (one node; general) | `Setup.out_eq_of_single`, `Setup.out_eq` | `OrderInvariance.lean` |
| Section 5.1 (PO-view of an EC-graph) | `cover`, `inv_smul_cover`, `cover_tGraph_view` | `POCover.lean` |
| Simulation (4), Corollary 9, Section 5.5 | `simEC`, `simEC_hasRunTime`, `Setup.simEC_isMaxFM` | `Simulation.lean` |
| Non-vacuity of `IDAlg.Solves` | `exists_solves` | `NonVacuity.lean` |

**Not formalized.** Randomized algorithms (Appendix B), the algebraic proof of Lemma 4 (A.1), and the
general forms of the simulations EC ⇝ PO and PO ⇝ OI for arbitrary PO-checkable problems.

**Trust.** No `sorry`; `theorem1`, `ECAlg.le_runTime` and `Cslib.FreeGroupOrder.lt_mul_left_iff` use
only `propext`, `Classical.choice`, `Quot.sound`. Non-vacuity: `exists_solves` gives a (global)
algorithm satisfying `Solves Δ` for every `Δ`. The EC model comes from CSLib `Cslib.ColourSystem` and
the locality notion from `Cslib.Local.GAgree`. The finite hypergraph Ramsey theorem is staged in
`Podc/Foundations/Combinatorics/HypergraphRamsey.lean`.

**CSLib candidates.** `Podc/Foundations/GroupTheory/FreeGroupLeftOrder.lean` (free groups are
left-orderable). Also, from `ECConfig.lean`: `ColouredGraph.restrict`, `ball_view_zero`,
`ball_view_succ_of_step_eq`, and first-letter lemmas for `FreeCox` (marked `-- CSLib candidate`). The
generic pieces of `FreeTree.lean`, `POCover.lean` and `IDGraph.lean` (free-group Cayley tree, PO-views
of EC-graphs, ID-graphs carved out of a tree) would also fit in CSLib if a second paper uses them.
