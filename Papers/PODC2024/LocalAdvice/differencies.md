# Differences between the formalization and the paper

Paper: Balliu, Brandt, Kuhn, Nowicki, Olivetti, Rotenberg, Suomela, *Distributed Computation with Local
Advice*, arXiv:2405.04519 v2 (full version of the PODC 2024 brief announcement *Local Advice and Local
Decompression*). Formalized: Theorem 30 with Lemmas 31–34 (Appendix D), Theorem 5 (Section 4.1), and
Lemma 1 (as a tool).

## Statement-level issues (verdict-relevant)

1. **Lemma 1 (LLL), condition `e·p·d ≤ 1`.** This is false for `d = 0`: take one event of
   probability 1 (`lemma_1_as_stated_false`). Rule R2 (degenerate corner, never used) → ⚠️.
   We prove and use the standard symmetric form `e·p·(d+1) ≤ 1`
   (`Cslib.Probability.exists_forall_not_of_symmetric`) and an asymmetric form. The paper's
   application satisfies both. Borderline: Lemma 1 is a cited textbook lemma, but it is a numbered
   statement of the paper, so it counts.
2. **Algorithm `A` (page 42), "smallest ID … that receive color 1".** Nodes of `C(u)` never have
   colour 1, so the description must read "bit 1". The overview ("the smallest-ID node in the
   component") and the proof of Theorem 34 recover this. Rule R3 (typo, evident intent, local fix)
   → ⚠️. We implement "bit 1" (`outW`, `zone`).
3. **Theorem 5, proof.** The LOCAL model of Section 3.1 gives `n` to the nodes, but the proof treats
   `A` as `n`-independent. Running `A` on the padded graph `H` (with `N ≠ n` nodes, `N` chosen after
   the Ramsey set) is then not covered. The statement is true (`theorem_5`), so this is a proof
   repair (🛠️), not a statement issue. Repair: finite Ramsey for every size `M` on `{1,…,(R(M)+M)!}`
   against `A_{(R(M)+M)!}`, then pigeonhole over the finitely many behaviour types. Choosing
   `M ≥ n + s` gives `n | N` and room to pad balls.

Final label: ⚠️ (worst of ⚠️ (items 1, 2) and 🛠️ (item 3); no false non-degenerate statement).

## Modelling choices (3-colouring part)

* **Identifiers.** The node type `V` is a finite linear order whose order gives the identifiers. The
  algorithm is one definition `decode Δ`, uniform in `V`. The paper's identifier range
  `{1, …, poly(n)}` plays no role.
* **Quantifier order in Theorem 30.** `theorem_30` fixes the node type `V` (hence `n` and the
  identifier set) before `∃ A`, so read alone it would allow `A` to depend on `V`. The witness is the
  single definition `decode Δ`, and `theorem_30_decode` states the result for it, uniformly in `V`.
* **Knowledge.** The algorithm knows an upper bound `Δ` on the degrees (the paper: the maximum
  degree). The correctness theorems hold for any upper bound. `n` is not used.
* **Rounds = locality.** An `R`-round algorithm is an `IsLocal R` function (CSLib): the output only
  depends on the edges at nodes at distance `< R` and on the bits at distance `≤ R`.
* **Round bound.** We prove radius `8000Δ⁹ + 3` (`decode_isLocal`). The proof of Theorem 34 sketches
  `4000Δ⁹ + 2`. Theorem 34 claims only `O(Δ⁹)` and Theorem 30 only `Δ^{O(1)}`, so the constant does not
  matter. Our locality proof transfers distances between two nodes of the radius-`4000Δ⁹` ball, which
  costs a factor 2. The paper's sharper bound is plausible: a node sees its whole small component.
  We did not formalize it.
* **Small-component test.** "The component `C(u)` has diameter `≤ 4000Δ⁹`" is computed as `SmallAt`:
  no node at distance `4000Δ⁹ + 1`, and the radius-`4000Δ⁹` ball has diameter `≤ 4000Δ⁹`.
  `smallAt_iff_not_isLarge` proves this equivalent to the paper's condition.
* **Choices of the decoder.** "`u` selects a node `w` …" is made deterministic: `w` is the 1-bit of
  smallest identifier within distance `3000Δ⁹`. The paper allows any such `w`; the proof works for
  any. "The number `N` of components of 1-bit nodes" becomes the predicate `ZConn` (the 1-bits of the
  zone induce a connected subgraph), which is how the decoder uses `N` (`N = 1` vs `N > 1`).
* **Components and distances.** `G_{2,3}` is `H23 G φ`: same vertex type, colour-1 nodes isolated.
  `dist_C` is `(H23 G φ).edist` (`⊤` across components). The ruling sets `R_C` of all large
  components are merged into one set `R`. Their separation (`≥ 2000Δ⁹` within a component) is stated
  with `edist`, so it holds across components automatically. The domination radius is `2000Δ⁹`.
* **Ruling set.** We use a maximal set of large nodes with pairwise distance `≥ 2000Δ⁹`
  (`exists_rulingSet`), instead of a maximal independent set of the power graph
  `C^{2000Δ⁹}`. Both give the required properties.
* **Witness sets.** Lemma 31's two cases are packaged as `IsWitness` (`{w}` with `≥ 2` colour-1
  neighbours, or an adjacent pair without a common colour-1 neighbour). The paper's remark that the
  proof of Lemma 31 "also works" along `P_v` is proved as `exists_witness_on_path`, and Lemma 31 is
  derived from it.
* **`T_v`.** `InT` is the paper's definition of `T_v`. The paper's bound
  `|V(C) \ T_v| ≤ 2Δ² + 2Δ + 2 ≤ 6Δ²` is reproduced (`exists_bad_set`). The pigeonhole over
  `6Δ² + 1` disjoint blocks of `Δ + 1` consecutive nodes of a geodesic of length `20Δ³` gives `P_v`.
* **LLL application (Lemma 32).** Variables: one per `r ∈ R`, uniform on `Q_r`. Events: `A_u` for
  every node `u`; it is empty for nodes of colour `≠ 1`. We bound `Pr[A_u] ≤ (Δ / 12Δ⁶)² = 1/(144Δ¹⁰)`
  using `∑_r #hits ≤ Δ`, which is slightly better than the paper's `1/(144Δ⁸)`. The dependency degree
  is `≤ 48Δ⁸`, as in the paper, and `e · p · (48Δ⁸ + 1) ≤ 1` holds for `Δ ≥ 1` (`lll_numeric`).
* **`Δ ≥ 1`.** The schema lemmas assume `1 ≤ Δ` (several constant comparisons need it). For `Δ = 0`
  the graph has no edges and Theorem 30 is trivial (handled in `theorem_30`).
* **Greedy colouring.** Its existence is proved (`exists_isGreedy`); the paper assumes it.
* **Lemma 33.** "At most one neighbour `w` with `b(w) = 1`" is `(nbrIn G v (ones b)).card ≤ 1`.
  Lemma 33 needs no hypothesis on `Δ`.
* **Theorem 34.** It is split into `Schema.decode_eq_psi` (`A` outputs the paper's colouring `ψ`),
  `psi_proper` (`ψ` is proper) and `decode_isLocal` (rounds).

## Modelling choices (Theorem 5)

* **Instances.** Node inputs only. The paper's "finite-input" problems may also label edges, and
  these are not modelled. Outputs are node labels, as in the paper.
* **Component-wise.** The paper says "a valid solution for `G` is also valid for a connected
  component isomorphic to `G`". We use the slightly stronger natural reading (`ComponentWise`).
  Validity restricts along any isomorphism onto a union of components, and only the outputs on the
  nodes of the instance matter. The proof needs this because `G` itself may be disconnected, and
  isomorphism-invariance is implicit in the paper.
* **Family.** The paper leaves implicit that the graph family admits the padded graph `H`. We
  assume the family is closed under disjoint unions of copies (`hFam`) and that its graphs have
  maximum degree `≤ Δ` (`hdeg`).
* **Identifier range.** "Identifiers from `{1, …, poly(n)}`" is abstracted to any predicate `Adm` on
  identifier sets with `Adm {1, …, N}` for all `N`.
* **Conclusion strengthened.** `A'` is order-invariant (`OrderInvariant`: invariant under every
  order embedding `ℕ ↪o ℕ`), does not take `n`, and solves the problem on every instance of the
  family with arbitrary identifiers.
* **Ramsey.** We use the finite hypergraph Ramsey theorem plus pigeonhole instead of the infinite
  one, which is not in Mathlib. Ball sizes are bounded by `s = (Δ + 1)^T`.
* The hypotheses `[Nonempty In]`, `[Nonempty Out]` of the first draft were unnecessary and are not
  in the statement.

## Not formalized

Theorem 6 (ETH), Appendix A (Theorem 7, LCLs on sub-exponential growth graphs, Lemmas 9–10), Appendix B
(balanced orientations, Lemma 12, decompression), Appendix C (`Δ`-colouring, Theorem 20, Lemmas 22–26),
Appendix E (composability, Lemmas 35–36), Definitions 3–4 (sparsity, composability).
