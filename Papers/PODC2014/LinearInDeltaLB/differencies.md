# Differences between the formalization and the paper

Paper: Göös, Hirvonen, Suomela, *Linear-in-Δ lower bounds in the LOCAL model*, PODC 2014;
formalized version arXiv 1304.1007v1.

## Scope

1. **Randomized algorithms (Section 2, Appendix B) are not formalized.** Theorem 1 is proved for
   deterministic LOCAL algorithms only (`theorem1`). The derandomization of Appendix B (Lemma 10,
   finite Ramsey sets `I_n ⊆ S_n`) is not formalized. This is a scope limitation, not an issue found
   in the paper.
2. **Explicit constant.** The paper states `Ω(Δ)`. We prove `t ≥ ⌊Δ/2⌋ − 1` for every `Δ`
   (the bound is vacuous for `Δ < 4`). The constant comes from the paper's own chain: an EC lower bound
   `t ≥ k − 1` for `k` colours, and EC with `k = ⌊Δ/2⌋` colours embeds into degree `2k ≤ Δ`.
3. **Lemma 4, algebraic proof (A.1).** Not formalized. Only the combinatorial proof (A.2) is
   formalized, rephrased as a positive cone on reduced words (`Cslib.FreeGroupOrder`).
4. **The general simulations of Section 5 are formalized only where they are used.** The paper
   states EC ⇝ PO for all graphs, and PO ⇝ OI for all PO-checkable problems. We formalize the
   composite simulation `simEC` (EC ⇝ PO ⇝ OI ⇝ ID) and prove it correct on loopy EC-graphs
   (`Setup.simEC_isMaxFM`), which is all that Section 5.5 uses. Separate notions of PO- and
   OI-algorithms, PO-checkability and Corollary 9 for `A_OI` as a standalone algorithm are not
   introduced.

## Modelling choices

5. **ID model.** An ID-graph is a `SimpleGraph ℕ` with finitely many edges; identifiers are node
   names, unbounded and arbitrary (strictly local algorithms do not know `n`). `A G v u` is the
   weight node `v` outputs for its edge to the neighbour with identifier `u`. Run-time `t` is CSLib's
   `GAgree G G' v t`: the output depends only on the edges incident to nodes at distance `< t`.
   This is the paper's `τ_t` (an edge `{u,w}` is at distance `min + 1`, so `τ_0` contains no edges).
   Correctness (`IDAlg.Solves Δ`) is required on all finite graphs of maximum degree `≤ Δ`, as in
   the paper.
   `IDAlg.HasRunTime t` asks for locality on *all* graphs (also infinite ones or ones of degree
   `> Δ`), while the paper only uses graphs of maximum degree `Δ`. This is no loss of generality: an
   algorithm that is `t`-local on finite graphs of degree `≤ Δ` can be replaced by
   `A'(G, v) := A(τ_t(G, v), v)` (and `0` when `τ_t(G, v)` is infinite or has degree `> Δ`), which is
   `t`-local on all graphs and agrees with `A` on the paper's graphs.

6. **EC model.** An EC-algorithm is a function of the view, a colour system `⊆ FreeCox k` (CSLib
   `Cslib.ColourSystem`), with outputs `Fin k → ℝ`. Lift-invariance (eq. (2)) is built in. Outputs
   on multigraphs are read off the universal cover, and a loop counts once in the load (Section 3.5).
   `ECAlg.SolvesLoopy` requires correctness on finite loopy multigraphs, in this multigraph
   semantics. The paper requires correctness on simple graphs and transfers it to multigraphs via
   lifts (discussion before Lemma 2). This does not matter for Theorem 1: the hypothesis is
   *derived* from ID-correctness on finite simple graphs (`Setup.simEC_isMaxFM`).
7. **Loopiness.** `IsLoopy G` means that every node of `G` carries a half-loop. This is a sufficient
   condition for the paper's Definition 1, which asks for a loop at every node of the factor graph
   `F_G`. The paper's `k`-loopiness of `G_i` is tracked as "at most `i + 1` non-loop colours per
   node" (`Cfg.Good`). For PO-views we use `IsLoopyF U`: every node has a neighbour with the same
   re-rooted view.
8. **PO-views.** The universal cover of the PO-graph of an EC-graph is `cover G a ⊆ F_k`: the reduced
   words that can be followed letter by letter (letters `c` and `c⁻¹` both follow the `c`-edge). The
   tree `T` of Section 5.3 is the Cayley graph of `F_k = FreeGroup (Fin k)`. Its edge colouring and
   orientation are the letters.
9. **Lemma 2** is immediate in the multigraph semantics, where a loop is an edge with both endpoints
   at `v` (`Cfg.Good.load_eq_one`). The paper's lift argument (Figure 4) is not needed.

## Proofs: changes and details supplied

10. **Lemma 5 (Naor–Stockmeyer) — finite instead of infinite Ramsey.** Mathlib has no hypergraph
    Ramsey theorem. We use the finite one (`Podc/Foundations/Combinatorics/HypergraphRamsey.lean`,
    `Cslib.exists_homogeneous`), iterated over the finitely many shapes `X ⊆ B_t(F_k)`
    (`exists_homogeneous_family`, `exists_homog`). This gives a *finite* set `I` that is homogeneous
    for the saturation indicator on every shape and is as large as needed. The paper itself notes
    that a finite version suffices (Appendix B).
11. **Lemma 7 — no sparse set `J`, no extension of labellings.** The paper labels only `B_t(v)`
    with identifiers from a sparse `J ⊆ I`, then extends two labellings to `B_{2t+1}(v)` with
    values in `I`. We instead compare two order-preserving `I`-labellings of the *same* ball
    `U ∩ B_{2t+2}` (`Setup.out_eq`). The one-node-change chain stays inside `I`
    (`chain_induction`). The EC-algorithm `simEC` labels a fixed big ball of `F_k` by `I` once and for
    all (`labelOf B I`). Its run-time `t` is then immediate (`simEC_hasRunTime`), and its outputs are
    identified with those of `A` on a bigger labelled ball through Lemma 7 (`Setup.big_out`).
12. **Radius `2t + 2` instead of `2t + 1` in the proof of Lemma 7.** The radius `2t + 1` occurs only
    in the proof, not in the statement. The saturation of a node `u ∈ B_{t+1}(v)` needs all
    neighbours of `u`, which lie in `B_{t+2}(v)`; this is inside `B_{2t+1}(v)` iff `t ≥ 1`. Also, the
    saturation indicator `A*` of step (i) needs radius `≥ 1` to see its own edges. For `t = 0` the
    hypothesis of Lemma 7 (a 0-round ID-algorithm finding a maximal FM) is unsatisfiable
    (`not_hasRunTime_zero`: such an algorithm fails on a 3-node path), so Lemma 7 is vacuously true
    there. Not a statement-level issue; at most a degenerate case of the proof (R2).
13. **Walk in the proof of Lemma 7 (Fact 8).** The paper walks from `v` "away from `v*`". We take,
    among the nodes `w` in the shadow of the root as seen from `v*` (`|v*⁻¹ w| = |v*| + |w|`) whose
    parent edge carries a disagreement, one of maximal depth. This is the same argument
    (`Setup.out_eq_of_single`).
14. **Fact 3 / propagation walk in Section 4.** The paper walks until it reaches a loop. We choose,
    among the nodes with an "incoming disagreement", one farthest from `g` (`propagation`,
    `Inv.step_core`). This is the same argument.
15. **Base case of Section 4 (terse in the paper).** The paper says the pair `(G_0, H_0 = G_0 − e)`
    "satisfies (P1–P3)". (P1) needs a loop of a colour `c_0` present at both nodes, so `c_0` cannot
    be the colour of the removed loop `e`. Figure 5 indicates the intended `c_0`. The detail
    supplied: `H_0` is loopy, so it is saturated too (needs `Δ ≥ 2`). Both loads are `1` and
    `y(e) ≠ 0`, so the common loops cannot all keep their weights (`exists_inv_zero`). Only
    `y(e) ≠ 0` is used, not positivity.
16. **Equation (3) needs a separate nested induction (proof repair).** The paper says the critical
    case is `g* = g`, and that `τ_i(GG, ĝ) ≅ τ_i(GH, h)` follows "by our induction assumption"
    `τ_i(G, g) ≅ τ_i(H, h)`. `GG` is a lift of `G`, but `GH` is not a lift of `H`: walks in the views
    can cross the colour-`c` edge between the two halves several times (through loops), so
    `τ_i(GH, h)` is not `τ_i(H, h)` and the induction assumption does not apply as cited. The formal
    proof inducts on the radius `r ≤ i + 1`, simultaneously for all nodes of the `G`-part (`GG` vs
    `GH`) and of the `H`-part (`HH` vs `GH`). It uses `ball_view_succ_of_step_eq`: the radius-`(r+1)`
    view is determined by the edges at the root and the radius-`r` views of the neighbours. The
    paper's idea is correct, but the justification given is not, so we count this as a genuine (if
    small) repair of the proof of Step 1, not a routine detail.
17. **The "analogous" case of the inductive step** (weight of `{g,h}` differs from that of `f`) is
    handled by the symmetry `mix_swap`: `D.mix C c` is `C.mix D c` re-rooted at `c`.
18. **Typo in the proof of Lemma 6.** "By order homogeneity, `τ_t(U_G, ≺, v) ≅ τ_t(U_G, ≺, v)`": the
    right-hand side should be `τ_t(U_G, ≺, u)`.

## Verdict calculation

Checked statements: Theorem 1 (deterministic part), Lemma 2 (multigraph form), Step 1, Fact 3/8,
Lemma 4, Lemma 5 (finite form), Lemma 6, Lemma 7 (for labellings of a slightly larger ball),
Corollary 9 / Section 5.5 (as `simEC_isMaxFM`). All are true as written. The proof of Step 1 needs a
repair at equation (3) (item 16: the cited induction hypothesis does not give the claimed view
isomorphism; a nested induction is needed). Items 15 and 17 supply routine details, item 12 concerns
only the proof and only the vacuous case `t = 0` (R2), item 18 is a typo inside a proof. No statement
is wrong, so no rule R2–R4 is needed; the worst label is 🛠️ (proof repaired). Borderline: item 16
could be read as a routine detail (→ ✅); we count it as a gap because the paper's stated
justification ("by our induction assumption") does not apply to `GH`.
