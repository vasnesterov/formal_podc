# Differences between the formalization and the paper

Paper: S. A. Amiri, S. Schmid, S. Siebertz, *A Local Constant Factor MDS Approximation for Bounded
Genus Graphs*, PODC 2016. Text used: arXiv:1602.02991v2 (12 Feb 2016, the latest arXiv version).
The ACM proceedings version could not be compared. All statements refer to arXiv v2.

Verdict rules are those of `verdicts.md` (R1–R6).

## Errors in the paper (statement level)

1. **Lemma 7 (items 2 and 3) is false** (R1: numbered lemma → ❌).
   - *Graph.* `G7 K` has vertices `m_i, c', m_j, u_1..u_K` and edges `m_i c'`, `c' u_k`, `m_j u_k`.
     It is planar, and every edge meets `{c', m_j}`. So every depth-1 minor has `|E(H)| ≤ 2|V(H)|`
     and `K_{3,3}` is not a depth-1 minor (`SimpleGraph.depth1_of_cover_two`): Assumption 6 holds
     with `c = 2`, `t = 3`.
   - *Setup.* `M = {m_i, m_j}` is a minimum dominating set (`G7_min`). `D = ∅` (`G7_phase1`).
     `C_{m_i} = C_{m_j} = {c'}`.
   - *Item 2* (order `m_i, m_j`). `|{u ∈ N_j : u sees N_i}| = K > 2ct = 12` for `K = 13`
     (`lemma_7_2_false`).
   - *Item 3* (order `m_j, m_i`). `K > 4ct = 24` for `K = 25` (`lemma_7_3_false`).
   - The statements do not mention `C`, so the counterexamples do not depend on the choice of `C_m`.
   - *Item 1* (`m_i ∈ D`) has the same proof gap but was not refuted formally.
   - *Where the proof breaks.* The covering vertex `c ∈ C_{m_j}` may itself lie in `N_i`. Then the
     branch sets "star of `m_i` without `c`", `{c}`, `{m_j}` do not see the `u` whose only
     `N_i`-neighbour is `c`.
   - *Repair.* Count only leaves outside `C` with a neighbour outside `C` (`Setup.X a b`). The bounds
     become `2c(t-1)` (`Setup.lemma_7_12`) and `4c(t-1)` (`Setup.lemma_7_3`).
2. **Corollary 8 is false** (R1 → ❌). In `G7 145` the paper's `Y` contains all 145 vertices `u_k`,
   but `6c²t|M| = 144` (`corollary_8_false`). This holds for every choice of `C`.
   - *Repair.* Use `Y` = leaves outside `C` of stars of `M \ D` with a neighbour outside `C` in another
     star, and `Y_D` = its part that sees stars of `M ∩ D`. Then `|Y| + |Y_D| ≤ 6c²(t-1)|M|`
     (`Setup.corollary_8`). The proof charges every vertex to an oriented edge of the depth-1 minor
     `H`, at most `2c(t-1)` (forward) and `4c(t-1)` (backward) per edge. It splits the `≤ 2c|M|`
     oriented edges by the order of their endpoints.
3. **Lemma 11 is false** (R1 → ❌).
   - *Graph.* The book `K_{1,1,17}` (spine `m x`, pages `u_k`; vertex cover `{m, x}`), with `c = 2`,
     `t = 3`.
   - *Setup.* `M = {m}`, `D = ∅`, `C_m = {x}`. Every admissible `C_m` (`|C_m| ≤ 4`, `m ∉ C_m`,
     covering 17 pages) must contain `x`.
   - *Dominators.* `dom ≡ x` is a legal choice: `m` and `x` both have residual degree `|V|`
     (`S11_isDominator`).
   - *Violation.* `Y = Z = ∅`, and all 18 leaves of `m` have `dom(u) ∈ N_{E'}(m) \ (Y ∪ Z)`, while
     `(2(t-1)+4)c|M| = 16` (`lemma_11_false`).
   - *Where the proof breaks.* It applies Lemma 9 to `dom(u)`, which may lie in `C_m`.
   - *Repair.* Exclude `C` from the range as well, i.e. require `dom(u) ∈ N_{E'}(m) \ (C ∪ Y ∪ Z)`,
     and count sources `u ∉ N[D]`. Then the paper's bound `(2(t-1)+4)c|M|` holds (`Setup.lemma_11`).
     Per star: `#sources ≤ |N_{E'}(m) \ N[D]| ≤ deg(x) ≤ 4c + 2c(t-1)`. The middle inequality comes from
     `d_{V-D}(m) ≤ d_{V-D}(x)`; it is not "`m` has at most … `E'`-neighbours", which fails when `m`'s
     leaves are dominated by `D`.
4. **Lemma 9 is false for some admissible `C_m`** (R1 → ❌; not formalized, informal counterexample).
   - *Graph.* `m – v`, both adjacent to 18 vertices forming 6 paths `a_i – c_i – b_i`. This is
     planar: draw `K_{2,18}` with the `u`'s on a line and the path edges inside consecutive faces.
     So `c = 3` and `t = 3`.
   - *Setup.* `D = ∅`. `C_m = {c_1, …, c_6}` is admissible and `v ∉ C_m`.
   - *Violation.* `v` has 18 neighbours in `N_{E'}(m)`, but the lemma claims `2c(t-1) = 12`.
   - *Where the proof breaks.* It covers only neighbours `u ∈ N(c)` for `c ∈ C_m`, not `u ∈ C_m`.
   - *Repair.* Count only neighbours outside `C` (`Setup.lemma_9`), which is all Lemma 11 needs.
   - This item does not affect the verdict (items 1–3 are formal).
5. **Theorem 13: the `O(g)` approximation factor is not established** (headline, unestablished →
   ❌ by R5).
   - *What the paper uses.* The proof uses Lemma 12 with `t = 4g+3` and treats `c` as a constant
     ("`c ≤ 3.01` … in sufficiently large graphs", §4).
   - *Why `c` grows with `g`.* Lemma 5 (applied to `H̃`) and Lemma 10 (applied to `G[Z ∪ M ∪ C]`)
     need the density bound for small depth-1 minors too. Small graphs of genus `g` have density up
     to `Θ(√g)` (`K_k`).
   - *Lean.* `density_unbounded`: for every `c`, some complete graph satisfies the genus-type
     hypotheses (Euler's bound for all depth-1 minors with some `g`, and no `K_{4g+3,3}`) but has a
     depth-1 minor of density `> c`.
   - *What we prove.* With `c(g) = 3 + ⌊√(3g)⌋ + 1` (`depth1DensityLE_of_euler`) the factor is
     `≤ 1100(g+1)²` (`theorem_13`, `factor_le`). Whether the algorithm is an `O(g)`-approximation
     remains open.
   - *Rounds.* "`O(g)` communication rounds" holds but is far from tight: 6 rounds suffice
     (`output_isLocal`).

## Proof repairs (statements true)

6. **Lemma 5.**
   - *Gap.* `H̃` contracts the stars only for `m ∈ M \ D`. Vertices `v ∈ N(D \ M) \ (D ∪ M)` whose
     unique `H`-neighbour in `M` lies in `M ∩ D` remain as extra vertices of `H̃`, so
     `|V(H̃)| = |D \ M| + |M|` is false.
   - *Repair.* For every `m ∈ M`, contract `m` together with the vertices outside `M ∪ D` assigned to
     `m` (via any assignment `a : V \ M → M` to an `M`-neighbour). Keep `{w}` for `w ∈ D \ M`.
   - *Double counting.* With `S = Σ_{w ∈ D\M} deg_{H̃}(w) ≥ (2c+1)|D\M|` and inclusion–exclusion over
     ordered touching pairs, `2S ≤ 2c|V(H̃)| + 2c|D \ M|`.
   - *Generality.* The lemma holds for every dominating set `M`, not only minimum ones.
7. **Lemma 12.**
   - *Gap.* The paper's accounting relies on Corollary 8 (false) and Lemma 11 (false).
   - *Repaired accounting.* `dom(R) ⊆ (M ∪ C) ∪ Z ∪ Y ∪ dom(Y_D) ∪ dom(R ∩ (M ∪ C)) ∪ dom(Src)`
     (`Setup.image_dom_subset`). A dominator outside `M ∪ C ∪ Y ∪ Z` either lies in the source's own
     star (then it is counted by Lemma 11), or lies in a star of `M ∩ D` (then the source is in `Y_D`).
   - *Constant.* `(c+1) + (2c+1) + (2c+1) + (2c+1) + 6c²(t-1) + (2(t-1)+4)c
     = 6c²t + (2t+5)c + 4 + (4c − 6c²) ≤ 6c²t + (2t+5)c + 4`, for `t ≥ 1`. So the paper's constant is
     recovered exactly.
   - *Degenerate case.* `t = 0`: excluding `K_{0,3}` forces `|V| ≤ 2`, handled separately.
8. **Lemma 10.** The claim `|Z| < |M ∪ C|` fails for the empty graph (both sides 0; R2,
   degenerate). We prove `|Z| ≤ |M ∪ C|` (`Setup.lemma_10`). The paper's "more than `½·4c|Z|`
   edges" is also handled correctly when `Z ∩ C ≠ ∅`: we count ordered pairs.

## Imprecisions and typos

9. **Lemma 12's hypothesis** reads "edge density at most `c`", but the proof needs Assumption 6
   (all depth-1 minors have density `≤ c`). Lemma 12 lies in the scope of Assumption 6 ("for the
   rest of this section"), so we read it with Assumption 6 (R4). The Lean statement assumes
   `Depth1DensityLE G c`.
10. The last display of Lemma 12 drops the factor `|M|` on the right-hand side.
11. Proof of Lemma 7:
    - "`m_i ∉ C_{m_2}`" should read `C_{m_j}`.
    - It is not implied "by definition of `E'`": `C_{m_j}` is arbitrary. However, `m_i` covers no
      vertex of `N_j`, so it can be ignored (we do so, `lemma_7_12`).
12. The remark after Theorem 13 ("for planar graphs … a 199-approximation") is `lemma_12` with
    `c = 3`, `t = 3` (`6·9·3 + 11·3 + 4 = 199`), taking as hypotheses that depth-1 minors of planar
    graphs are planar (so `|E(H)| ≤ 3|V(H)|`) and that planar graphs exclude `K_{3,3}`. With these
    facts the claim holds; it is not stated as a separate Lean theorem.
13. Algorithm 1 has a stray `end if`. The algorithm returns `D ∪ D'` with `D' = dom(V \ N[D])`, as
    modelled.

## Modelling choices

14. **Dominator choice.** Line 15 "choose any `dom(v)`" is formalized as a hypothesis `IsDominator`.
    `lemma_12` holds for every such choice, adversarial ones included. For locality we fix the
    tie-break "smallest identifier among the maximizers" (`domMin`, `Locality.lean`).
15. **Approximation.** `IsApprox G f S` requires `|S| ≤ f·|M|` for every dominating set `M`. This is
    equivalent to `|S| ≤ f·γ(G)` and avoids defining `γ`.
16. **Parameters.** `c` is a natural number, as in the paper ("an integer `c`"). `ε(H) ≤ c` is stated
    as `|E(H)| ≤ c·|V(H)|` for finite depth-1 minors on vertex types in `Type`. `t` is any natural
    number; the paper assumes `t ≥ 3`, and our statements are stronger.
17. **Depth-1 minors.** A depth-1 minor model is a family of pairwise disjoint vertex sets, each with
    a center adjacent to all its other vertices, and every edge of `H` is realized by a `G`-edge
    between the branch sets. This matches §2 ("pairwise disjoint stars `G_v ⊆ G`"). Bridge to CSLib
    minors: `SimpleGraph.Depth1Model.toMinorModel`, `SimpleGraph.MinorDensityLE.depth1DensityLE`.
18. **Ordering and `E'`.** The paper defines `E'` inductively along an ordering of `M` with `M ∩ D`
    first. We use an injective rank `ord` on `M` (D-first). The star of `v ∉ M` is the `ord`-first
    `M`-neighbour `S.star v`, which gives exactly the paper's `N_{E'}(m)` (`Setup.leaves`). The
    covering sets `C_m` are part of the data (`Setup.Cm`, any admissible choice). The counterexamples
    exhibit specific admissible choices; the existence of a `Setup` for every dominating set is
    `Setup.exists_of_dominating`.
19. **Genus.** Mathlib has no surfaces or genus, so Theorem 13 assumes the consequences of
    Lemmas 1, 2, 4:
    - Euler's bound `|E(H)| ≤ 3|V(H)| + 6g` for all depth-1 minors (`EulerEdgeBound`; weaker than
      `3|V| + 6g − 6`, so it is implied for orientable genus `g` and for non-orientable genus `g̃`
      with `g = g̃`);
    - exclusion of `K_{4g+3,3}` as a depth-1 minor.

    Lemma 3 and Section 4 are not formalized.
20. **LOCAL model.** Locality is extensional (CSLib `Cslib.Local.IsLocal`): membership of `v` in the
    output depends only on the edges at nodes at distance `< 6` from `v`. Identifiers are the
    elements of the linearly ordered vertex type.

## Not formalized

- Lemmas 1–4 (topological graph theory; used as hypotheses).
- Lemma 14, Algorithm 2 and Theorem 15 (Section 4), and Section 5 (first-order definability).
- The counterexample to Lemma 9 (informal, item 4).
