# Differences between the formalization and the paper

Version formalized: Chapter 4 of G. Rétvári's D.Sc. dissertation (2020), which reproduces the PODC 2011 paper
(numbering Definition 4.1 … Theorem 4.17). The PODC text was not available, so slips listed here are slips of the
thesis text. Labels follow `mistakes-labeling.md`.

## Mistakes

1. 🔧 **Theorem 4.14, memory of the scheme.** With the paper's non-strict balls and an unspecified choice of
   "the closest landmark", every table can contain all `n` nodes for any landmark set: monotone selective
   algebras (e.g. widest path) with equal edge weights (`paperScheme_table_eq_univ`, `paperScheme_card_table`,
   instance `paperScheme_card_table_path3`). Strict balls do not help: with non-strict monotonicity the packet can
   bounce between `l_v` and its neighbour forever (`strictBall_loops`). Fixed by the strict lexicographic key
   `(w(p*_{x,v}), in-tree rank, x)` (`refinedScheme`, `theorem_4_14`, `refinedBall_subset`). Cowen's landmark
   selection giving `O(n^{2/3})` is not formalized.
2. ✏️ **Definition 4.3.** (SM) `w₁ ≺ w₂ ⊕ w₁` "for all `w₁, w₂ ∈ W`" is unsatisfiable (`w₁ = φ`,
   `not_isStrictlyMonotoneLit`). (N) fails in every algebra with a finite weight (`not_isCancellativeLit`). (C) forces
   `⊕ ≡ φ` (`isCondensedLit_iff`). We use `IsStrictlyMonotone` and `IsCancellative` for `w₁ ≠ φ`, and `IsCondensed`
   for finite `w₁, w₂, w₃`.
3. ✏️ **Lemma 4.12 / Theorem 4.11, degenerate case.** `W_φ = {φ}` is finite, so the cyclic-subsemigroup claim needs
   `w ≠ φ`. Both statements need a finite weight in the (sub)algebra: the algebra `{φ}` is delimited and SM
   (vacuously), yet every routing function implements it (`trivial_algebra`). Our `lemma_4_12` and `theorem_4_11`
   assume a finite weight.
4. ✏️ **Proposition 4.4, carrier of the product.** The literal product on `W_A × W_B` with `φ = (φ_A, φ_B)` is not
   delimited (`litProd_not_isDelimited`), and the M rule fails at elements `(φ_A, b)` (`litProd_not_isMonotone`).
   We use the product of the finite parts with a new `φ` (`lexProd`), for which the three rules hold under
   φ-free (SM), (N), (C) and nonempty finite parts. The proofs are ours; the paper cites Gurney–Griffin.
5. ✏️ **Table 4.2, row R.** `R = ((0,1], 0, ∗, ≥)` is not SM (`mostReliable_not_isStrictlyMonotone`); its
   subalgebra on `(0,1)` is (`mostReliableOpen_props`).
6. ✏️ **Table 4.2, row MRWS.** It is isotone (`mostReliableWS_isIsotone`), not ¬I.
7. Typos: "Theorem 4.12" in Section 4.3.2 is Lemma 4.12. The `Ω(n)` for `R` comes from Lemma 4.12, not
   Theorem 4.11.

## Proof gaps (statements true)

8. 🔧 **Lemma 4.10, converse, non-monotone case** ("preferred paths might contain loops"). Replaced by the
   triangle counterexample (`not_mapsToTree_of_not_monotone`). Delimitedness is not needed for the converse
   (`lemma_4_10_converse`; the paper's version is `lemma_4_10_converse'`). Case (c) of the proof is case (a).
9. **Lemma 4.10, sufficiency (different proof, not a gap).** The Kruskal argument is replaced by a cycle-property spanning tree obtained from
   CSLib's greedy spanner (`exists_isTree_forall_walk`, `exists_preferred_spanningTree`). The paper's argument is
   fine, only formalized differently. Not a mistake.
10. 🔧 **Theorem 4.14, mixed routes.** Only the pure landmark route is bounded. The actual route (towards `l_v` until
    the first node storing `v`) is bounded in `Scheme.weight_le_of_not_good`. Routes are paths (`Follows.isPath`).
    Consistent next hops (in-trees) are needed and built by a Dijkstra argument (`exists_isHO`, `exists_inTree`); the
    paper delegates them to [191, 192].
11. 🔧 **Theorem 4.17, counting.** The described family (`δ^p` targets with distinct words) is one graph up to
    isomorphism, and node labels chosen by the scheme can carry the words. We use `p ≈ n/4` centres, `δ = 2` and
    `q ≈ n/4` targets with arbitrary words, and do the counting ourselves (`card_bound`, `theorem_4_17`: memory
    `≥ n/8` at some centre for large `n`).

## Modelling choices and imprecisions

- **Order and weights.** `⪯` is the ambient `LinearOrder` of `W`; maximality is `w ⪯ φ`. Walk weights live in
  `A.Ext = W ∪ {1}` (`1` = empty walk), so `w^k` and products of edge weights are monoid operations.
- **Preferred paths** are minimum-weight paths among paths. Ties are arbitrary: any path of minimum weight counts.
  The paper's "broken arbitrarily but deterministically" is reflected only in the routing function generating one
  path.
- **`pw`** is the preferred weight (`φ` for unreachable pairs). Lemma 4.16 and the triangle inequality need
  monotonicity, because concatenated paths are walks (`pw_triangle`).
- **Routing functions** (§4.2): labels injective and `< n^c`; ports a bijection of the neighbours onto
  `{1,…,δ(u)}` (we require injective with values in that range, which is equivalent); local functions
  `R_u : ℕ → ℕ × ℕ`; initial header `L_V(t)`. "Implements" is required only for pairs with a traversable path, as in
  the paper.
- **Memory** is an arbitrary measure `mem : (ℕ → ℕ × ℕ) → ℕ∞` (the paper does not fix an encoding; `⊤` for
  functions without a finite code). The maximum in Definition 4.5 also
  ranges over edge weights (implicit in the paper). Graphs are over any finite `V : Type` with `n` elements.
  "Incompressible" is `∃ C > 0, eventually n ≤ C · M(n)`, and "compressible" is its negation, as in the paper's text.
- **Theorem 4.9** is stated as `M_A(n) ≤ f(n)` given a tree-routing scheme with memory `f` (`TreeRoutingScheme`,
  hypothesis for [74]). With `f = O(log n)` this gives compressibility (`theorem_4_9_compressible`).
- **Lemma 4.12** is stated as `M_S(n) ≤ M_A(n)` (for every `mem`, `c`, `n`) for the shortest-path algebra `S`.
  Proposition 4.8 (`S` incompressible) is an explicit hypothesis of `lemma_4_12` and `theorem_4_11`. The subalgebra
  is a set closed under `⊕`, delimited and SM on its elements, with a finite element.
- **Definition 4.13 / stretch schemes.** `ImplementsStretch k` requires the generated route to be a *path*. If
  routes could be walks, bouncing walks such as `c_i z c_i z' t` (weight `w_i^4 ⪯ w_i^{2k}` for `k ≥ 2`) would
  break the "routes are forced" step of Theorem 4.17's proof. Theorem 4.14's scheme produces paths, so requiring
  paths is consistent with the paper.
- **Theorem 4.14** is formalized for an abstract table-based forwarding scheme (`Scheme`), not inside the bit-level
  routing-function model. Delimitedness is not used anywhere. The memory claim is reduced to table contents
  `C(u) ∪ L` and ball containment; Cowen's landmark selection is not formalized.
- **Theorem 4.17** needs `CodeLength mem` (fewer than `2^b` local functions have code length `< b`), which holds
  for every code-length notion; the paper's "bits needed to encode" implicitly assumes it. It is satisfiable only
  with infinite values (`not_codeLength_of_ne_top`, `codeLength_top`). Condition (4.2) is
  used as `w_i^{2k} ≺ w_i ⊕ w_j` for all ordered pairs `i ≠ j`, which is equivalent to the paper's two inequalities.
- **Table 4.2 instances** use `ℕ+` costs/capacities (instead of `ℤ⁺`/`ℝ⁺`) and rationals in `(0,1]` for
  reliabilities. The "Local memory" column is derived from the hypotheses (`widestPath_compressible`,
  `shortestWidest_incompressible`).
- **Not formalized:** Proposition 4.6 / Observation 4.7 (except that `exists_inTree` is the regular ⇒
  destination-based direction), Cowen's / Thorup–Zwick's memory bounds, the non-delimited (BGP) results.
