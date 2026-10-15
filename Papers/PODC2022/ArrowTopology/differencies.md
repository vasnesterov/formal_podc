# Differences between the formalization and the paper

Paper: S. Rajsbaum, A. Raventós-Pujol, *A Distributed Combinatorial Topology Approach to Arrow's
Impossibility Theorem*, PODC 2022 ("PODC version"). Full version: *A Combinatorial Topology Approach to
Arrow's Impossibility Theorem*, MPRA 120023 (2024) ("full version"). Numbering is the PODC numbering unless
stated otherwise.

**Overall verdict.** Arrow's theorem and its combinatorial-topology proof (Sections 2, 3, 5) are correct, up to
small gaps that we repaired (items 6, 9, 10). Section 4 of the PODC version (domain restrictions) contains
a false theorem (item 13) and missing hypotheses (item 12). The full version corrects them, and we verified its corrected theorem (item 15).

## Model and definitions (Section 2)

1. **Preferences.** `Pref X` is a bundled strict total order. `X` is an arbitrary type, possibly infinite, as
   Lemma 5.1 allows. Voters form an arbitrary type `ι`; Theorems 2.1 and 2.2 assume `ι` finite with
   `2 ≤ card ι` (the paper's `n ≥ 2`).
2. **IIA** is stated as: if `(R i).P a b ↔ (S i).P a b` for all `i`, then `(F R).P a b ↔ (F S).P a b`.
   For strict total orders this is the paper's "same order on `{a, b}`".
3. **Vertices are sets.** As in the paper, a vertex of `N_I` is the set `U^σ_{αβ}` of profiles itself, so
   `U^σ_{αβ} = U^{−σ}_{βα}` holds automatically. Simplices are finite vertex sets with a common profile
   (nerves, `PreAbstractSimplicialComplex`). For computations with three alternatives we use an
   equivalent "sign model" (`SignModel.lean`) and prove the correspondence (`ThreeAlt.lean`,
   `theorem_2_2_base`).
4. **Theorem 2.2 without "chromatic".** The PODC statement asks only for a simplicial map. The full version
   (Theorem 5) adds "chromatic", and the translation to Arrow's classical setting (full-version Prop. 3)
   needs it. We prove that every unanimous simplicial map `N_I → N_O` is automatically chromatic
   (`isChromatic_of_unanimous`). So the PODC statement is correct as written, and `theorem_2_2` proves it
   without a chromaticity hypothesis.
5. **Propositions 3 and 4 of the full version.** The PODC version only sketches them (Section 2.3.3).
   The forward direction (`prop_3_forward`) and the unanimity equivalence (`prop_4_unanimity`) need at
   least one voter. With no voters all the sets `U^σ_{ab}` coincide, so the induced map cannot be
   chromatic, and unanimity of `F` is unsatisfiable. This is irrelevant for `n ≥ 2`.

## Index lemma and Lemma 3.2 (Section 3)

6. **Index lemma (Theorem 3.1).** The paper's hypotheses are: "every edge lies in one or in an even number
   of triangles", and the orientation pairs the induced orientations. We formalize the orientation
   condition directly: on every edge that is not a boundary edge, the two directions are induced equally
   often (`IsOriented`). This implies the "even number" condition. The triangles form a finite family
   `T → V × V × V` (possibly with repetitions). The proof is the paper's double-counting argument.
7. **Lemma 3.2 (orientability).**
   - The proof's pairing ("`σ₃` and `σ₃'` are paired if they are equal on each component but one") is not a
     pairing when `k ≥ 2` coordinates are free. We pair by flipping a fixed free coordinate
     (`card_even_eq_card_odd`).
   - Typo: "if `σ₁(i) = σ₂(i) = +` (resp. `−`), then `σ₃(i) = +` (resp. `+`)" should read
     "`σ₃(i) = −` (resp. `+`)".
   - We prove the lemma for **any** number of voters (as the paper's proof does) and also characterise the
     boundary edges: `{U^α_j, U^β_{j'}}` is a boundary edge iff `α = β` (`isBoundary_iff`). The paper uses
     this characterisation (Figure 7) without proof.
8. **Parity convention.** The orientation `AB → BC → CA` is used when the product of all signs is `+1`
   (additively: `parity = 0` in `ZMod 2`), and `AB → CA → BC` otherwise. This is the paper's convention.
9. **Proof of Theorem 2.2 for `n = 2`, `|X| = 3` (Section 3.3).** The paper says "the two remaining
   contributions to `I` have to be `−1` each". This needs each of them to lie in `{0, −1}`. That holds
   because a non-unanimous Condorcet cycle is oriented opposite to the unanimous ones, and its contribution
   is `−1` exactly when its three signs are equal (`cyc_split`). The paper does not state this step; we
   prove it. The other steps are formalized as in the paper: `C = 0` (`content_eq_zero`), `I = 0`
   (`index_eq_zero`), the boundary is the four Condorcet cycles (`index_eq`, `boundary_multiset`, the
   latter checked by kernel `decide`), the unanimous cycles contribute `+1` each (`cyc_unanimous`), and
   the triangle `{U^{−+}_{AB}, U^{−+}_{BC}, U^{+−}_{CA}}` separates the two split cycles.

## Reduction (Section 5)

10. **Lemma 5.1 — gap (repaired).** The auxiliary profile `x R' b R' a R' y` / `a R' y R' x R' b` needs
    `a, b, x, y` pairwise distinct. But `a, b` are arbitrary and `x, y` are fixed in advance, so e.g.
    `a = x` breaks the construction. Repair: the dictator `k` of `F̄` dictates every pair inside the triple
    `T = {x, y, z}`.
    - If `a, b ∈ T`, IIA finishes the proof.
    - Otherwise at most one of `a, b` is in `T`. We run the construction with two elements `u ≠ v` of
      `T \ {a, b}` in place of `x, y` (`arrow_of_three`).
11. **Lemma 5.2 — typos.** In Step 3, "`x F^n(R) z`" and "`z F^n(R) y`" should read "`x F^n(R') z`" and
    "`z F^n(R') y`". The conclusion `x F^n(R') y` is then transferred back to `R` by IIA, since `R'` and `R`
    agree on `{x, y}`. Otherwise the proof is formalized as written (`arrow_of_two_voters`). Voters are
    `Fin n`; the paper's voter `n` is `Fin.last`, and voters 1 and 2 are indices 0 and 1.

## Domain restrictions (Section 4)

All Section 4 statements concern `n = 2`, `|X| = 3`. A *domain* is a set `D` of profiles. An aggregation map
on `D` must satisfy unanimity and IIA for profiles in `D`; it is dictatorial if one voter dictates on `D`
(`AdmitsNonDictatorial`). The cylinders `C₁`, `C₂`, critical profiles, blue edges, critical pairs and critical
triples are given explicitly (`Domains.lean`). We obtained `C₁` as the connected component of the torus `T`
containing `(ABC, ACB)` and `(BAC, ACB)` (Figure 9) and checked it against Table 1 of the full version. The
statements are reduced to sign functions on the 12 vertices (`admitsNonDictatorial_iff_sign`) and decided by
the kernel.

12. **Proposition 4.1, last sentence — missing hypothesis.** The sentence says "every domain contained in one of
    these maximal domains belongs to `D_T`". Read literally it is false, but only because "non-dictatorial" is
    not inherited by subdomains that lose a vertex of `N_I`.
    - Counterexample: the one-profile domain `{(ABC, ACB)}` lies in every `T \ {R₁, R₂}`, yet admits no
      non-dictatorial map. Unanimity forces `F(R) ∈ {ABC, ACB}`, which is one voter's preference
      (`prop41_moreover_false`). The empty domain is another trivial counterexample. Both drop vertices of
      `N_I`.
    - Correct statement: the sentence holds for subdomains in which every pair is free, i.e. which keep all
      12 vertices (`prop41_moreover_of_pairFree`, via `admits_of_subset_of_pairFree`). This also follows
      from the full version's Theorem 6: the removed profiles form a critical pair, or two profiles of a
      critical triple whose third (antiunanimity) profile is not in `T`.
    - The rest of Prop. 4.1 is correct (`prop41_admits`, `prop41_maximal`), and the condition "different
      blue edges" is necessary (`prop41_equal_blueEdge`).
13. **Theorem 4.2 — false.** It claims that `N_I \ {R₁, R₂}`, with `R₁ ∈ C₁` and `R₂ ∈ C₂` critical and having
    *different* blue edges, admits a non-dictatorial map.
    - This fails whenever the two blue edges are adjacent, i.e. share a vertex (12 of the 30 choices,
      `thm42_not_admits_of_adjacent`). The antiunanimity profile spanned by the two blue edges is still in
      the domain and forces dictatorship.
    - Explicit instance: `R₁ = (BAC, ACB)`, `R₂ = (CBA, ACB)`, with third profile `(BCA, ACB)`
      (`thm42_counterexample`, `thm42_false`).
    - The statement is true for disjoint blue edges (critical pairs: `thm42_admits_of_disjoint`,
      `thm42_maximal`).
    - The "moreover" sentence has the same missing hypothesis as in item 12: `{(ABC, ABC)}` is a
      counterexample (`thm42_moreover_false`). For disjoint blue edges it holds for subdomains in which all
      pairs are free (`thm42_moreover_of_pairFree`).
    - The full version replaces Theorem 4.2 by Theorem 6, which adds critical *triples*.
14. **Full version, example of a critical triple — wrong.** "`R₁ = (BAC, ACB)`, `R₂ = (BCA, ABC)`,
    `R₃ = (BCA, ACB)` is a critical triple" is false: `(BCA, ABC)` lies in `C₁`, not `C₂`. Removing these three
    profiles leaves a dictatorial domain (`paper_triple_example_not_critical`). The intended `R₂` is
    `(CBA, ACB)`, as in case (f) of the full version's Table 1. This is a typo-level error.
15. **Full version, Theorem 6 (characterization) — verified.** Let `D` be a domain in which every pair of
    alternatives is free. Then `D` admits a unanimous, IIA, non-dictatorial map iff `D` misses both profiles
    of some critical pair (18 of them) or all three profiles of some critical triple (12 of them) (`thm6`).
    The paper's words "does not intersect the interior of" are read as "misses these profiles".
16. **Section 4.2 (polarised domain).** The aggregation map is well defined, unanimous, IIA and non-dictatorial
    (`ThreeAlts.polarised_admits`), for any three alternatives `x, y, z` with `z` the "left-wing" party. This
    is consistent with Theorem 6 (`polarised_misses_criticalPair`).
    - **Non-contractibility is not formalized**: Mathlib has no geometric realisation of abstract simplicial
      complexes. We prove the combinatorial certificate instead: the induced complex has 12 vertices,
      36 edges and 16 triangles, so its Euler characteristic is `−8 ≠ 1` (`polarised_fVector`,
      `polarised_euler`). The standard fact "contractible ⇒ χ = 1" is not formalized.
    - The paper's sentence "deleting a triangle on each of the concentric cylinders" is imprecise: the
      domain contains 4 of the 6 unanimous and 4 of the 6 opposite profiles.
17. **Section 4.1's index-lemma argument (full version, Figure 11)** is not formalized as such. Its conclusion
    ("`C₁` is dictatorial") is proved by exhaustive kernel computation (`not_admits_C1`).

## Not formalized

- **Vertex counts and dimension (Section 2.3.2).** We prove the vertex counts for every finite `X`: `N_O` has
  `|X|(|X|−1)` vertices (`card_VO`), and `N_I` has `|X|(|X|−1)2^{n−1}` vertices for `n ≥ 1`
  (`card_VI`, stated as `2·#V = |X|(|X|−1)2^n`). The dimension claim `(|X|+1)(|X|−2)/2`, cited from
  Baryshnikov, is not formalized.
- **The remark that Arrow's theorem fails for infinitely many voters** (cited from [27]) is not formalized.
- **Ties / weak orders** ([10, Lemma 1], cited) are not formalized.
- **Section 6** (relation to distributed tasks) is an informal analogy. Only its counting claims are
  checked (`Counts.lean`).
- **Remarks 2.1–2.3** (adjacent triangles differ by one transposition) are illustrative and not formalized.
- **The pivotal-voter proof** (full version Section 5) is not part of the PODC paper and is not formalized.
