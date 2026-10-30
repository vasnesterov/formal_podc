# Differences between the formalization and the paper

Paper: Bar-Yehuda, Censor-Hillel, Maus, Pai, Pemmaraju, *Distributed Approximation on Power Graphs*, PODC 2020,
arXiv 2006.03746 v1. Verdict rules: `.claude/skills/formalize-paper/verdicts.md`.

## Errors and gaps in the paper

1. **Corollary 17, proof gap (R1 → 🛠️).** The proof applies Theorem 12 to the remaining graph `G²[U]`, which is
   not a square. Algorithm 2 is not a 5/3-approximation there. `Cor17Gap.corollary_17_proof_gap` gives a run of
   Phase I (`ε = 1/2`) that ends with `G²[U] = K₄,₄`, followed by a complete run of Algorithm 2 that outputs 8
   vertices while 4 suffice. The corollary itself is true. We prove the approximation part (`corollary_17`) with a
   new accounting (`Centralized.induced_bound`): on `G²[U₀]`, `18|S₂| ≤ 30|OPT ∩ U₀| + 2|V \ U₀|`, because a blue
   edge's midpoint is in `V1` or outside `U₀`. Combined with Lemma 5 (`2|S| ≤ 3|OPT ∩ S|`), this gives
   `3|S ∪ S₂| ≤ 5|OPT|`. Only the CONGEST variant (Phase I of Theorem 1) is formalized, not the CONGESTED CLIQUE
   one (Theorem 11). The same accounting works there, because it only uses that `S` is charged at ratio `≤ 3/2`.
2. **Lemma 6, proof (R1 → 🛠️).** "This implies `|I| < n/α`" is false (`lemma_6_strict_false`: `P₄`, `r = 2`).
   The argument gives `|I|·α ≤ n` (`card_mul_le_of_indep`), which suffices for the statement.
   - Our proof of `|I|·α ≤ n` uses disjoint balls of radius `⌊r/2⌋` and `|B(v, j)| ≥ min(n, j + 1)` in a connected
     graph (`card_ballF`). The paper instead assigns "`⌊r/2⌋` unique vertices on the path from `u` to `v`", which
     needs a second vertex of `I`. For `|I| = 1` it needs `r ≤ n`, which the hypothesis `r ≤ n` provides.
   - Hypothesis `1 ≤ r` is not needed for the first sentence (for `r = 0` the bound is trivial).
3. **Lemma 6, second sentence (borderline, not counted).** "(1 + 1/⌊r/2⌋)-approximation" is undefined for `r = 1`.
   We state it for `2 ≤ r ≤ n` (`lemma_6_approx`). With the convention `1/0 = ∞` the case `r = 1` is trivially true,
   so we do not count it as a statement error. In any case it would only be a degenerate parameter corner (R2).
4. **Theorem 12, degree-3 case (typo in proof).** The disjoint edges are `{y₁,z₁}, {y₂,z₂}, {x,y₃}`. The paper writes
   `{x,y₂}`, which meets `{y₂,z₂}`.
5. **Theorem 12, degree-2 case (routine detail).** `{z,y₁}` and `{x,y₂}` are disjoint because `z ≠ y₂`. This
   follows from triangle-freeness, which the paper does not mention. In the degree-3 case the existence of `z₁ ≠ z₂`
   outside `{x,y₁,y₂,y₃}` likewise uses triangle-freeness for `zᵢ ≠ yⱼ`. We prove these in `exists_step` and
   `inv_deg2`.
6. **Lemma 13 (3) (routine detail).** The paper does not explicitly exclude that the midpoint `v` left `V'` as an
   isolated vertex in part 1. It cannot have, since it has two remaining neighbours. This is covered by
   `Inv.triClosed`.
7. **Theorem 1, case `ε > 1`.** The claim "`G²`-MIS has size `≤ n/2` in a connected graph" fails for `n = 1`
   (degenerate, R2, inside a proof). This case is not formalized.
8. **Phase I, CONGEST implementation (prose slip, not formalized).** The pseudocode (line 4), Lemma 2 and
   Lemma 5 use "more than `1/ε` neighbours in `R`", but the description of the distributed symmetry
   breaking says "any vertex with degree at least `1/ε` in `R` is a candidate". With "at least", Lemma 5's
   bound `dᵢ ≥ l + 1` fails. We follow the pseudocode.
9. **Lemma 5 typo.** `Sᵢ = N(vᵢ) ∩ R` should read `N(cᵢ) ∩ R`.
10. **Theorems 20/22 typo.** `V_B = V(G_{x,y}) \ V_B` should read `\ V_A`.
11. **[CKP17] bit gadgets.** The order of the 4-cycle on `t_A, f_A, t_B, f_B` is not given. We take
    `t_A–f_A–t_B–f_B–t_A`, so the 2-independent sets are `{t_A,t_B}` and `{f_A,f_B}`, as the reduction needs.
12. **Lemma 24.** Lemma 24 follows without Lemma 23: restricting a cover to the core gives a
    cover of `G`, and the triangle `P[1]P[2]P[3]` forces 2 vertices per gadget. Lemma 23 is proved anyway.

## Modelling choices

- **Algorithm 2.**
  - The state stores `V'` only, with `E' := G²[V']`. This is justified by the paper's own remark that the remaining
    graph always equals `G²[V_R]`.
  - Isolated vertices may be removed at any time in parts 1 and 2. The paper removes them eagerly, so our runs are a
    superset of the paper's.
  - The degree-3 guard is "no vertex of degree 1 or 2", where the paper says "`< 3`". With eager removal the two
    agree; ours allows more runs.
  - In the degree-1/2/3 cases the vertex `x` (left isolated) is removed in the same step, as the paper's eager
    removal does.
  - The choices of triangle, `x`, `z`, `z₁`, `z₂` and the part-3 cover are nondeterministic. Part 3 is "any cover
    `C ⊆ V'` of `G²[V']` with `|C| ≤ 2|D|` for every cover `D ⊆ V'`". A maximal matching provides one
    (`exists_twoApprox`).
  - Theorem 12 is stated with `α = 5/3` (the abstract's value; the theorem says "a constant `α < 2`") as
    `3|S| ≤ 5|OPT|` for every vertex cover `OPT` of `G²`.
- **Polynomial time** is formalized as `run_length_le`: at most `n + 3` steps (for `init U₀`, at most `|U₀| + 3`).
  The cost of a step is not formalized.
- **Lemmas 13–15** are not separate theorems. Their content is in the invariant `Centralized.Inv`:
  - `noTri` is Lemma 13 (1) / Lemma 14 (1).
  - Red edges forming a matching and `s₁ ≥ |E^blue|` are used inside `blue_bound`, which proves Lemma 14 (4) as
    `3|V_{R'}| ≤ 2s₁` (generalized: `+ 2|V \ U₀|`).
  - `charge` combines `opt₁ ≥ (2/3)s₁` and `opt₂ ≥ (3/5)s₂` into `10s₁ + 9s₂ ≤ 15|OPT ∩ (U₀ \ V')|`.
  - `opt₃ ≥ s₃/2` is the 2-approximation in part 3.
  - The paper's `OPT_i` (optimal covers of `G²[W_i]`) are replaced by restrictions of one fixed cover `OPT`. This
    is equivalent for the final bound.
- **Algorithm 1 / Theorem 1.**
  - Only the sequential semantics is formalized, with `ε = 1/l`. The paper reduces general `ε ≤ 1` to this case.
  - Phase II takes any `R*` that is optimal among covers of `G²[U]` contained in `U`.
  - The CONGEST implementation and round count are not formalized. Formalized are their combinatorial inputs:
    Lemma 2's "`≤ l` neighbours in `U`" (`card_nbrs_U_le`), Lemma 3, and "`≤ n/(l+1)` iterations"
    (`phase1_length`).
  - Lemma 3 is stated as a characterization of `G²[U]`-adjacency in terms of `F`.
- **Corollary 17.**
  - Formalized only for Phase I of Theorem 1 followed by Algorithm 2 on `G²[U]`, in sequential semantics.
  - "Nodes only use polynomial computations" and the `O(n)` round bound are not formalized.
  - Our proof does not use that Phase I has finished. Any reachable Phase-I state works.
- **Lower bounds (Theorems 20, 22).**
  - CSLib's deterministic CONGEST model with exactly `B` bits per edge, direction and round. Node input is the
    adjacency row (and the weight for Theorem 20).
  - "Computes the minimum (weighted) vertex cover of `G²`" is formalized as "all nodes accept after `T` rounds iff
    `H²` has a cover of size (weight) `≤ W'`" (the decision version used by Theorem 19). Turning an MVC output into
    the decision needs an aggregation the paper does not discuss either.
  - The bound is stated as `k² ≤ T · 2 · |cut| · B + 2` with `|cut| = 4 log k`, and with `n = |V(H)|` as
    `n² ≤ c log² n (8 T B log n + 2)` for the family sizes `n_L` only. There is no padding to arbitrary `n`.
  - Theorem 20 uses weights in `{0, 1}`. Section 3.2's "WLOG positive weights" is not assumed there, as in the
    paper.
  - The randomized versions take `CC^R(DISJ_K) ≥ κK` as a hypothesis, which is not proved in CSLib. The
    constant `κ` is real and the coin spaces are nonempty; otherwise the hypothesis is only satisfiable
    with `κ = 0` (empty coin spaces make `ret true` a zero-error, zero-cost protocol; a natural-number
    constant `κ ≥ 1` would claim `CC^R(DISJ_K) ≥ K`, false for large `K`, since `CC^R(DISJ_K) ≈ 0.49K`).
  - The `_connected` versions require correctness only on connected members of the family (all members except
    `x = y = 1`).
- **Graph power.** `G.power r` uses `edist ≤ r`, so unreachable pairs are never adjacent. The paper's `G²` ("at most
  two hops") agrees.
