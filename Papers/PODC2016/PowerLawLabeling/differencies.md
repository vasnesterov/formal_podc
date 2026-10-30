# Differences between the formalization and the paper

Paper: Petersen, Rotbart, Simonsen, Wulff-Nilsen, *Near-optimal adjacency labeling scheme for
power-law graphs*, arXiv:1502.03971v1 (full version of the PODC 2016 brief announcement).

## Definitions and model

1. **Labeling schemes** (`HasAdjLabeling`). The paper never defines labeling schemes formally. We
   use the following: a decoder (an arbitrary relation on bit lists) is fixed for the family of
   `n`-vertex graphs and may depend on `n`. Each graph gets labels of length `≤ X`, and adjacency of
   distinct vertices is decided by the decoder. Labels have variable length and the label size is
   the maximum length. Upper bounds give a concrete decoder that depends only on `⌈log₂ n⌉`. Lower
   bounds allow any decoder, which makes them stronger.
2. **`log n`** is read as `⌈log₂ n⌉` (`lg`), the length of an identifier. This holds in Theorems 1
   and 2 and in Definition 1 (where we use `Real.logb 2 n`). With the real `log₂ n` and ceiling-size
   identifiers, the stated bounds are not what the paper's scheme gives (the identifiers would cost
   `⌈log₂ n⌉` bits). We regard `⌈·⌉` as the standard convention (R4).
3. **`c`-sparse / `S_{c,n}`** is never defined. The proof of Theorem 1 uses `|E| ≤ cn`, so `Sparse c G`
   is `|E| ≤ c·n`, with `c ≥ 0` real.
4. **The constant `C`** in Definition 2 is never defined. We set `C = 1/ζ(α)` (`C`). Prop. 1's proof
   needs `Cζ(α) ≥ 1`. Thm 3's proof needs `Cζ(α) ≤ 1` (`Σ_{i ≤ i₁} ⌊Cn/i^α⌋ ≤ n`). (R4: standard
   normalisation of a power law; the only value consistent with the proofs.)
5. **`i₁`** is "the smallest integer with `⌊Cn/i₁^α⌋ ≤ 1`". We take the smallest *positive* integer
   (`i₁`); `i = 0` would qualify trivially.
6. **Definition 1** (`IsPowerLaw α C'`). The constant `C'` is a parameter. The paper's `C'` depends
   on `n` through `i₁/n^{1/α}`, which it nevertheless calls "a constant". We add `1 ≤ k`. This is
   automatic for `n ≥ 2`. It only excludes `n = 1`, where `n / log n = 1/0` is meaningless, and where
   with the Lean convention `x/0 = 0` the literal definition would make Prop. 3 false.
7. **Definition 2** (`IsProperPowerLaw α`) is transcribed literally, with `n = |V|`, condition 1 in
   `ℤ`, and conditions 3 and 4 for the stated ranges. As in the paper, the number of isolated
   vertices `|V₀|` is unconstrained.
8. **Asymptotics.** Theorem 3 ("for all `n` … `Ω(n^{1/α})`") becomes `∃ κ > 0, ∀ᶠ n, …`.
   Proposition 2 ("sparse") becomes `∃ c, ∀ n G, |E| ≤ cn`.

## Statements

* **Theorem 1** (`theorem1`): as stated, for every `n` and `c ≥ 0`. Our proof gives the slightly
  better `√(2cn⌈log n⌉) + ⌈log n⌉ + 1`, because thin vertices have degree `< f(n)`.
* **Theorem 2** (`theorem2`): as stated for `n ≥ 2` and `C' ≥ 2`. The paper's `C' ≥ 5^α` satisfies
  this. `C' ≥ 2` is needed for the threshold to lie in the range where Definition 1 applies,
  `f ≥ (n/log₂ n)^{1/α}`. Here too the proof gives `+ log n` instead of `+ 2 log n`.
* **Proposition 1** (`prop1`): exactly the stated bound `(C/(α-1)+2) n^{1/α} + i₁ + 3`, for `n ≥ 1`,
  `α > 1`.
* **Proposition 2** (`prop2`): for `α > 2`, with the explicit
  `c = C·ζ(α-1) + (C/(α-1)+8)²`.
* **Proposition 3** (`prop3`): `P'_α ⊆ P_α` for every `C' ≥ C'₀ = (C/(α-1)+8)^α + Cα/(α-1)`. This
  is not the paper's `C' ≥ (C/(α-1) + i₁/n^{1/α} + 5)^α + C/(α-1)`, because the paper's proof has
  the integral comparison in the wrong direction (see below). Classified as a proof repair:
  the paper's own constant also suffices, by the following reviewer's pen-and-paper argument
  (**not checked in Lean**). In Definition 1's range `k ≥ 2` (since `n / log₂ n > 1` for `n ≥ 3`, and
  the range is empty for `n ≤ 2`). Let `m = n^{1/α}`, `A = C/(α-1) + i₁/m + 5 ≥ 5`, `Δ` the maximum
  degree; Prop. 1 gives `Δ ≤ Am - 3m + 3`. If `k > Δ` the sum is `0`; otherwise put `t = Am/k ≥ 1`.
  Then `Σ_{i≥k} |V_i| ≤ (Δ-k+1) + [k=2] + Cnk^{-α} + Cnk^{1-α}/(α-1)`, `Δ-k+1 ≤ k(t-1) + 1`,
  `Cnk^{-α} = Ct^α/A^α` and `A^α n k^{1-α} = k t^α`, so it suffices that
  `Ct^α/A^α + 1 + [k=2] ≤ k(t^α - t + 1)`. With `C ≤ min(1, α-1)` (as `ζ(α) ≥ 1/(α-1)`),
  `A ≥ 5`, and `t ≥ 5/2` when `k = 2`, this elementary inequality holds for every `α > 1`
  (for `α ≥ 2` use `t^α ≥ t²`; for `α < 2` use `t^{α-1} - 1 ≥ (α-1) ln t`). The formalized
  `prop3` uses the cruder constant `C'₀` and does not need the lower end `(n/log n)^{1/α}` of the
  range.
* **Proposition 4** (`prop4`): proved under the extra hypothesis `c < n` (and `c > 0`). **False in
  general** (`prop4_false`): for `n = 2`, `c = 100`, 1-bit labels exist but `⌊√(cn)/2⌋ = 7`. For
  `c ≥ (n-1)/2`, `S_{c,n}` contains all graphs, so the bound cannot grow with `c`. This is a
  degenerate parameter corner: the paper intends constant `c` and growing `n` (R2 → ⚠️).
* **Theorem 3** (`theorem3_proper` for `P'_α`, `theorem3` for `P_α` with `C' ≥ C'₀`): for `α > 2`,
  `∃ κ > 0` such that for all large `n` every scheme needs `κ n^{1/α}` bits. We use
  `κ = (C/2)^{1/α}/4`. For `P_α` the Lean statement covers only `C' ≥ C'₀`, which exceeds the
  paper's threshold `(C/(α-1) + i₁/n^{1/α} + 5)^α + C/(α-1)`; for `C'` between the two it follows
  from `theorem3_proper` and the (unformalized) argument under Proposition 3 above.
* **Moon's bound** (`moon`): `⌊(m-1)/2⌋` for labels of length at most `ℓ`, via
  `2^{m(m-1)/2} ≤ (2^{ℓ+1}-1)^m`. The paper cites `⌊n/2⌋`, which is the fixed-length version. Our
  version suffices for Prop. 4 exactly and for Theorem 3. Requires `m ≥ 1`: for `m = 0`, any `X`
  works vacuously.

## Proofs

* **Prop. 1**: `k' = ⌊n^{1/α}⌋` in the proof must be `⌈n^{1/α}⌉`. The integral step and the final
  `+3` both come from the ceiling. Typo-level.
* **Prop. 3**: `Σ_{i=k}^d i^{-α} ≤ ∫_k^d x^{-α}dx` is false. The left endpoint term `k^{-α}` is
  missing. Also `|V_2| ≤ ⌈Cn/2^α⌉ + 1 ≤ Cn/2^α + 2`, not `+1`. Repaired with the telescoping bound
  `Σ_{i>k} i^{-α} ≤ k^{1-α}/(α-1)` (`sum_Ioc_rpow_neg_le`, proved without integrals) and a larger
  constant. The lower bound `k ≥ (n/log n)^{1/α}` of Definition 1 is not needed: the bound holds for
  every `1 ≤ k ≤ n-1`.
* **Prop. 4**: the proof mixes up the two `n`s (family size versus size of the embedded graph). As
  written, it shows the bound only for family sizes `⌊m²/c⌋`. We embed a graph on `⌊√(cn)⌋+1`
  vertices directly into `n` vertices.
* **Theorem 3**: the greedy phases are replaced by edge-maximal graphs (`exists_maximal_fill`).
  - Phase 1 omits "non-adjacent" from the pair condition, so the loop as written does not terminate.
    Its claim (all of `V_H` processed) holds for large `n`. We prove it by double counting
    (`bip_phase`): every `V'`-vertex is either adjacent to the deficient vertex or saturated by edges
    to `V_H`.
  - Phase 2's "at most one vertex of `V'` remains unprocessed" is false. The unprocessed vertices
    form a clique (targets 3, 3, 2 with edge order `ab, ac, bc` leave two). Repaired: the clique has
    at most `i₁ - 1` vertices with deficiency `< i₁` each, and all are completed with leaves of `V₁`
    (`bip_phase` again).
  - Phase 3 (parity): instead of moving a vertex from `V₁` to `V₂`, we choose `|V₁| ∈ {⌊Cn⌋-i₁,
    ⌊Cn⌋-i₁-1}` so that the target degree sum is even. Then no unprocessed leaf remains. Condition 1
    of Definition 2 allows both values.
  - Class sizes (`cnt`): we keep the paper's `|V₁|` (up to parity), `|V_d| = ⌊Cn/d^α⌋` for
    `2 ≤ d < i₁`, and one vertex of each degree `i₁ ≤ d < 2i₁` hosting `H`. The paper instead uses
    `n - n'` singleton degrees `i₁, …, i₁+n-n'-1`, with the extra ones outside `H`. We put the
    remaining vertices into `V₀` (isolated), which Definition 2 permits. With the paper's choice, the
    extra high-degree singletons would also have to be realized.
  - "for all `n`": the construction needs `n` large: `i₁ ≥ 3`,
    `⌊Cn⌋ ≥ i₁² + 2i₁ + 1`, `⌊Cn/2^α⌋ ≥ 2i₁² + 2i₁` (`eventually_construct`).

## Not formalized

* Proposition 5 (BA model, arboricity, external results [10, 11, 31]), the remark after it, and the
  induced-universal-graph consequences.
* Section 6 (experiments) and the threshold "prediction" heuristic `⌈(Cn/(α-1))^{1/α}⌉`.
