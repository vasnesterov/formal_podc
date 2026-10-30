# Differences between the formalization and the paper

Paper: Bareilles, Bouaziz, Fageot, El Mhamdi, *Byzantine Machine Learning: MultiKrum and an Optimal
Notion of Robustness*, PODC 2026 (brief announcement); formalized from the full version
arXiv:2602.03899v1. Verdict rules: `.claude/skills/formalize-paper/verdicts.md` (R1–R6).

## Statement-level issues in the paper

1. **Theorem 1, display (1): `≥` instead of `≤`.** The theorem is announced as an upper bound
   ("has the following upper-bound"), the proof concludes `κ⋆_m ≤ min(κ₁, κ₂(m))`, and the paper
   uses it as an upper bound everywhere, but the display reads `κ⋆_m ≥ (n-f)/(n-2f) min(...)`.
   Read literally it is false: `theorem_1_as_written_false` (for `f = 0`, `m = n`, MultiKrum is the
   mean, `κ⋆ ≤ 0 < 1 =` right-hand side). Typo with evident intent (R3) → ⚠️. We prove the
   intended `≤` (`theorem_1`).
2. **`n = 1` (degenerate).** With the paper's own convention `0/0 = -∞`, for `n = 1` (`f = 0`) Krum
   (= the only MultiKrum rule, `F(x) = x₁`) has `κ⋆ = -∞`: the only reference set is `{1}`, with
   variance 0 and zero bias. Hence Proposition 1 (this `F` is robust but `κ⋆ ≥ f/(n-2f) = 0`
   fails), Theorem 3 for odd `n` (`κ⋆₁ ≥ (n-1)/(n-2f+1) = 0`) and Theorem 4 (`n > 3f`,
   `κ⋆_{n-f} ≥ 0`) all fail at `n = 1` (`kappaStar_eq_bot_of_n_eq_one`,
   `exists_isMultiKrum_kappaStar_eq_bot`). Degenerate case (R2) → ⚠️. We assume `n ≥ 2` and a
   nontrivial vector space (`d ≥ 1`; for `d = 0` every ratio is `0/0` as well).
3. **Theorem 3 has no explicit hypotheses.** We assume Definition 2's standing `f ≤ n/2` (for
   `n = 2f`, `f ≥ 1`, the bound holds trivially because `κ⋆ = +∞`,
   `kappaStar_eq_top_of_n_eq_two_mul`; the paper's construction itself needs `n - 2f > 0`) and
   `n ≥ 2` (even case) / `n ≥ 3` (odd case). For `n = 2` the paper's
   construction (`n/2 - 1 = 0` copies of `e`) has zero variance; the bound is `0` there and we prove
   it with another instance (`zero_le_kappaStar`). (R4, R2.)
4. **Proposition B.1 needs `f ≥ 1`**: for `f = 0` its formula divides by `f = 0` (and the
   configuration has zero variance). We state B.1 for `f ≥ 1`; Theorem 4 is proved for all `f`
   (`f = 0` gives the bound `0`, true for `n ≥ 2`).

## Proof-level issues (statements true)

5. **Proposition B.1, wrong bias.** The proof computes
   `‖x̄_{S⋆_m} - x̄_S‖ = (a·f/(n-f) + (m-a)(1-ε))/m`; the correct value is
   `f/(n-f) + (m-a)(1-ε)/m = (m·f/(n-f) + (m-a)(1-ε))/m` (since `x̄_S = -f/(n-f) e`). The stated
   `R(n,f,m)` is therefore not the limit of the ratio, but it is smaller than the correct limit
   `R'(n,f,m) = (n-f)²/(f(n-2f)) (f/(n-f) + (m-a)/m)²` (as `a ≤ m`), so the *statement* of B.1 is
   true. Consequence: B.1 as stated does not recover Theorem 4 at `m = n - f` (it gives
   `f(2n-3f)²/((n-2f)(n-f)²) < 4f/(n-2f)`), contrary to "closed-form lower bounds for all `m`".
   We prove the corrected bound `R'` and derive both B.1 and Theorem 4 from it. → 🛠️
6. **Theorem 2, upper bound in the proof.** The proof derives
   `m† ≤ (A² + √(A⁴ + 2Cf²))/C` and claims "both bounds reduce to `n/C (1+o(1))`". The upper bound
   reduces to `2n/C (1+o(1))` (at `f = 0` it is exactly `2n/C = 2 m†`:
   `paper_upper_bound_at_f_zero`, `paper_upper_not_asymp`), so the proof does not establish the
   asymptotics. Theorem 2 is true: `m† C / n = g(f/n)` exactly for an explicit continuous `g` with
   `g(0) = 1` (`mDagger_mul_div`, `theorem_2`). → 🛠️
7. **Theorem 6, optimisation over `α₁`, `α₂`.** The minimisers `α₁ = √(B/A)`, `α₂ = √(u/(2m))` need
   `A, B, u > 0`. We avoid `α₁` altogether (triangle inequality for the norm gives
   `‖a + b‖² ≤ (√A + √B)²` directly) and treat `u = 0` separately. Routine.
8. **Theorem 4 / B.1 score values.** The paper gives `s(x_j) = f/(n-f)` and
   `s(x_k) = (1-ε)(n-2f)/(n-f)`; the exact values are `f(1-ε)²/(n-f)` and `(1-ε)²(n-2f)/(n-f)`.
   Only the strict ordering `s(0) < s((1-ε)e) < s(-e)` matters, and it holds. Typos.

## Typos and small slips (no effect)

- Section 2.1: `s^X : ℝⁿ → ℝ` should be `ℝ^d → ℝ`.
- Lemma 3 proof: "`|U(x)| = |S ∪ N(x)| = |S| + |N(x)| - |S ∩ N(x)|`" — `∪` and `∩` are swapped.
- Lemma 2 proof: "averaging over the larger set `S`" — `S` has the same size `n - f` as `N(x_i)`;
  the inequality holds because `N(x_i)` minimises the sum.
- Theorem 2 proof: "`Cx⁴ = (A + f/x)²`" should be `Cx² = (A + f/x)²` (the next display
  `Cx⁴ = A²x² + 2Afx + f²` is right).
- After Theorem 2: "the `κ^<_2(m)` regime becomes active" should be `κ^>_2(m)`.
- Section 5: "the upper bound of Theorem 3" (should be Theorem 1), "Theorems 3 and 4 for the upper
  bound `m = 1`" (lower bound); B.1 proof: "`(1 + ε)e`" should be `(1 - ε)e`; Section 3.2 calls the
  bounds of Appendix B `κ†_m`.
- Table 1 lists for `(n-f)`-MultiKrum the bound `(n-f)/(n-2f) κ^>_2(n-f)` without the `min` with
  `(√2+1)²` of Theorem 1; this entry is *larger* than the Krum entry when `f/(n-f)` is close to 1
  (e.g. `n = 19`, `f = 9`: `κ^>_2(10) ≈ 6.54 > (√2+1)² ≈ 5.83`). The claim "MultiKrum's bounds are
  never worse than Krum's" holds for Theorem 1's bound (with the `min`), not for the table entry.

## Modelling choices

- **Vectors** live in an arbitrary real inner product space `E` (paper: `ℝ^d`). Upper bounds hold
  for every `E`; lower bounds assume `Nontrivial E` (paper: `d ≥ 1`, `e = e₁`).
- **Scores.** The paper fixes a tie-breaking `N(y)` of the `n-f` nearest points; we define the score
  as the minimum of `∑_{j ∈ T} ‖y - x_j‖²` over all `(n-f)`-sets `T` (`nearestSum`), and prove that
  every valid `N(y)` attains it (`IsNearest.sum_eq_nearestSum`), so the score does not depend on
  tie-breaking.
- **MultiKrum tie-breaking.** `IsMultiKrum f m F` says that `F` outputs the mean of *some* valid
  `S⋆_m` on every input. Upper bounds hold for every such `F`; lower bounds also hold for every such
  `F` (constructions with strictly separated scores, or where all valid selections give the same
  output). Non-vacuity: `exists_isMultiKrum`.
- **`κ⋆` is an `EReal` supremum** (`kappaStar`), with `0/0 = -∞` as in the paper and `a/0 = +∞` for
  `a > 0` (the paper does not say; this is the standard extended-real convention and the one under
  which "`κ⋆ < ∞` iff robust" is meaningful). The first part of Proposition 1 (`κ⋆ < ∞ ⇒ n - 2f > 0`)
  uses it: for `n = 2f` some instance has `Σ_S = 0` and nonzero bias. `kappaStar_le_iff`: `κ⋆ ≤ c` iff
  `‖F(x) - x̄_S‖² ≤ c Σ_S` for all `x`, `S`, which is how upper bounds are stated.
- **Theorem 2** is formalized for real `n, f` (`0 ≤ f`, `2f < n`), which contains the integer case;
  "`= n/C (1 + o(1))` as `f/n → 0`" is stated in ε–δ form (`theorem_2`) and filter form
  (`theorem_2_tendsto`).
- Remark 1 (comparison with the original Krum score of [BEGS17], which excludes `x_i`) is not
  formalized; we use the paper's own Definition 1.
