import Mathlib

/-!
# Lemma 3.12: packing of distributions in `ℓ₁`

Lemma 3.12 of [KOS18] states: *if `U` is a set of distributions on `[d]` whose pairwise `ℓ₁`
distances exceed `1/2`, then `|U| < 5^d`.*

The statement is true, but the paper's volume argument is sloppy: it intersects the `ℓ₁` balls with
`[0,1]^d` (after which balls around different centres no longer have equal volume) and uses the
wrong volume formula `(4r)^d/(d+1)!` for an `ℓ₁` ball of radius `r`. We use the following repaired
argument, which needs no explicit volume formula.

Work in `E = PiLp 1 (Fin d → ℝ)` with an additive Haar measure `μ`. The open balls `B(x, 1/4)`,
`x ∈ U`, are pairwise disjoint (triangle inequality) and, since `‖x‖₁ = 1`, contained in
`B(0, 5/4) \ B(0, 3/4)`. By translation invariance and scaling, `μ B(x, r) = r^d · μ B(0, 1)` with
`0 < μ B(0, 1) < ∞`. Hence `|U| (1/4)^d + (3/4)^d ≤ (5/4)^d`, i.e. `|U| + 3^d ≤ 5^d`, so `|U| < 5^d`.
No case split on `d = 0` is needed (then no distribution exists and `U = ∅`). Separation `> 1/2`
is only used as `≥ 1/2`.

The general packing bounds (`card_add_three_pow_le_five_pow_of_norm_eq_one`,
`card_le_five_pow_of_norm_le_one`) hold in any finite-dimensional real normed space.
-/

open MeasureTheory Metric Module

namespace Podc.InteractiveDistributedProofs.LowerBound

section General

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

-- CSLib candidate
omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
/-- Volume core of the packing bound: if `S` is `1/2`-separated and every point of `S` satisfies
`r₀ + 1/4 ≤ ‖x‖ ≤ R - 1/4`, then the disjoint balls `B(x, 1/4)`, `x ∈ S`, together with `B(0, r₀)`
fit into `B(0, R)`. -/
theorem card_mul_measure_ball_add_le [MeasurableSpace E] [BorelSpace E] (μ : Measure E)
    [μ.IsAddHaarMeasure] {S : Finset E} {r₀ R : ℝ} (hr : r₀ ≤ R)
    (hS : ∀ x ∈ S, r₀ + 1 / 4 ≤ ‖x‖ ∧ ‖x‖ + 1 / 4 ≤ R)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 / 2 ≤ dist x y) :
    S.card * μ (ball (0 : E) (1 / 4)) + μ (ball (0 : E) r₀) ≤ μ (ball (0 : E) R) := by
  have hdisj : (S : Set E).PairwiseDisjoint (fun x => ball x (1 / 4)) := by
    intro x hx y hy hxy
    exact ball_disjoint_ball (by linarith [hsep x hx y hy hxy])
  have hdisj2 : Disjoint (⋃ x ∈ S, ball x (1 / 4)) (ball (0 : E) r₀) := by
    rw [Set.disjoint_iUnion₂_left]
    intro x hx
    apply ball_disjoint_ball
    rw [dist_zero_right]
    linarith [(hS x hx).1]
  have hsub : (⋃ x ∈ S, ball x (1 / 4)) ∪ ball (0 : E) r₀ ⊆ ball (0 : E) R := by
    refine Set.union_subset (Set.iUnion₂_subset fun x hx => ball_subset_ball' ?_) ?_
    · rw [dist_zero_right]; linarith [(hS x hx).2]
    · exact ball_subset_ball hr
  calc S.card * μ (ball (0 : E) (1 / 4)) + μ (ball (0 : E) r₀)
      = μ (⋃ x ∈ S, ball x (1 / 4)) + μ (ball (0 : E) r₀) := by
        rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_ball)]
        simp [Measure.addHaar_ball_center]
    _ = μ ((⋃ x ∈ S, ball x (1 / 4)) ∪ ball (0 : E) r₀) :=
        (measure_union hdisj2 measurableSet_ball).symm
    _ ≤ μ (ball (0 : E) R) := measure_mono hsub

-- CSLib candidate
/-- Packing bound on the unit sphere of a finite-dimensional real normed space: a finite set of unit
vectors with pairwise distances `≥ 1/2` has at most `5^n - 3^n` elements, `n = finrank ℝ E`. -/
theorem card_add_three_pow_le_five_pow_of_norm_eq_one {S : Finset E}
    (hS : ∀ x ∈ S, ‖x‖ = 1) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 / 2 ≤ dist x y) :
    S.card + 3 ^ finrank ℝ E ≤ 5 ^ finrank ℝ E := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar
  have key := card_mul_measure_ball_add_le μ (r₀ := 3 / 4) (R := 5 / 4) (by norm_num)
    (fun x hx => by rw [hS x hx]; norm_num) hsep
  rw [Measure.addHaar_ball_of_pos μ _ (by norm_num : (0 : ℝ) < 1 / 4),
    Measure.addHaar_ball_of_pos μ _ (by norm_num : (0 : ℝ) < 3 / 4),
    Measure.addHaar_ball_of_pos μ _ (by norm_num : (0 : ℝ) < 5 / 4)] at key
  set c := μ (ball 0 1)
  set n := finrank ℝ E
  have hc0 : c ≠ 0 := (measure_ball_pos μ _ one_pos).ne'
  have hctop : c ≠ ⊤ := measure_ball_lt_top.ne
  have h : ENNReal.ofReal (S.card * (1 / 4) ^ n + (3 / 4) ^ n) * c ≤
      ENNReal.ofReal ((5 / 4) ^ n) * c := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast, add_mul, mul_assoc]
    exact key
  rw [ENNReal.mul_le_mul_iff_left hc0 hctop, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have h4 : (S.card : ℝ) + 3 ^ n ≤ 5 ^ n := by
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4 ^ n)
    have e1 : (4 : ℝ) ^ n * (S.card * (1 / 4) ^ n + (3 / 4) ^ n) = S.card + 3 ^ n := by
      rw [mul_add, mul_left_comm, ← mul_pow, ← mul_pow]; norm_num
    have e2 : (4 : ℝ) ^ n * (5 / 4) ^ n = 5 ^ n := by rw [← mul_pow]; norm_num
    linarith
  exact_mod_cast h4

-- CSLib candidate
/-- Packing bound in the unit ball of a finite-dimensional real normed space: a finite set of
vectors of norm `≤ 1` with pairwise distances `≥ 1/2` has at most `5^n` elements,
`n = finrank ℝ E`. -/
theorem card_le_five_pow_of_norm_le_one {S : Finset E}
    (hS : ∀ x ∈ S, ‖x‖ ≤ 1) (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 / 2 ≤ dist x y) :
    S.card ≤ 5 ^ finrank ℝ E := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  set μ : Measure E := Measure.addHaar
  have key := card_mul_measure_ball_add_le μ (r₀ := -1) (R := 5 / 4) (by norm_num)
    (fun x hx => ⟨by linarith [norm_nonneg x], by linarith [hS x hx]⟩) hsep
  rw [ball_eq_empty.2 (show (-1 : ℝ) ≤ 0 by norm_num), measure_empty, add_zero,
    Measure.addHaar_ball_of_pos μ _ (by norm_num : (0 : ℝ) < 1 / 4),
    Measure.addHaar_ball_of_pos μ _ (by norm_num : (0 : ℝ) < 5 / 4)] at key
  set c := μ (ball 0 1)
  set n := finrank ℝ E
  have hc0 : c ≠ 0 := (measure_ball_pos μ _ one_pos).ne'
  have hctop : c ≠ ⊤ := measure_ball_lt_top.ne
  have h : ENNReal.ofReal (S.card * (1 / 4) ^ n) * c ≤ ENNReal.ofReal ((5 / 4) ^ n) * c := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast, mul_assoc]
    exact key
  rw [ENNReal.mul_le_mul_iff_left hc0 hctop, ENNReal.ofReal_le_ofReal_iff (by positivity)] at h
  have h4 : (S.card : ℝ) ≤ 5 ^ n := by
    have := mul_le_mul_of_nonneg_left h (by positivity : (0 : ℝ) ≤ 4 ^ n)
    have e1 : (4 : ℝ) ^ n * (S.card * (1 / 4) ^ n) = S.card := by
      rw [mul_left_comm, ← mul_pow]; norm_num
    have e2 : (4 : ℝ) ^ n * (5 / 4) ^ n = 5 ^ n := by rw [← mul_pow]; norm_num
    linarith
  exact_mod_cast h4

end General

/-- Lemma 3.12 of [KOS18]. A family of distributions on `[d]` (vectors in `ℝ^d` with nonnegative
entries summing to `1`) whose pairwise `ℓ₁` distances exceed `1/2` has fewer than `5^d` members. -/
theorem lemma_3_12 {d : ℕ} (U : Finset (Fin d → ℝ))
    (hdist : ∀ μ ∈ U, (∀ i, 0 ≤ μ i) ∧ ∑ i, μ i = 1)
    (hfar : ∀ μ ∈ U, ∀ η ∈ U, μ ≠ η → 1 / 2 < ∑ i, |μ i - η i|) :
    U.card < 5 ^ d := by
  let E := PiLp 1 (fun _ : Fin d => ℝ)
  have hrank : finrank ℝ E = d := by
    rw [(WithLp.linearEquiv 1 ℝ (Fin d → ℝ)).finrank_eq, Module.finrank_fin_fun]
  let S : Finset E := U.image (WithLp.toLp 1)
  have hcard : S.card = U.card := Finset.card_image_of_injective _ (WithLp.toLp_injective 1)
  have key := card_add_three_pow_le_five_pow_of_norm_eq_one (S := S) ?_ ?_
  · rw [hrank, hcard] at key
    have : 1 ≤ 3 ^ d := Nat.one_le_pow _ _ (by norm_num)
    omega
  · simp only [S, Finset.mem_image]
    rintro _ ⟨μ, hμ, rfl⟩
    rw [PiLp.norm_eq_of_L1]
    simp only [Real.norm_eq_abs]
    rw [← (hdist μ hμ).2]
    exact Finset.sum_congr rfl fun i _ => abs_of_nonneg ((hdist μ hμ).1 i)
  · simp only [S, Finset.mem_image]
    rintro _ ⟨μ, hμ, rfl⟩ _ ⟨η, hη, rfl⟩ hne
    have hne' : μ ≠ η := fun h => hne (h ▸ rfl)
    rw [PiLp.dist_eq_of_L1]
    simp only [Real.dist_eq]
    exact (hfar μ hμ η hη hne').le

end Podc.InteractiveDistributedProofs.LowerBound
