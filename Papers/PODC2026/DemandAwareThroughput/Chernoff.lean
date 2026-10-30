import Papers.PODC2026.DemandAwareThroughput.Rounding
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# The Chernoff lower tail under negative correlation of zeros (Theorem 4)

Bentert, Avin, Schmid, PODC 2026, §3.1, Theorem 4 (Panconesi–Srinivasan; Gandhi et al., JACM
2006, Theorem 3.1). We prove `NegCorrChernoff`: if `X₁, …, X_t` are `0/1` random variables on a
finite probability space with `P(Xₖ = 1) = xₖ` and negatively correlated zeros,
`P(∀ k ∈ S, Xₖ = 0) ≤ ∏_{k ∈ S} (1 - xₖ)`, and `aₖ ∈ [0, 1]`, then for `μ = ∑ₖ aₖ xₖ` and
`δ ∈ [0, 1]`,
`P(∑ₖ aₖ Xₖ ≤ μ(1 - δ)) ≤ exp(-μδ²/2)`.

Proof (exponential moment method):
1. Markov: `P(S ≤ c) ≤ e^{δc} · E[e^{-δS}]`.
2. `e^{-δ aₖ Xₖ} = uₖ + vₖ (1 - Xₖ)` with `uₖ = e^{-δaₖ}`, `vₖ = 1 - e^{-δaₖ} ≥ 0`; expanding the
   product over subsets and using negative correlation of zeros,
   `E[e^{-δS}] ≤ ∏ₖ (uₖ + vₖ(1 - xₖ)) = ∏ₖ (1 - xₖvₖ) ≤ exp(-∑ₖ xₖvₖ)`.
3. Convexity of `exp`: `vₖ ≥ aₖ (1 - e^{-δ})`, so `∑ₖ xₖvₖ ≥ μ(1 - e^{-δ})`.
4. `e^{-δ} ≤ 1 - δ + δ²/2` gives `δμ(1 - δ) - μ(1 - e^{-δ}) ≤ -μδ²/2`.
-/

namespace Podc.DemandAwareThroughput

open Finset

/-- `e^{-δ} ≤ 1 - δ + δ²/2` for `δ ≥ 0`. -/
private lemma exp_neg_le_one_sub_add_sq_div_two {δ : ℝ} (hδ : 0 ≤ δ) :
    Real.exp (-δ) ≤ 1 - δ + δ ^ 2 / 2 := by
  have h1 := Real.quadratic_le_exp_of_nonneg hδ
  have hpos : 0 < 1 - δ + δ ^ 2 / 2 := by nlinarith [sq_nonneg (δ - 1)]
  have h2 := mul_le_mul_of_nonneg_right h1 hpos.le
  rw [Real.exp_neg]
  rw [inv_le_iff_one_le_mul₀ (Real.exp_pos δ)]
  nlinarith [sq_nonneg (δ ^ 2)]

/-- Convexity of `exp`: `e^{-La} ≤ (1 - a) + a e^{-L}` for `a ∈ [0, 1]`. -/
private lemma exp_neg_mul_le_convex (L : ℝ) {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    Real.exp (-(L * a)) ≤ (1 - a) + a * Real.exp (-L) := by
  have := convexOn_exp.2 (Set.mem_univ 0) (Set.mem_univ (-L)) (sub_nonneg.2 ha1) ha0
    (by ring)
  simp only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one] at this
  convert this using 2
  ring

/-- The exponential-moment bound under negative correlation of zeros:
`E[∏ₖ (uₖ + vₖ (1 - Xₖ))] ≤ ∏ₖ (uₖ + vₖ (1 - xₖ))` for non-negative `u, v`. -/
private lemma moment_bound_of_negCorr {Ω ι : Type} [Fintype Ω] [Fintype ι] (μ : FinDist Ω)
    (X : ι → Ω → Bool) (x u v : ι → ℝ) (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k)
    (hneg : ∀ S : Finset ι, μ.prob (fun ω => ∀ k ∈ S, X k ω = false) ≤ ∏ k ∈ S, (1 - x k)) :
    ∑ ω, μ.w ω * ∏ k, (u k + v k * (1 - bval (X k ω))) ≤ ∏ k, (u k + v k * (1 - x k)) := by
  classical
  have key : ∀ t : Finset ι,
      ∑ ω, μ.w ω * ∏ k ∈ t, (1 - bval (X k ω)) ≤ ∏ k ∈ t, (1 - x k) := by
    intro t
    refine le_trans (le_of_eq ?_) (hneg t)
    unfold FinDist.prob
    refine Finset.sum_congr rfl fun ω _ => ?_
    split_ifs with h
    · rw [Finset.prod_eq_one, mul_one]
      intro k hk
      simp [h k hk, bval]
    · push Not at h
      obtain ⟨k, hk, hX⟩ := h
      rw [Finset.prod_eq_zero hk, mul_zero]
      simp [bval, hX]
  have expand : ∀ c : ι → ℝ, ∏ k, (u k + v k * c k) =
      ∑ t ∈ (univ : Finset ι).powerset,
        (∏ k ∈ t, u k) * (∏ k ∈ univ \ t, v k) * ∏ k ∈ univ \ t, c k := by
    intro c
    rw [Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_mul_distrib, mul_assoc]
  simp_rw [expand, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  have hc : 0 ≤ (∏ k ∈ t, u k) * ∏ k ∈ univ \ t, v k :=
    mul_nonneg (prod_nonneg fun k _ => hu k) (prod_nonneg fun k _ => hv k)
  calc ∑ ω, μ.w ω * ((∏ k ∈ t, u k) * (∏ k ∈ univ \ t, v k) *
          ∏ k ∈ univ \ t, (1 - bval (X k ω)))
      = ((∏ k ∈ t, u k) * ∏ k ∈ univ \ t, v k) *
          ∑ ω, μ.w ω * ∏ k ∈ univ \ t, (1 - bval (X k ω)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ω _ => by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (key _) hc

-- CSLib candidate
/-- **Theorem 4** of the paper (Panconesi–Srinivasan; Gandhi et al., Thm 3.1), proved. -/
theorem negCorrChernoff : NegCorrChernoff := by
  intro Ω ι _ _ μ X a x ha hx hmarg hneg δ hδ0 hδ1
  classical
  set m := ∑ k, a k * x k with hm
  have hm0 : 0 ≤ m := sum_nonneg fun k _ => mul_nonneg (ha k).1 (hx k).1
  set u : ι → ℝ := fun k => Real.exp (-(δ * a k)) with hu_def
  set v : ι → ℝ := fun k => 1 - Real.exp (-(δ * a k)) with hv_def
  have hu : ∀ k, 0 ≤ u k := fun k => (Real.exp_pos _).le
  have hv : ∀ k, 0 ≤ v k := fun k => by
    simp only [v, sub_nonneg, Real.exp_le_one_iff, neg_nonpos]
    exact mul_nonneg hδ0 (ha k).1
  -- Step 1: Markov's inequality for `e^{-δS}`.
  have step1 : μ.prob (fun ω => ∑ k, a k * bval (X k ω) ≤ m * (1 - δ)) ≤
      Real.exp (δ * (m * (1 - δ))) * ∑ ω, μ.w ω * ∏ k, (u k + v k * (1 - bval (X k ω))) := by
    unfold FinDist.prob
    rw [Finset.mul_sum]
    refine sum_le_sum fun ω _ => ?_
    have hprod : ∏ k, (u k + v k * (1 - bval (X k ω))) =
        Real.exp (-(δ * ∑ k, a k * bval (X k ω))) := by
      rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum]
      refine prod_congr rfl fun k _ => ?_
      cases X k ω <;> simp [u, v, bval]
    rw [hprod, mul_left_comm, ← Real.exp_add]
    split_ifs with h
    · calc μ.w ω = μ.w ω * 1 := (mul_one _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_left (Real.one_le_exp (by nlinarith)) (μ.nonneg ω)
    · exact mul_nonneg (μ.nonneg ω) (Real.exp_pos _).le
  -- Step 2: negative correlation of zeros.
  have step2 := moment_bound_of_negCorr μ X x u v hu hv hneg
  -- Step 3: `∏ₖ (1 - xₖvₖ) ≤ exp(-μ(1 - e^{-δ}))`.
  have step3 : ∏ k, (u k + v k * (1 - x k)) ≤ Real.exp (-(m * (1 - Real.exp (-δ)))) := by
    calc ∏ k, (u k + v k * (1 - x k)) ≤ ∏ k, Real.exp (-(x k * v k)) := by
          refine Finset.prod_le_prod₀ (fun k _ => ?_) (fun k _ => ?_)
          · exact add_nonneg (hu k) (mul_nonneg (hv k) (by linarith [(hx k).2]))
          · have : u k + v k * (1 - x k) = -(x k * v k) + 1 := by simp only [u, v]; ring
            rw [this]
            exact Real.add_one_le_exp _
      _ = Real.exp (-∑ k, x k * v k) := by rw [← Real.exp_sum, sum_neg_distrib]
      _ ≤ _ := by
          apply Real.exp_le_exp.2
          rw [neg_le_neg_iff, hm, Finset.sum_mul]
          refine sum_le_sum fun k _ => ?_
          have hc := exp_neg_mul_le_convex δ (ha k).1 (ha k).2
          have hx0 := (hx k).1
          simp only [v]
          nlinarith [mul_le_mul_of_nonneg_left hc hx0]
  -- Step 4: `e^{-δ} ≤ 1 - δ + δ²/2`.
  have hexp := exp_neg_le_one_sub_add_sq_div_two hδ0
  calc _ ≤ _ := step1
    _ ≤ Real.exp (δ * (m * (1 - δ))) * Real.exp (-(m * (1 - Real.exp (-δ)))) :=
        mul_le_mul_of_nonneg_left (step2.trans step3) (Real.exp_pos _).le
    _ = Real.exp (δ * (m * (1 - δ)) + -(m * (1 - Real.exp (-δ)))) := (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.2 (by nlinarith [mul_le_mul_of_nonneg_left hexp hm0])

end Podc.DemandAwareThroughput
