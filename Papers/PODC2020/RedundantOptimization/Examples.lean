/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2020.RedundantOptimization.CGC

/-!
# Instances for Theorem 2

* `example_assumptions` — non-vacuity: `n = 4`, `f = 1`, three honest agents with cost
  `Q_i(x) = x²/2` on `ℝ`; all hypotheses of Theorem 2 hold with `α = 1/12 > 0`.
* `theorem2_rho_nonneg_false` — Theorem 2 (i) fails in the degenerate case `W* = ℝ`.
-/

open Finset
open scoped RealInnerProductSpace

namespace RedundantOptimization

lemma hasGradientAt_half_sq (x : ℝ) : HasGradientAt (fun x : ℝ => x ^ 2 / 2) x x := by
  apply HasDerivAt.hasGradientAt'
  have := (hasDerivAt_pow 2 x).div_const 2
  convert this using 1
  ring

lemma convexOn_half_sq : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2 / 2) := by
  have := (even_two.convexOn_pow (𝕜 := ℝ)).smul (by norm_num : (0 : ℝ) ≤ 1 / 2)
  convert this using 1
  funext x; simp; ring

lemma argmin_half_sq : argmin (fun x : ℝ => x ^ 2 / 2) = {0} := by
  ext x
  simp only [argmin, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h; have := h 0; nlinarith [sq_nonneg x]
  · rintro rfl v; nlinarith [sq_nonneg v]

/-- Every nonempty set of agents with costs `x²/2` has aggregate minimum `{0}`. -/
lemma argmin_agg_half_sq {S : Finset (Fin 4)} (hS : S.Nonempty) :
    argmin (agg S fun (_ : Fin 4) (x : ℝ) => x ^ 2 / 2) = {0} := by
  rw [lemma1 S _ ⟨0, Set.mem_iInter₂.2 fun i _ => by rw [argmin_half_sq]; rfl⟩]
  obtain ⟨i, hi⟩ := hS
  ext x
  simp only [Set.mem_iInter, argmin_half_sq, Set.mem_singleton_iff]
  exact ⟨fun h => h i hi, fun h _ _ => h⟩

/-- The example: `n = 4`, `f = 1`, honest agents `{0, 1, 2}`, `Q_i(x) = x²/2`, `∇Q_i(x) = x`,
`μ = λ = 1`, `W* = {0}`. -/
noncomputable def exampleA : Assumptions 4 1 ℝ where
  H := {0, 1, 2}
  card_H := by decide
  Q := fun _ x => x ^ 2 / 2
  G := fun _ x => x
  convex := fun _ _ => convexOn_half_sq
  hasGradient := fun _ _ w => hasGradientAt_half_sq w
  μ := 1
  μ_pos := one_pos
  lipschitz := fun _ _ w w' => by simp
  redundant := by
    intro S hS hcard
    rw [argmin_agg_half_sq (Finset.card_pos.1 (by omega)),
      argmin_agg_half_sq ⟨0, by simp⟩]
  proj := fun _ => 0
  proj_mem := fun _ => by rw [argmin_agg_half_sq ⟨0, by simp⟩]; rfl
  proj_min := fun w v hv => by
    rw [argmin_agg_half_sq ⟨0, by simp⟩] at hv
    rw [Set.mem_singleton_iff.1 hv]
  lam := 1
  lam_pos := one_pos
  strong := fun w => by
    simp only [sub_zero, one_mul]
    rw [real_inner_smul_left, Finset.sum_const]
    simp
    apply le_of_eq; ring

/-- **Non-vacuity of Theorem 2** with one Byzantine agent: the hypotheses hold, `α = 1/12 > 0`,
`η̄ = 1/8`, and with `η = 1/16` every run converges at rate `ρ = 1 - 1/16 = 15/16`. -/
theorem example_assumptions :
    exampleA.α = 1 / 12 ∧ exampleA.ηbar = 1 / 8 ∧ exampleA.ρ (1 / 16) = 15 / 16 ∧
      ∀ w : ℕ → ℝ, exampleA.IsRun (1 / 16) w →
        ∀ t, ‖w t‖ ^ 2 ≤ (15 / 16) ^ t * ‖w 0‖ ^ 2 := by
  have hα : exampleA.α = 1 / 12 := by
    simp only [Assumptions.α, exampleA]; norm_num
  have hη : exampleA.ηbar = 1 / 8 := by
    simp only [Assumptions.ηbar, hα]; simp only [exampleA]; norm_num
  have hρ : exampleA.ρ (1 / 16) = 15 / 16 := by
    simp only [Assumptions.ρ, hη]; simp only [exampleA]; norm_num
  refine ⟨hα, hη, hρ, fun w hw t => ?_⟩
  have := (exampleA.theorem2 (by norm_num) (by norm_num) (by rw [hη]; norm_num) hw).2 t
  rw [hρ] at this
  have hp : ∀ x, exampleA.proj x = 0 := fun _ => rfl
  simpa [hp] using this

/-- The degenerate instance: `n = 3`, `f = 1`, honest agents `{0, 1}` with zero cost, `W* = ℝ`,
`μ = 1`, `λ = 30`. -/
noncomputable def degenerateA : Assumptions 3 1 ℝ where
  H := {0, 1}
  card_H := by decide
  Q := fun _ _ => 0
  G := fun _ _ => 0
  convex := fun _ _ => convexOn_const 0 convex_univ
  hasGradient := fun _ _ w => by
    simpa using (hasDerivAt_const w (0 : ℝ)).hasGradientAt'
  μ := 1
  μ_pos := one_pos
  lipschitz := fun _ _ w w' => by simp
  redundant := by
    intro S _ _
    ext x; simp [argmin]
  proj := id
  proj_mem := fun _ v => by simp
  proj_min := fun w v _ => by simp
  lam := 30
  lam_pos := by norm_num
  strong := fun w => by simp

/-- **Theorem 2 (i) is false in the degenerate case `W* = ℝ`**: all hypotheses of Theorem 2 hold
(`α = 29/3 > 0`, `η = 29/3 ∈ (0, η̄)`, `η̄ = 58/3`) but `ρ = 1 - 9α² = -840 < 0`. (Part (ii) holds
trivially here, since every point is a minimum point.) -/
theorem theorem2_rho_nonneg_false :
    0 < degenerateA.α ∧ 0 < (29 / 3 : ℝ) ∧ (29 / 3 : ℝ) < degenerateA.ηbar ∧
      degenerateA.ρ (29 / 3) = -840 := by
  have hα : degenerateA.α = 29 / 3 := by
    simp only [Assumptions.α, degenerateA]; norm_num
  have hη : degenerateA.ηbar = 58 / 3 := by
    simp only [Assumptions.ηbar, hα]; simp only [degenerateA]; norm_num
  refine ⟨by rw [hα]; norm_num, by norm_num, by rw [hη]; norm_num, ?_⟩
  simp only [Assumptions.ρ, hη]; simp only [degenerateA]; norm_num

end RedundantOptimization
