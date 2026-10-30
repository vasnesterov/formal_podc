/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2021.ApproxByzantineOptimization.Basic

/-!
# Theorem 1, literal (per-profile) reading: false

Theorem 1 of the paper: "There exists a deterministic `(f, ε)`-resilient distributed optimization
algorithm only if the agents' cost functions satisfy the `(2f, ε)`-redundancy property."
Read for the given cost functions (Definition 2 is a property of an algorithm in the executions
with these costs), the statement is false, in the paper's own scenario (`d = 1`, every aggregate has
a unique minimum point), even with convex costs and for every approximation level:

`n = 3`, `f = 1`, `Q₀ = (x - a)²`, `Q₁ = (x + a)²`, `Q₂ = 2a|x|` (`a > 0`). Every pair of agents
has `arg min = {0}`, so the constant algorithm `0` is `(1, 0)`-resilient (exactly fault-tolerant).
But `arg min Q₀ = {a}` is at distance `a` from `arg min (Q₀ + Q₁) = {0}`, so the costs are not
`(2, ε)`-redundant for `ε < a`. By `exists_isResilient_iff`, per profile only the existence of a
common `ε`-close point of the `(n - f)`-`arg min`s matters.
-/

open Finset Metric
open scoped ENNReal NNReal

namespace Podc.ApproxByzantineOptimization

/-- Every non-empty aggregate has a unique minimum point (the scenario of the paper's proofs). -/
def UniqueMinima {E : Type*} {n : ℕ} (Q : Profile n E) : Prop :=
  ∀ T : Finset (Fin n), T.Nonempty → ∃ x, argminSet Q T = {x}

lemma UniqueMinima.assumption1 {E : Type*} [PseudoEMetricSpace E] [T1Space E] {n : ℕ}
    {Q : Profile n E} (h : UniqueMinima Q) : Assumption1 Q := fun T hT => by
  obtain ⟨x, hx⟩ := h T hT
  rw [hx]
  exact ⟨Set.singleton_nonempty x, isClosed_singleton⟩

/-- The profile of the counterexample. -/
noncomputable def ppQ (a : ℝ) : Profile 3 ℝ :=
  ![fun x => (x - a) ^ 2, fun x => (x + a) ^ 2, fun x => 2 * a * |x|]

lemma fin3_card2 : ∀ T : Finset (Fin 3), T.card + 1 = 3 →
    T = {0, 1} ∨ T = {0, 2} ∨ T = {1, 2} := by decide

lemma fin3_nonempty : ∀ T : Finset (Fin 3), T.Nonempty → T = {0} ∨ T = {1} ∨ T = {2} ∨
    T = {0, 1} ∨ T = {0, 2} ∨ T = {1, 2} ∨ T = {0, 1, 2} := by decide

section
set_option linter.unusedSectionVars false
variable {a : ℝ} (ha : 0 < a)
include ha

lemma ppQ_0 : argminSet (ppQ a) {0} = {a} :=
  argminSet_eq_singleton fun y hy => by
    simp only [ppQ, Finset.sum_singleton, Matrix.cons_val_zero, sub_self]
    have : y - a ≠ 0 := sub_ne_zero.2 hy
    rw [zero_pow two_ne_zero]
    positivity

lemma ppQ_1 : argminSet (ppQ a) {1} = {-a} :=
  argminSet_eq_singleton fun y hy => by
    simp only [ppQ, Finset.sum_singleton, Matrix.cons_val_one, Matrix.cons_val_zero]
    have : y + a ≠ 0 := fun h => hy (by linarith)
    simp only [neg_add_cancel]
    rw [zero_pow two_ne_zero]
    positivity

lemma ppQ_2 : argminSet (ppQ a) {2} = {0} :=
  argminSet_eq_singleton fun y hy => by
    simp [ppQ]
    have : 0 < |y| := abs_pos.2 hy
    positivity

lemma ppQ_01 : argminSet (ppQ a) {0, 1} = {0} :=
  argminSet_eq_singleton fun y hy => by
    simp [ppQ]
    have : 0 < y ^ 2 := by positivity
    nlinarith

lemma ppQ_02 : argminSet (ppQ a) {0, 2} = {0} :=
  argminSet_eq_singleton fun y hy => by
    simp [ppQ]
    have : 0 < y ^ 2 := by positivity
    nlinarith [le_abs_self y]

lemma ppQ_12 : argminSet (ppQ a) {1, 2} = {0} :=
  argminSet_eq_singleton fun y hy => by
    simp [ppQ]
    have : 0 < y ^ 2 := by positivity
    nlinarith [neg_abs_le y]

lemma ppQ_012 : argminSet (ppQ a) {0, 1, 2} = {0} :=
  argminSet_eq_singleton fun y hy => by
    simp [ppQ, Finset.sum_insert]
    have : 0 < y ^ 2 := by positivity
    nlinarith [abs_nonneg y]

lemma ppQ_uniqueMinima : UniqueMinima (ppQ a) := fun T hT => by
  rcases fin3_nonempty T hT with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [⟨_, ppQ_0 ha⟩, ⟨_, ppQ_1 ha⟩, ⟨_, ppQ_2 ha⟩, ⟨_, ppQ_01 ha⟩, ⟨_, ppQ_02 ha⟩,
    ⟨_, ppQ_12 ha⟩, ⟨_, ppQ_012 ha⟩]

lemma ppQ_convex : ∀ i, ConvexOn ℝ Set.univ (ppQ a i) := by
  intro i
  fin_cases i
  · have := (Even.convexOn_pow (𝕜 := ℝ) even_two).comp_affineMap
      (AffineMap.id ℝ ℝ - AffineMap.const ℝ ℝ a)
    simpa [ppQ, Function.comp_def] using this
  · have := (Even.convexOn_pow (𝕜 := ℝ) even_two).comp_affineMap
      (AffineMap.id ℝ ℝ + AffineMap.const ℝ ℝ a)
    simpa [ppQ, Function.comp_def] using this
  · have := convexOn_univ_norm (E := ℝ) |>.smul (show (0 : ℝ) ≤ 2 * a by linarith)
    simpa [ppQ, Real.norm_eq_abs, smul_eq_mul] using this

end

/-- **Theorem 1 is false as literally stated.** For every `ε ≥ 0` there are convex cost functions
on `ℝ` (`n = 3`, `f = 1`) such that every non-empty aggregate has a unique minimum point
(Assumption 1 holds), the constant algorithm `0` is `(1, 0)`-resilient (a fortiori
`(1, ε)`-resilient), but the costs are not `(2, ε)`-redundant. -/
theorem theorem_1_false_per_profile (ε : ℝ≥0) :
    ∃ Q : Profile 3 ℝ, (∀ i, ConvexOn ℝ Set.univ (Q i)) ∧ UniqueMinima Q ∧ Assumption1 Q ∧
      IsResilient 1 0 (fun _ => 0) Q ∧ IsResilient 1 ε (fun _ => 0) Q ∧
      ¬ IsRedundant 1 ε Q := by
  have ha : (0 : ℝ) < ε + 1 := by positivity
  have hres : IsResilient 1 0 (fun _ => 0) (ppQ (ε + 1)) := by
    intro B _ R _ S _ hS
    rcases fin3_card2 S hS with rfl | rfl | rfl
    · rw [ppQ_01 ha, infEDist_singleton, edist_self]; exact le_rfl
    · rw [ppQ_02 ha, infEDist_singleton, edist_self]; exact le_rfl
    · rw [ppQ_12 ha, infEDist_singleton, edist_self]; exact le_rfl
  refine ⟨ppQ (ε + 1), ppQ_convex ha, ppQ_uniqueMinima ha, (ppQ_uniqueMinima ha).assumption1,
    hres, fun B hB R hR S hSB hS => (hres B hB R hR S hSB hS).trans (by simp), ?_⟩
  intro h
  have := h {0, 1} {0} (by decide) (by decide) (by decide)
  rw [ppQ_01 ha, ppQ_0 ha, hausdorffEDist_singleton, edist_dist, dist_zero_left,
    Real.norm_eq_abs, abs_of_pos ha] at this
  have h2 : ENNReal.ofReal ((ε : ℝ) + 1) ≤ ENNReal.ofReal ε := by simpa using this
  rw [ENNReal.ofReal_le_ofReal_iff ε.coe_nonneg] at h2
  linarith

end Podc.ApproxByzantineOptimization
