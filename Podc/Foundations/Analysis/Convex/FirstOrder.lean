import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Convex.Deriv

-- CSLib candidate: Cslib/Foundations/Analysis/Convex/FirstOrder.lean (Mathlib candidate)

/-!
# First-order condition for convex functions

* `ConvexOn.add_fderiv_le`: a convex function `q : E → ℝ` differentiable at `x` lies above its
  tangent hyperplane, `q x + q'(x) (y - x) ≤ q y`;
* `ConvexOn.add_inner_le`: the same with a gradient in a Hilbert space,
  `q x + ⟪∇q(x), y - x⟫ ≤ q y`;
* `ConvexOn.fun_sum`: a finite sum of convex functions is convex.

Mathlib has the one-dimensional version (`ConvexOn.le_slope_of_hasDerivAt`), from which the
general statement is derived by restricting to the line through `x` and `y`.
-/

open Finset InnerProductSpace
open scoped RealInnerProductSpace

/-- First-order condition for convex functions: the tangent hyperplane lies below the graph. -/
theorem ConvexOn.add_fderiv_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {q : E → ℝ}
    (hq : ConvexOn ℝ Set.univ q) {D : E →L[ℝ] ℝ} {x : E}
    (hD : HasFDerivAt q D x) (y : E) : q x + D (y - x) ≤ q y := by
  set φ : ℝ → ℝ := fun t => q (x + t • (y - x)) with hφdef
  have hφ : ConvexOn ℝ Set.univ φ := by
    let g : ℝ →ᵃ[ℝ] E := AffineMap.lineMap x y
    have h := hq.comp_affineMap g
    simp only [Set.preimage_univ] at h
    convert h using 1
    funext t
    simp [φ, g, AffineMap.lineMap_apply, add_comm]
  have hline : HasDerivAt (fun t : ℝ => x + t • (y - x)) (y - x) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (y - x)).const_add x
  have hD' : HasFDerivAt q D (x + (0 : ℝ) • (y - x)) := by simpa using hD
  have hd : HasDerivAt φ (D (y - x)) 0 := hD'.comp_hasDerivAt (0 : ℝ) hline
  have := hφ.le_slope_of_hasDerivAt (Set.mem_univ 0) (Set.mem_univ 1) zero_lt_one hd
  simp only [slope, φ, sub_zero, inv_one, one_smul, zero_smul, add_zero, vsub_eq_sub] at this
  have h1 : x + (y - x) = y := by abel
  rw [h1] at this
  linarith

/-- First-order condition for convex functions, with gradients. -/
theorem ConvexOn.add_inner_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {q : E → ℝ} (hq : ConvexOn ℝ Set.univ q) {g x : E}
    (hg : HasGradientAt q g x) (y : E) : q x + ⟪g, y - x⟫ ≤ q y := by
  have := ConvexOn.add_fderiv_le hq (hasGradientAt_iff_hasFDerivAt.1 hg) y
  simpa [InnerProductSpace.toDual_apply_apply] using this

/-- A finite sum of convex functions is convex. -/
theorem ConvexOn.fun_sum {E ι : Type*} [AddCommGroup E] [Module ℝ E] {S : Finset ι}
    {Q : ι → E → ℝ} (h : ∀ i ∈ S, ConvexOn ℝ Set.univ (Q i)) :
    ConvexOn ℝ Set.univ (fun w => ∑ i ∈ S, Q i w) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have : (fun w => ∑ i ∈ (∅ : Finset ι), Q i w) = fun _ => 0 := by funext w; simp
    rw [this]; exact convexOn_const (0 : ℝ) convex_univ
  | insert a S ha ih =>
    have : (fun w => ∑ i ∈ insert a S, Q i w) = Q a + fun w => ∑ i ∈ S, Q i w := by
      funext w; simp [Finset.sum_insert ha]
    rw [this]
    exact (h a (mem_insert_self a S)).add (ih fun i hi => h i (mem_insert_of_mem hi))
