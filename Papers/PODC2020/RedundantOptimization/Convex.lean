/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2020.RedundantOptimization.Basic
import Cslib.Foundations.Analysis.Convex.FirstOrder

/-!
# Convex differentiable cost functions

* the first-order characterization of convexity `q x + q'(x)(y - x) ≤ q y` is the shared
  `ConvexOn.add_fderiv_le` (`Cslib/Foundations/Analysis/Convex/FirstOrder.lean`);
* `mem_argmin_iff_of_hasFDerivAt` — for convex differentiable functions, minimum points are exactly
  the critical points (used throughout the paper as "`w ∈ arg min Q` iff `∇Q(w) = 0`");
* `partI` — Part I of the proof of Theorem 1: a point that minimizes the aggregate of *every* set of
  `n - f` agents (with `1 ≤ f < n`) is a common minimum point of all `n` cost functions.
-/

open Finset

namespace RedundantOptimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A critical point of a convex function is a global minimum point. -/
lemma mem_argmin_of_hasFDerivAt_zero {q : E → ℝ} (hq : ConvexOn ℝ Set.univ q) {x : E}
    (hD : HasFDerivAt q (0 : E →L[ℝ] ℝ) x) : x ∈ argmin q := fun y => by
  simpa using ConvexOn.add_fderiv_le hq hD y

/-- At a global minimum point the derivative vanishes. -/
lemma hasFDerivAt_eq_zero_of_mem_argmin {q : E → ℝ} {D : E →L[ℝ] ℝ} {x : E}
    (hD : HasFDerivAt q D x) (hx : x ∈ argmin q) : D = 0 :=
  IsLocalMin.hasFDerivAt_eq_zero (Filter.Eventually.of_forall hx) hD

/-- For a convex function differentiable at `x`: `x` is a minimum point iff `q'(x) = 0`. -/
theorem mem_argmin_iff_of_hasFDerivAt {q : E → ℝ} (hq : ConvexOn ℝ Set.univ q)
    {D : E →L[ℝ] ℝ} {x : E} (hD : HasFDerivAt q D x) : x ∈ argmin q ↔ D = 0 :=
  ⟨hasFDerivAt_eq_zero_of_mem_argmin hD, fun h => mem_argmin_of_hasFDerivAt_zero hq (h ▸ hD)⟩

lemma hasFDerivAt_agg {ι : Type*} (S : Finset ι) {Q : ι → E → ℝ} {w : E}
    (h : ∀ i ∈ S, DifferentiableAt ℝ (Q i) w) :
    HasFDerivAt (agg S Q) (∑ i ∈ S, fderiv ℝ (Q i) w) w := by
  have := HasFDerivAt.fun_sum (u := S) (A := fun i => Q i) (A' := fun i => fderiv ℝ (Q i) w)
    (x := w) fun i hi => (h i hi).hasFDerivAt
  exact this

/-- **Part I of the proof of Theorem 1.** Let `1 ≤ f < n` and let all `n` (received) cost
functions be convex and differentiable. If `w` is a minimum point of the aggregate of every set of
exactly `n - f` agents, then `w` is a minimum point of every one of the `n` functions. -/
theorem partI {n f : ℕ} (hf : 1 ≤ f) (hfn : f < n) {C : Fin n → E → ℝ}
    (hconv : ∀ i, ConvexOn ℝ Set.univ (C i)) (hdiff : ∀ i, Differentiable ℝ (C i)) {w : E}
    (hw : ∀ T : Finset (Fin n), T.card = n - f → w ∈ argmin (agg T C)) :
    ∀ i, w ∈ argmin (C i) := by
  classical
  set D : Fin n → E →L[ℝ] ℝ := fun i => fderiv ℝ (C i) w with hDdef
  have hsum : ∀ T : Finset (Fin n), T.card = n - f → ∑ i ∈ T, D i = 0 := fun T hT =>
    hasFDerivAt_eq_zero_of_mem_argmin (hasFDerivAt_agg T fun i _ => (hdiff i) w) (hw T hT)
  -- a set of size `n - f` containing `i` and avoiding `j`
  have hset : ∀ i j : Fin n, i ≠ j → ∃ T : Finset (Fin n), i ∈ T ∧ j ∉ T ∧ T.card = n - f := by
    intro i j hij
    have hsub : ({i} : Finset (Fin n)) ⊆ univ.erase j := by
      simp [Finset.subset_iff, hij]
    have hc : (univ.erase j).card = n - 1 := by simp
    obtain ⟨T, hiT, hTj, hTc⟩ :=
      Finset.exists_subsuperset_card_eq (n := n - f) hsub (by simp; omega) (by rw [hc]; omega)
    exact ⟨T, hiT (Finset.mem_singleton_self i), fun h => by simpa using hTj h, hTc⟩
  -- all derivatives agree
  have hall : ∀ i j, D i = D j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    obtain ⟨T, hiT, hjT, hTc⟩ := hset i j hij
    set T' := insert j (T.erase i)
    have hT'c : T'.card = n - f := by
      rw [Finset.card_insert_of_notMem (by simp [hjT]), Finset.card_erase_of_mem hiT]
      omega
    have h1 := hsum T hTc
    have h2 := hsum T' hT'c
    rw [← Finset.add_sum_erase T D hiT] at h1
    rw [Finset.sum_insert (by simp [hjT])] at h2
    have : D i = -∑ x ∈ T.erase i, D x := eq_neg_of_add_eq_zero_left h1
    rw [this, eq_neg_of_add_eq_zero_left h2]
  -- hence all derivatives vanish
  have hzero : ∀ i, D i = 0 := by
    intro i
    obtain ⟨T, -, hTc⟩ :=
      Finset.exists_subset_card_eq (s := (univ : Finset (Fin n))) (n := n - f) (by simp)
    have h := hsum T hTc
    rw [Finset.sum_congr rfl (fun k _ => hall k i), Finset.sum_const, hTc] at h
    have hne : ((n - f : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (by omega : n - f ≠ 0)
    rw [← Nat.cast_smul_eq_nsmul ℝ] at h
    exact (smul_eq_zero.1 h).resolve_left hne
  intro i
  apply mem_argmin_of_hasFDerivAt_zero (hconv i)
  have := ((hdiff i) w).hasFDerivAt
  rwa [show fderiv ℝ (C i) w = 0 from hzero i] at this

end RedundantOptimization
