import Cslib.Foundations.Combinatorics.Apportionment.Divisor
import Mathlib

/-!
# Swiper: weight reduction problems (definitions)

Tonkikh, Freitas, *Swiper: a new paradigm for efficient weighted distributed protocols*,
PODC 2024 (arXiv 2307.15561), Section 2.

Parties are the elements of a finite type `ι` (`n = Fintype.card ι`), weights are `w : ι → ℝ`
(non-negative, total `W = ∑ i, w i`), ticket assignments are `t : ι → ℕ` (total `T = ∑ i, t i`).
Sums over a set `S : Finset ι` play the role of the paper's `w(S)` and `t(S)`.
-/

namespace Papers.PODC2024.Swiper

open Finset

variable {ι : Type*} [Fintype ι]

/-- **Problem 1 (Weight Restriction)**, the constraint: every set of weight less than `αw · W`
gets less than `αn · T` tickets. -/
def IsWR (αw αn : ℝ) (w : ι → ℝ) (t : ι → ℕ) : Prop :=
  ∀ S : Finset ι, ∑ i ∈ S, w i < αw * ∑ i, w i →
    ∑ i ∈ S, (t i : ℝ) < αn * ∑ i, (t i : ℝ)

/-- **Problem 2 (Weight Qualification)**, the constraint: every set of weight more than `βw · W`
gets more than `βn · T` tickets. -/
def IsWQ (βw βn : ℝ) (w : ι → ℝ) (t : ι → ℕ) : Prop :=
  ∀ S : Finset ι, βw * ∑ i, w i < ∑ i ∈ S, w i →
    βn * ∑ i, (t i : ℝ) < ∑ i ∈ S, (t i : ℝ)

/-- **Problem 3 (Weight Separation)**, the constraint: every set of weight less than `α · W` gets
fewer tickets than every set of weight more than `β · W`. -/
def IsWS (α β : ℝ) (w : ι → ℝ) (t : ι → ℕ) : Prop :=
  ∀ S₁ S₂ : Finset ι, ∑ i ∈ S₁, w i < α * ∑ i, w i → β * ∑ i, w i < ∑ i ∈ S₂, w i →
    ∑ i ∈ S₁, (t i : ℝ) < ∑ i ∈ S₂, (t i : ℝ)

/-- A *viable* ticket assignment (Appendix A.1): it assigns at least one ticket and satisfies the
Weight Restriction constraint. -/
def Viable (αw αn : ℝ) (w : ι → ℝ) (t : ι → ℕ) : Prop :=
  ∑ i, t i ≠ 0 ∧ IsWR αw αn w t

/-- The Weight Restriction bound `αw (1 - αw) / (αn - αw) · n` (before taking the ceiling). -/
noncomputable def wrBound (αw αn : ℝ) (n : ℕ) : ℝ := αw * (1 - αw) / (αn - αw) * n

/-- If `W > 0` and `αw > 0`, the WR constraint forces `T ≠ 0` (take `S = ∅`), so viability is
the WR constraint itself. -/
theorem IsWR.sum_ne_zero {αw αn : ℝ} {w : ι → ℝ} {t : ι → ℕ} (h : IsWR αw αn w t)
    (hW : 0 < ∑ i, w i) (hαw : 0 < αw) : ∑ i, t i ≠ 0 := by
  intro h0
  have := h ∅ (by simpa using mul_pos hαw hW)
  have h0' : ∑ i, (t i : ℝ) = 0 := by exact_mod_cast h0
  simp [h0'] at this

theorem viable_iff {αw αn : ℝ} {w : ι → ℝ} {t : ι → ℕ} (hW : 0 < ∑ i, w i) (hαw : 0 < αw) :
    Viable αw αn w t ↔ IsWR αw αn w t :=
  ⟨fun h => h.2, fun h => ⟨h.sum_ne_zero hW hαw, h⟩⟩

/-- Non-negative weights with `W ≠ 0` have a positive member and a positive total. -/
theorem exists_pos_of_sum_ne_zero {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i ≠ 0) :
    ∃ i, 0 < w i := by
  by_contra h
  push Not at h
  exact hW (Finset.sum_eq_zero fun i _ => le_antisymm (h i) (hw i))

theorem sum_pos_of_sum_ne_zero {w : ι → ℝ} (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i ≠ 0) :
    0 < ∑ i, w i :=
  lt_of_le_of_ne (Finset.sum_nonneg fun i _ => hw i) (Ne.symm hW)

/-- Splitting a sum over `univ` with a membership test. -/
theorem sum_ite_mem_compl [DecidableEq ι] {β : Type*} [AddCommGroup β] (S : Finset ι)
    (f g : ι → β) :
    ∑ i, (if i ∈ S then f i else g i) = ∑ i ∈ S, f i + (∑ i, g i - ∑ i ∈ S, g i) := by
  rw [Finset.sum_ite, Finset.filter_mem_eq_inter, Finset.univ_inter,
    ← Finset.sum_compl_add_sum S g]
  simp [Finset.compl_eq_univ_sdiff, Finset.filter_not]

end Papers.PODC2024.Swiper
