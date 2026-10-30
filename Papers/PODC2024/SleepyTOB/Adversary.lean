import Papers.PODC2024.SleepyTOB.Model

/-!
# Section 2.3: churn rate, failure ratio and η-sleepiness

D'Amato, Losa, Zanolini, PODC 2024, Section 2.3 and footnote 7.

With `H_{r-η,r-1} = ⋃_{r-η ≤ r' ≤ r-1} H_{r'}` (`Hw`), the paper bounds the churn rate,
`|H_{r-η,r-1} \ H_r| ≤ γ |H_{r-η,r-1}|` (Equation 1), and the failure ratio,
`|B_r| < β̃ |O_r|` with `β̃ = (β - γ)/(γ(β - 2) + 1)` (Equation 2), while the proofs of Section 3
use the η-sleepiness condition `|H_r| > (1 - β) |O_{r-η,r}|` (Equation 3).

* `sleepy_of_churn_of_failure`: Equations 1 and 2 imply Equation 3 (for `0 ≤ γ < β < 1`, growing
  adversary). The bound is tight for the worst-case count `|O_{r-η,r}| ≤ |H_r| + |Hw \ H_r| + |B_r|`:
  `γ/(1-γ) + β̃/(1-β̃) = β/(1-β)` exactly. The paper does not state this implication explicitly; it is
  what makes its synchronous-round assumptions (1)–(2) sufficient for the proofs, which use (3).
* `footnote_7`: the three formulations of η-sleepiness in footnote 7 are equivalent.
-/

namespace Podc.SleepyTOB

open Finset

noncomputable section
open Classical

variable {P α : Type*}

namespace Exec

variable (E : Exec P α)

/-- `H_{r-η,r-1}`: processes honest and awake at some round of `[r - η, r - 1]` (empty for
`r = 0`, matching the paper's convention `H_s = ∅` for `s < 0`). -/
def Hw (r : ℕ) : Finset P := (Ico (r - E.η) r).biUnion E.H

variable {E}

theorem Ow_subset (r : ℕ) : E.Ow (r - E.η) r ⊆ E.H r ∪ (E.Hw r \ E.H r) ∪ E.B r := by
  intro q hq
  obtain ⟨s, hs, hqs⟩ := mem_biUnion.1 hq
  rw [mem_Icc] at hs
  simp only [mem_union, mem_sdiff]
  by_cases hB : q ∈ E.B r
  · exact Or.inr hB
  by_cases hH : q ∈ E.H r
  · exact Or.inl (Or.inl hH)
  left; right
  refine ⟨?_, hH⟩
  rcases eq_or_lt_of_le hs.2 with rfl | hlt
  · exact absurd (mem_sdiff.2 ⟨hqs, hB⟩) hH
  · have hqB : q ∉ E.B s := fun h => hB (B_mono' hlt.le h)
    exact mem_biUnion.2 ⟨s, mem_Ico.2 ⟨hs.1, hlt⟩, mem_sdiff.2 ⟨hqs, hqB⟩⟩

theorem Ow_eq (r : ℕ) : E.Ow (r - E.η) r = E.H r ∪ (E.B r ∪ (E.Hw r \ E.H r)) := by
  apply Subset.antisymm
  · intro q hq
    have := Ow_subset r hq
    simp only [mem_union] at this ⊢
    tauto
  · have hO : E.O r ⊆ E.Ow (r - E.η) r := O_subset_Ow (Nat.sub_le r E.η) le_rfl
    refine union_subset (subset_trans (H_subset_O r) hO)
      (union_subset (subset_trans (E.B_subset r) hO) ?_)
    intro q hq
    obtain ⟨s, hs, hqs⟩ := mem_biUnion.1 (mem_sdiff.1 hq).1
    rw [mem_Ico] at hs
    exact O_subset_Ow hs.1 hs.2.le (H_subset_O s hqs)

theorem card_Ow_eq (r : ℕ) :
    #(E.Ow (r - E.η) r) = #(E.H r) + #(E.B r ∪ (E.Hw r \ E.H r)) := by
  rw [Ow_eq, card_union_of_disjoint]
  rw [disjoint_union_right]
  exact ⟨sdiff_disjoint, disjoint_sdiff⟩

/-- **Footnote 7.** The formulations of η-sleepiness are equivalent:
`|B_r ∪ H_{r-η,r-1} \ H_r| < ρ |H_r|` with `ρ = β/(1-β)`, `|B_r ∪ H_{r-η,r-1} \ H_r| < β |O_{r-η,r}|`,
and `|H_r| > (1 - β) |O_{r-η,r}|` (for `β < 1`). -/
theorem footnote_7 (β : ℝ) (hβ : β < 1) (r : ℕ) :
    ((#(E.B r ∪ (E.Hw r \ E.H r)) : ℝ) < β / (1 - β) * #(E.H r) ↔
      (#(E.B r ∪ (E.Hw r \ E.H r)) : ℝ) < β * #(E.Ow (r - E.η) r)) ∧
    ((#(E.B r ∪ (E.Hw r \ E.H r)) : ℝ) < β * #(E.Ow (r - E.η) r) ↔
      (1 - β) * #(E.Ow (r - E.η) r) < #(E.H r)) := by
  rw [card_Ow_eq]
  push_cast
  have h1 : 0 < 1 - β := by linarith
  set c : ℝ := ((#(E.B r ∪ (E.Hw r \ E.H r)) : ℕ) : ℝ)
  set h : ℝ := ((#(E.H r) : ℕ) : ℝ)
  constructor
  · rw [div_mul_eq_mul_div, lt_div_iff₀ h1]
    constructor <;> intro H <;> nlinarith
  · constructor <;> intro H <;> nlinarith

/-- **Section 2.3.** The churn bound (Equation 1) and the failure-ratio bound (Equation 2) with
`β̃ = (β - γ)/(γ(β - 2) + 1)` imply η-sleepiness (Equation 3), for `0 ≤ γ < β < 1` and a growing
adversary. -/
theorem sleepy_of_churn_of_failure (β γ : ℝ) (hγ : 0 ≤ γ) (hγβ : γ < β) (hβ : β < 1) (r : ℕ)
    (h1 : (#(E.Hw r \ E.H r) : ℝ) ≤ γ * #(E.Hw r))
    (h2 : (#(E.B r) : ℝ) < (β - γ) / (γ * (β - 2) + 1) * #(E.O r)) :
    (1 - β) * #(E.Ow (r - E.η) r) < #(E.H r) := by
  -- counting
  have cO : #(E.O r) = #(E.H r) + #(E.B r) := by
    exact (card_sdiff_add_card_eq_card (E.B_subset r)).symm
  have cx : #(E.Hw r) ≤ #(E.Hw r \ E.H r) + #(E.H r) := card_le_card_sdiff_add_card
  have cOw : #(E.Ow (r - E.η) r) ≤ #(E.H r) + #(E.Hw r \ E.H r) + #(E.B r) :=
    (card_le_card (Ow_subset r)).trans ((card_union_le _ _).trans
      (Nat.add_le_add_right (card_union_le _ _) _))
  set h : ℝ := ((#(E.H r) : ℕ) : ℝ)
  set d : ℝ := ((#(E.Hw r \ E.H r) : ℕ) : ℝ)
  set x : ℝ := ((#(E.Hw r) : ℕ) : ℝ)
  set b : ℝ := ((#(E.B r) : ℕ) : ℝ)
  set o : ℝ := ((#(E.Ow (r - E.η) r) : ℕ) : ℝ)
  have cO' : (#(E.O r) : ℝ) = h + b := by rw [cO]; push_cast; rfl
  have cx' : x ≤ d + h := by simp only [x, d, h]; exact_mod_cast cx
  have cOw' : o ≤ h + d + b := by simp only [o, h, d, b]; exact_mod_cast cOw
  rw [cO'] at h2
  have hD : 0 < γ * (β - 2) + 1 := by nlinarith
  rw [div_mul_eq_mul_div, lt_div_iff₀ hD] at h2
  -- `(1-β)(1-γ) b < (β-γ) h` and `(1-β)(1-γ) d ≤ (1-β) γ h`
  have hb : (1 - β) * (1 - γ) * b < (β - γ) * h := by nlinarith
  have hd : (1 - γ) * d ≤ γ * h := by nlinarith
  have hd' : (1 - β) * (1 - γ) * d ≤ (1 - β) * γ * h := by
    have : 0 ≤ 1 - β := by linarith
    nlinarith
  have hsum : (1 - β) * (d + b) < β * h := by
    have h1γ : 0 < 1 - γ := by linarith
    have : (1 - γ) * ((1 - β) * (d + b)) < (1 - γ) * (β * h) := by nlinarith
    exact lt_of_mul_lt_mul_left this h1γ.le
  have : 0 ≤ 1 - β := by linarith
  nlinarith

end Exec

/-- The failure ratio `β̃ = (β - γ)/(γ(β - 2) + 1)` of Section 2.3 is exactly the one for which the
worst-case count of the proof of `Exec.sleepy_of_churn_of_failure` is tight:
`γ/(1 - γ) + β̃/(1 - β̃) = β/(1 - β)`. -/
theorem betaTilde_identity (β γ : ℝ) (hγ : 0 ≤ γ) (hγβ : γ < β) (hβ : β < 1) :
    γ / (1 - γ) + (β - γ) / (γ * (β - 2) + 1) / (1 - (β - γ) / (γ * (β - 2) + 1)) =
      β / (1 - β) := by
  have hD : 0 < γ * (β - 2) + 1 := by nlinarith
  have h1 : (1 : ℝ) - (β - γ) / (γ * (β - 2) + 1) = (1 - β) * (1 - γ) / (γ * (β - 2) + 1) := by
    field_simp; ring
  have hβ' : (1 : ℝ) - β ≠ 0 := by linarith
  have hγ' : (1 : ℝ) - γ ≠ 0 := by linarith
  rw [h1]
  field_simp
  ring

end

end Podc.SleepyTOB
