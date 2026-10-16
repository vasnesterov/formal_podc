import Mathlib

/-!
# Byzantine Agreement with Predictions — basic definitions

Ben-David, Dzulfikar, Ellen, Gilbert, *Byzantine Agreement with Predictions*, PODC 2025
(arXiv:2505.01793). Section 3 ("Model").

* A **classification prediction** of process `i` is a vector `a i : P → Bool`; `a i j = true`
  means "`p_j` is predicted to be honest", `false` means "predicted faulty".
* `wrongBits F a`: the paper's `B = B_F + B_H`, the number of incorrect bits in the predictions
  given to *honest* processes (processes outside `F`); the bits given to faulty processes are not
  counted.
* `correctPred F`: the correct classification `ĉ` (`ĉ j = true ↔ j ∉ F`).
-/

namespace BAWithPredictions

open Finset

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- The correct classification `ĉ` when `F` is the set of faulty processes. -/
def correctPred (F : Finset P) : P → Bool := fun j => decide (j ∉ F)

/-- The number of incorrect bits of the prediction vector `ai` (of one process) when `F` is the
faulty set. -/
def wrongBitsOf (F : Finset P) (ai : P → Bool) : ℕ :=
  (univ.filter fun j => ai j ≠ correctPred F j).card

/-- **The paper's `B`**: the total number of incorrect prediction bits given to honest processes
(Section 3: `B = B_F + B_H`). -/
def wrongBits (F : Finset P) (a : P → P → Bool) : ℕ :=
  ∑ i ∈ univ.filter (· ∉ F), wrongBitsOf F (a i)

/-- `B_F`: bits that predict a faulty process to be honest. -/
def wrongBitsF (F : Finset P) (a : P → P → Bool) : ℕ :=
  ∑ i ∈ univ.filter (· ∉ F), (F.filter fun j => a i j = true).card

/-- `B_H`: bits that predict an honest process to be faulty. -/
def wrongBitsH (F : Finset P) (a : P → P → Bool) : ℕ :=
  ∑ i ∈ univ.filter (· ∉ F), ((univ.filter (· ∉ F)).filter fun j => a i j = false).card

omit [Fintype P] in
@[simp] theorem correctPred_apply (F : Finset P) (j : P) : correctPred F j = decide (j ∉ F) := rfl

theorem wrongBitsOf_correctPred (F : Finset P) : wrongBitsOf F (correctPred F) = 0 := by
  simp [wrongBitsOf]

/-- Correct predictions have no wrong bits. -/
theorem wrongBits_correct (F : Finset P) : wrongBits F (fun _ => correctPred F) = 0 := by
  simp [wrongBits, wrongBitsOf_correctPred]

theorem wrongBitsOf_eq (F : Finset P) (ai : P → Bool) :
    wrongBitsOf F ai = (F.filter fun j => ai j = true).card +
      ((univ.filter (· ∉ F)).filter fun j => ai j = false).card := by
  unfold wrongBitsOf
  rw [← card_union_of_disjoint]
  · congr 1
    ext j
    by_cases hj : j ∈ F <;> cases h : ai j <;> simp [hj, h]
  · rw [disjoint_left]
    intro j h1 h2
    simp only [mem_filter, mem_univ, true_and] at h1 h2
    exact h2.1 h1.1

/-- `B = B_F + B_H`. -/
theorem wrongBits_eq_add (F : Finset P) (a : P → P → Bool) :
    wrongBits F a = wrongBitsF F a + wrongBitsH F a := by
  simp only [wrongBits, wrongBitsF, wrongBitsH, wrongBitsOf_eq, sum_add_distrib]

end BAWithPredictions
