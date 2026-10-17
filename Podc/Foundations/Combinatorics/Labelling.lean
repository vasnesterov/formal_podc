import Cslib.Foundations.Combinatorics.Labelling

-- CSLib candidate: Cslib/Foundations/Combinatorics/Labelling.lean (append to the existing file)

/-!
# Disjoint groups of a prescribed size

Addition to `Cslib/Foundations/Combinatorics/Labelling.lean`: partition-style lower-bound arguments
("split the processes into `k + 1` disjoint groups of `n - f` processes") need `m` pairwise
disjoint groups of size `ℓ`, which exist as soon as `m * ℓ` does not exceed the number of elements.
This is the special case of `Finset.exists_labelling` with `m` classes of size exactly `ℓ` and one
class for the remaining elements.

## Main statements

* `Finset.exists_pairwise_disjoint_card_eq`: `m` pairwise disjoint subsets of `t` of size `ℓ`, if
  `m * ℓ ≤ #t`;
* `Fintype.exists_pairwise_disjoint_card_eq`: the same for all elements of a finite type.
-/

open Finset Function

variable {α : Type*}

/-- A finset `t` with `m * ℓ ≤ #t` contains `m` pairwise disjoint subsets of size `ℓ`. -/
theorem Finset.exists_pairwise_disjoint_card_eq (t : Finset α) {m ℓ : ℕ} (h : m * ℓ ≤ #t) :
    ∃ G : Fin m → Finset α, (∀ i, G i ⊆ t) ∧ (∀ i, #(G i) = ℓ) ∧ Pairwise (Disjoint on G) := by
  classical
  have hsum (c : ℕ) : ∑ i ∈ range (m + 1), (if i < m then ℓ else c) = m * ℓ + c := by
    rw [sum_range_succ, if_neg (lt_irrefl m), sum_congr rfl fun i hi => if_pos (mem_range.1 hi)]
    simp
  obtain ⟨g, -, hg⟩ := t.exists_labelling (m + 1) (fun i => if i < m then ℓ else 0)
    (fun i => if i < m then ℓ else #t) (fun i _ => by split_ifs <;> omega)
    (by rw [hsum]; omega) (by rw [hsum]; omega)
  refine ⟨fun i => {a ∈ t | g a = i}, fun i => filter_subset _ _, fun i => ?_, fun i j hij => ?_⟩
  · have := hg i (by omega)
    simp only [i.isLt, if_true] at this
    exact le_antisymm this.2 this.1
  · exact disjoint_filter.2 fun a _ hi hj => hij (Fin.ext (hi.symm.trans hj))

/-- A finite type with `m * ℓ ≤ card α` contains `m` pairwise disjoint subsets of size `ℓ`. -/
theorem Fintype.exists_pairwise_disjoint_card_eq [Fintype α] {m ℓ : ℕ} (h : m * ℓ ≤ card α) :
    ∃ G : Fin m → Finset α, (∀ i, #(G i) = ℓ) ∧ Pairwise (Disjoint on G) := by
  obtain ⟨G, -, hG⟩ := (univ : Finset α).exists_pairwise_disjoint_card_eq (by simpa using h)
  exact ⟨G, hG⟩
