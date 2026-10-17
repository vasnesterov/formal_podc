import Cslib.Foundations.Combinatorics.Labelling
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset

-- CSLib candidate: Cslib/Foundations/Combinatorics/Labelling.lean (append to the existing file)

/-!
# Disjoint groups of a prescribed size; labellings into `Fin k`

Additions to `Cslib/Foundations/Combinatorics/Labelling.lean`.

Partition-style lower-bound arguments
("split the processes into `k + 1` disjoint groups of `n - f` processes") need `m` pairwise
disjoint groups of size `ℓ`, which exist as soon as `m * ℓ` does not exceed the number of elements.
This is the special case of `Finset.exists_labelling` with `m` classes of size exactly `ℓ` and one
class for the remaining elements.

## Main statements

* `Finset.exists_pairwise_disjoint_card_eq`: `m` pairwise disjoint subsets of `t` of size `ℓ`, if
  `m * ℓ ≤ #t`;
* `Fintype.exists_pairwise_disjoint_card_eq`: the same for all elements of a finite type.

Lower-bound executions usually name their groups by a small finite type, so labels in `Fin k`
(rather than natural numbers `< k`) are more convenient:

* `Fintype.exists_fin_labelling`: `Fintype.exists_labelling` with labels in `Fin k` and bounds
  `lo hi : Fin k → ℕ`;
* `Fintype.exists_fin_labelling_le`: every class has at most `t` elements and the classes of a
  given set `S` of labels are nonempty, provided `#S ≤ card α ≤ k * t`.
-/

open Finset Function

variable {α : Type*}

/-- A finset `t` with `m * ℓ ≤ #t` contains `m` pairwise disjoint subsets of size `ℓ`. -/
theorem Finset.exists_pairwise_disjoint_card_eq (t : Finset α) {m ℓ : ℕ} (h : m * ℓ ≤ #t) :
    ∃ G : Fin m → Finset α, (∀ i, G i ⊆ t) ∧ (∀ i, #(G i) = ℓ) ∧ Pairwise (Disjoint on G) := by
  classical
  have hsum (c : ℕ) : ∑ i ∈ range (m + 1), (if i < m then ℓ else c) = m * ℓ + c := by
    rw [sum_range_succ, ite_eq_right_of_eq_false _ _ (eq_false (lt_irrefl m)),
      sum_congr rfl fun i hi => ite_eq_left_of_eq_true _ _ (eq_true (mem_range.1 hi))]
    simp
  obtain ⟨g, -, hg⟩ := t.exists_labelling (m + 1) (fun i => if i < m then ℓ else 0)
    (fun i => if i < m then ℓ else #t) (fun i _ => by split_ifs <;> omega)
    (by rw [hsum]; omega) (by rw [hsum]; omega)
  refine ⟨fun i => {a ∈ t | g a = i}, fun i => filter_subset _ _, fun i => ?_, fun i j hij => ?_⟩
  · have := hg i (by omega)
    simp only [i.isLt, ite_true] at this
    exact le_antisymm this.2 this.1
  · exact disjoint_filter.2 fun a _ hi hj => hij (Fin.ext (hi.symm.trans hj))

/-- A finite type with `m * ℓ ≤ card α` contains `m` pairwise disjoint subsets of size `ℓ`. -/
theorem Fintype.exists_pairwise_disjoint_card_eq [Fintype α] {m ℓ : ℕ} (h : m * ℓ ≤ card α) :
    ∃ G : Fin m → Finset α, (∀ i, #(G i) = ℓ) ∧ Pairwise (Disjoint on G) := by
  obtain ⟨G, -, hG⟩ := (univ : Finset α).exists_pairwise_disjoint_card_eq (by simpa using h)
  exact ⟨G, hG⟩

/-- `Fintype.exists_labelling` with labels in `Fin k`: the elements of a finite type can be
labelled by `Fin k` so that the class of `i` has between `lo i` and `hi i` elements, provided
`lo i ≤ hi i` and `∑ lo ≤ card α ≤ ∑ hi`. -/
theorem Fintype.exists_fin_labelling [Fintype α] {k : ℕ} (lo hi : Fin k → ℕ)
    (hle : ∀ i, lo i ≤ hi i) (hlo : ∑ i, lo i ≤ card α) (hhi : card α ≤ ∑ i, hi i) :
    ∃ g : α → Fin k, ∀ i, lo i ≤ #{a | g a = i} ∧ #{a | g a = i} ≤ hi i := by
  classical
  let ext (f : Fin k → ℕ) (i : ℕ) : ℕ := if h : i < k then f ⟨i, h⟩ else 0
  have hsum (f : Fin k → ℕ) : ∑ i ∈ range k, ext f i = ∑ i, f i := by
    rw [Finset.sum_range]; simp [ext]
  obtain ⟨g, hg, hc⟩ := Fintype.exists_labelling k (ext lo) (ext hi)
    (fun i hi => by simp only [ext, hi, ↓reduceDIte]; exact hle _) (by rwa [hsum]) (by rwa [hsum])
  refine ⟨fun a => ⟨g a, hg a⟩, fun i => ?_⟩
  simpa [ext, Fin.ext_iff] using hc i i.isLt

/-- The elements of a finite type with `#S ≤ card α ≤ k * t` can be labelled by `Fin k` so that
every class has at most `t` elements and the classes of the labels in `S` are nonempty. -/
theorem Fintype.exists_fin_labelling_le [Fintype α] {k t : ℕ} (S : Finset (Fin k))
    (hS : #S ≤ card α) (hk : card α ≤ k * t) :
    ∃ g : α → Fin k, (∀ i ∈ S, ∃ a, g a = i) ∧ ∀ i, #{a | g a = i} ≤ t := by
  classical
  have ht : S.Nonempty → 1 ≤ t := fun ⟨i, _⟩ => by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · have := (Finset.card_pos.2 ⟨i, ‹_›⟩).trans_le hS; simp at hk; omega
    · exact h
  obtain ⟨g, hg⟩ := Fintype.exists_fin_labelling (fun i => if i ∈ S then 1 else 0) (fun _ => t)
    (fun i => by split_ifs with h; exacts [ht ⟨i, h⟩, Nat.zero_le _])
    (by simpa [Finset.sum_boole] using hS) (by simpa using hk)
  refine ⟨g, fun i hi => ?_, fun i => (hg i).2⟩
  obtain ⟨a, ha⟩ := Finset.card_pos.1 (by simpa [hi] using (hg i).1)
  exact ⟨a, (mem_filter.1 ha).2⟩
