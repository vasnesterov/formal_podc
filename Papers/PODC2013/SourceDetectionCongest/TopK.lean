import Mathlib

/-!
# `top_k` of a finite linearly ordered set

`topk k F` is the set of the `k` smallest elements of a finite set `F` in a linear order (all of
`F` if `#F ≤ k`): an element is in it iff fewer than `k` elements of `F` are smaller. This is the
set version of the paper's `top_k(L)` ("the list of the first `k` elements of `L`, or `L` if
`|L| < k`") for a lexicographically sorted list `L` without duplicates; `sort_topk` says that
sorting `topk k F` gives exactly the first `k` entries of the sorted list of `F`.

-- CSLib candidate (generic order theory on finsets).
-/

namespace Podc.SourceDetectionCongest

open Finset

variable {α : Type*} [LinearOrder α]

/-- The `k` smallest elements of `F`. -/
def topk (k : ℕ) (F : Finset α) : Finset α :=
  F.filter fun x => #(F.filter (· < x)) < k

variable {k k' : ℕ} {F : Finset α} {x y : α}

lemma mem_topk : x ∈ topk k F ↔ x ∈ F ∧ #(F.filter (· < x)) < k := mem_filter

lemma topk_subset : topk k F ⊆ F := filter_subset _ _

@[simp] lemma topk_zero : topk 0 F = ∅ := by
  ext x; simp [mem_topk]

lemma topk_mono (h : k ≤ k') : topk k F ⊆ topk k' F := fun x hx => by
  rw [mem_topk] at *; exact ⟨hx.1, lt_of_lt_of_le hx.2 h⟩

/-- `topk` is downward closed in `F`. -/
lemma mem_topk_of_le (hx : x ∈ topk k F) (hy : y ∈ F) (hyx : y ≤ x) : y ∈ topk k F := by
  rw [mem_topk] at *
  refine ⟨hy, lt_of_le_of_lt (card_le_card fun z hz => ?_) hx.2⟩
  simp only [mem_filter] at *
  exact ⟨hz.1, lt_of_lt_of_le hz.2 hyx⟩

/-- An element strictly below an element of `topk k F` is in `topk (k - 1) F`. -/
lemma mem_topk_pred_of_lt (hx : x ∈ topk k F) (hy : y ∈ F) (hyx : y < x) :
    y ∈ topk (k - 1) F := by
  rw [mem_topk] at *
  refine ⟨hy, ?_⟩
  have : #(F.filter (· < y)) < #(F.filter (· < x)) := by
    apply card_lt_card
    refine ⟨fun z hz => ?_, fun h => ?_⟩
    · simp only [mem_filter] at *; exact ⟨hz.1, hz.2.trans hyx⟩
    · have := h (mem_filter.2 ⟨hy, hyx⟩); simp at this
  omega

/-- The `i`-th element of `F` (in increasing order) has exactly `i` smaller elements in `F`. -/
lemma card_filter_lt_orderEmbOfFin (i : Fin #F) :
    #(F.filter (· < F.orderEmbOfFin rfl i)) = i := by
  set f := F.orderEmbOfFin rfl
  have : F.filter (· < f i) = (univ.filter (· < i)).map f.toEmbedding := by
    ext z
    simp only [mem_filter, mem_map, mem_univ, true_and, RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨hz, hlt⟩
      have : z ∈ Set.range f := by rw [range_orderEmbOfFin]; exact hz
      obtain ⟨j, rfl⟩ := this
      exact ⟨j, f.lt_iff_lt.1 hlt, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨orderEmbOfFin_mem _ _ _, f.lt_iff_lt.2 hj⟩
  rw [this, card_map]
  simpa using Fin.card_filter_val_lt (n := #F) (m := i)

lemma mem_topk_iff_orderEmbOfFin :
    x ∈ topk k F ↔ ∃ i : Fin #F, (i : ℕ) < k ∧ F.orderEmbOfFin rfl i = x := by
  constructor
  · intro hx
    have hxF := topk_subset hx
    have : x ∈ Set.range (F.orderEmbOfFin rfl) := by rw [range_orderEmbOfFin]; exact hxF
    obtain ⟨i, rfl⟩ := this
    refine ⟨i, ?_, rfl⟩
    have := (mem_topk.1 hx).2
    rwa [card_filter_lt_orderEmbOfFin] at this
  · rintro ⟨i, hi, rfl⟩
    exact mem_topk.2 ⟨orderEmbOfFin_mem _ _ _, by rwa [card_filter_lt_orderEmbOfFin]⟩

lemma card_topk : #(topk k F) = min k #F := by
  have : topk k F = (univ.filter fun i : Fin #F => (i : ℕ) < k).map
      (F.orderEmbOfFin rfl).toEmbedding := by
    ext x
    rw [mem_topk_iff_orderEmbOfFin]
    simp
  rw [this, card_map, Fin.card_filter_val_lt, min_comm]

/-- At most `k' - k` elements are in `topk k' F` but not in `topk k F`. -/
lemma card_topk_sdiff_le : #(topk k' F \ topk k F) ≤ k' - k := by
  rcases le_total k k' with h | h
  · rw [card_sdiff_of_subset (topk_mono h), card_topk, card_topk]; omega
  · rw [sdiff_eq_empty_iff_subset.2 (topk_mono h)]; simp

/-- Sorting `topk k F` gives the first `k` elements of the sorted list of `F`: `topk` is the
paper's `top_k`. -/
theorem sort_topk : (topk k F).sort (· ≤ ·) = (F.sort (· ≤ ·)).take k := by
  apply List.SortedLT.eq_of_mem_iff (sortedLT_sort _)
  · exact List.sortedLT_iff_pairwise.2
      ((List.sortedLT_iff_pairwise.1 (sortedLT_sort F)).sublist (List.take_sublist _ _))
  · intro a
    rw [mem_sort, mem_topk_iff_orderEmbOfFin, List.mem_take_iff_getElem]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨i, by simp [length_sort]; omega, ?_⟩
      rw [orderEmbOfFin_apply]; rfl
    · rintro ⟨i, hi, rfl⟩
      simp only [length_sort, lt_min_iff] at hi
      exact ⟨⟨i, hi.2⟩, hi.1, by rw [orderEmbOfFin_apply]; rfl⟩

end Podc.SourceDetectionCongest
