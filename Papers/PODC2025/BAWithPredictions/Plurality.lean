import Mathlib

/-!
# Plurality votes

`plur X f d`: a value of `f` that occurs most often on `X` (`d` if `X` is empty). Ties are
broken arbitrarily (by choice); the only property we use is `plur_eq_of_majority`: a value that
occurs on a strict majority of `X` is the plurality.

`cnt X f w`: the number of elements of `X` on which `f` takes the value `w`.
-/

namespace BAWithPredictions

open Finset

variable {ι α : Type*} [DecidableEq ι] [DecidableEq α]

/-- The number of `j ∈ X` with `f j = w`. -/
def cnt (X : Finset ι) (f : ι → α) (w : α) : ℕ := (X.filter fun j => f j = w).card

/-- A most frequent value of `f` on `X` (`d` if `X = ∅`). -/
noncomputable def plur (X : Finset ι) (f : ι → α) (d : α) : α :=
  if h : X.Nonempty then f (Classical.choose (X.exists_max_image (fun j => cnt X f (f j)) h))
  else d

theorem cnt_add_cnt_le {X : Finset ι} {f : ι → α} {w w' : α} (h : w ≠ w') :
    cnt X f w + cnt X f w' ≤ X.card := by
  unfold cnt
  rw [← card_union_of_disjoint]
  · exact card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))
  · rw [disjoint_left]
    intro j h1 h2
    simp only [mem_filter] at h1 h2
    exact h (h1.2.symm.trans h2.2)

/-- A value occurring on a strict majority of `X` is the plurality. -/
theorem plur_eq_of_majority {X : Finset ι} {f : ι → α} {d w : α}
    (h : X.card < 2 * cnt X f w) : plur X f d = w := by
  have hne : X.Nonempty := by
    rw [← card_pos]; have := card_le_card (filter_subset (fun j => f j = w) X); unfold cnt at h
    omega
  unfold plur
  rw [dite_cond_eq_true (eq_true hne)]
  obtain ⟨hj, hmax⟩ := Classical.choose_spec (X.exists_max_image (fun j => cnt X f (f j)) hne)
  set j := Classical.choose (X.exists_max_image (fun j => cnt X f (f j)) hne)
  by_contra hfj
  obtain ⟨j', hj'⟩ : ∃ j', j' ∈ X ∧ f j' = w := by
    have : (X.filter fun j => f j = w).Nonempty := by
      rw [← card_pos]; unfold cnt at h; omega
    obtain ⟨j', hj'⟩ := this
    exact ⟨j', (mem_filter.mp hj').1, (mem_filter.mp hj').2⟩
  have h1 := hmax j' hj'.1
  rw [hj'.2] at h1
  have h2 := cnt_add_cnt_le (X := X) (f := f) hfj
  omega

end BAWithPredictions
