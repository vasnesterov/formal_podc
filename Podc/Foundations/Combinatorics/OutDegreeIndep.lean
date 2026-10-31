/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic

-- CSLib candidate: Cslib/Foundations/Combinatorics/OutDegreeIndep.lean

/-!
# Independent sets in digraphs of bounded out-degree; fibers versus images

(Staged by the PODC 2011 CCvsDSMSeparation formalization.)

* `exists_indep_of_outdeg`: a digraph on `T` with out-degrees `≤ d` has an independent set of
  size `≥ |T| / (2d + 1)` (greedy; the Turán-type bound used in the paper's proof of Lemma 6.10).
* `fiber_or_image`: if `t² ≤ |W|`, a map on `W` has a fiber of size `≥ t` or an image of size
  `≥ t` (the case split of the paper's proof of Lemma 6.10).

Overlap: `SimpleGraph.exists_isIndepSet_card_le_mul`
(`Papers/PODC2024/ListDefectiveColoring/NeighborhoodIndependence.lean`, also a CSLib candidate)
proves the same `(2d+1)` bound for an oriented `SimpleGraph`; merge the two when upstreaming
(one follows from the other). Mathlib has `indepNum` but no degree-based lower bound.
-/

namespace Cslib

open Finset

/-- A digraph on `T` whose out-degrees are at most `d` has an independent set `I` with
`|T| ≤ (2d+1)|I|`. -/
theorem exists_indep_of_outdeg {α : Type*} [DecidableEq α] (out : α → Finset α) (d : ℕ)
    (T : Finset α) (hd : ∀ x ∈ T, (out x).card ≤ d) :
    ∃ I ⊆ T, T.card ≤ (2 * d + 1) * I.card ∧ ∀ x ∈ I, ∀ y ∈ I, y ∈ out x → y = x := by
  induction T using Finset.strongInduction with
  | H T ih =>
  rcases T.eq_empty_or_nonempty with hT | hT
  · exact ⟨∅, by simp, by simp [hT], by simp⟩
  set nb : α → Finset α := fun x => T.filter fun y => y ∈ out x ∨ x ∈ out y with hnb
  have hnb_le : ∀ x ∈ T, (nb x).card ≤ (out x).card + (T.filter fun y : α => x ∈ out y).card := by
    intro x _
    calc (nb x).card ≤ (T.filter fun y : α => y ∈ out x).card
            + (T.filter fun y : α => x ∈ out y).card :=
          by rw [hnb]; simp only; rw [Finset.filter_or]; exact Finset.card_union_le _ _
      _ ≤ _ := by
          refine Nat.add_le_add_right ?_ _
          exact Finset.card_le_card (fun (y : α) hy => (Finset.mem_filter.1 hy).2)
  have hin : ∑ x ∈ T, (T.filter fun y : α => x ∈ out y).card ≤ d * T.card := by
    calc ∑ x ∈ T, (T.filter fun y : α => x ∈ out y).card
        = ∑ y ∈ T, (T.filter fun x : α => x ∈ out y).card := by
          simp only [Finset.card_filter]; exact Finset.sum_comm
      _ ≤ ∑ y ∈ T, d := by
          gcongr with y hy
          exact (Finset.card_le_card (fun x hx => (Finset.mem_filter.1 hx).2)).trans (hd y hy)
      _ = d * T.card := by simp [mul_comm]
  have hsum : ∑ x ∈ T, (nb x).card ≤ 2 * d * T.card := by
    calc ∑ x ∈ T, (nb x).card
        ≤ ∑ x ∈ T, ((out x).card + (T.filter fun y : α => x ∈ out y).card) :=
          Finset.sum_le_sum hnb_le
      _ = ∑ x ∈ T, (out x).card + ∑ x ∈ T, (T.filter fun y : α => x ∈ out y).card :=
          Finset.sum_add_distrib
      _ ≤ d * T.card + d * T.card := by
          gcongr
          calc ∑ x ∈ T, (out x).card ≤ ∑ x ∈ T, d := Finset.sum_le_sum hd
            _ = d * T.card := by simp [mul_comm]
      _ = 2 * d * T.card := by ring
  obtain ⟨x, hxT, hx⟩ : ∃ x ∈ T, (nb x).card ≤ 2 * d := by
    by_contra h
    push Not at h
    have : ∑ x ∈ T, (2 * d + 1) ≤ ∑ x ∈ T, (nb x).card := Finset.sum_le_sum fun x hx => h x hx
    simp only [Finset.sum_const, smul_eq_mul] at this
    have hc : 0 < T.card := Finset.card_pos.2 hT
    nlinarith
  set T' := T \ insert x (nb x) with hT'
  have hT'T : T' ⊂ T := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨Finset.sdiff_subset, fun h => ?_⟩
    have : x ∈ T' := h ▸ hxT
    simp [hT'] at this
  obtain ⟨I', hI', hc, hind⟩ := ih T' hT'T (fun y hy => hd y (Finset.sdiff_subset hy))
  have hxI' : x ∉ I' := fun h => by have := hI' h; simp [hT'] at this
  refine ⟨insert x I', Finset.insert_subset hxT (hI'.trans Finset.sdiff_subset), ?_, ?_⟩
  · rw [Finset.card_insert_of_notMem hxI']
    have h1 : T.card ≤ T'.card + (insert x (nb x)).card := by
      rw [hT']; exact Finset.card_le_card_sdiff_add_card
    have h2 : (insert x (nb x)).card ≤ 2 * d + 1 :=
      (Finset.card_insert_le _ _).trans (by omega)
    nlinarith
  · have hfar : ∀ y ∈ I', ¬ (y ∈ out x ∨ x ∈ out y) := by
      intro y hy h
      have := hI' hy
      simp only [hT', Finset.mem_sdiff, Finset.mem_insert, not_or] at this
      exact this.2.2 (by rw [hnb]; exact Finset.mem_filter.2 ⟨this.1, h⟩)
    intro a ha b hb hab
    rcases Finset.mem_insert.1 ha with ha | ha
    · subst ha
      rcases Finset.mem_insert.1 hb with hb | hb
      · exact hb
      · exact absurd (Or.inl hab) (hfar b hb)
    · rcases Finset.mem_insert.1 hb with hb | hb
      · rw [hb] at hab; exact absurd (Or.inr hab) (hfar a ha)
      · exact hind a ha b hb hab

/-- If `t² ≤ |W|`, then `f` has a fiber of size `≥ t` on `W`, or `f(W)` has size `≥ t`. -/
theorem fiber_or_image {α β : Type*} [DecidableEq β] (W : Finset α) (f : α → β) (t : ℕ)
    (ht : t * t ≤ W.card) :
    (∃ b, t ≤ (W.filter fun x => f x = b).card) ∨ t ≤ (W.image f).card := by
  by_contra h
  push Not at h
  obtain ⟨h1, h2⟩ := h
  rcases Nat.eq_zero_or_pos t with rfl | ht0
  · simp at h2
  have := Finset.card_le_mul_card_image W (t - 1) (fun b _ => Nat.le_sub_one_of_lt (h1 b))
  have h3 : (W.image f).card ≤ t - 1 := Nat.le_sub_one_of_lt h2
  have : W.card ≤ (t - 1) * (t - 1) := this.trans (Nat.mul_le_mul_left _ h3)
  have : (t - 1) * (t - 1) < t * t := Nat.mul_self_lt_mul_self (by omega)
  omega

end Cslib
