import Papers.PODC2025.ByzantineStableMatching.Problem

/-!
# Grouping parties

Instead of first proving impossibility for tiny systems and then scaling up with Lemma 3 (as the
paper does), our impossibility proofs work directly for every `k ≥ 2`: each side is split into a few
*groups* (intervals of indices) of size at most the threshold, and the covering arguments are done at
the level of groups. This file provides the interval bookkeeping.
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum

variable {k : ℕ}

lemma ncard_interval_le (k a b : ℕ) : {i : Fin k | a ≤ i.val ∧ i.val < b}.ncard ≤ b - a := by
  rw [Set.ncard_eq_toFinset_card']
  calc (Set.toFinset {i : Fin k | a ≤ i.val ∧ i.val < b}).card ≤ (Finset.Ico a b).card := by
        apply Finset.card_le_card_of_injOn Fin.val
        · intro i hi; simp only [Set.coe_toFinset, Set.mem_ofPred_eq] at hi; simp [hi.1, hi.2]
        · intro i _ j _ h; exact Fin.val_injective h
    _ = b - a := Nat.card_Ico a b

/-- A fibre contained in an interval of length `≤ t` has at most `t` elements. -/
lemma ncard_fiber_le {α : Type*} (g : Fin k → α) (z : α) (a b t : ℕ) (hab : b - a ≤ t)
    (h : ∀ i : Fin k, g i = z → a ≤ i.val ∧ i.val < b) : {i | g i = z}.ncard ≤ t :=
  (Set.ncard_le_ncard (fun i hi => h i hi) (Set.toFinite _)).trans
    ((ncard_interval_le k a b).trans hab)

/-- Split `Fin k` into three consecutive intervals `[0,t)`, `[t,k-t)`, `[k-t,k)` labelled `x`, `y`, `z`. -/
def split3 (k t : ℕ) {α : Type*} (x y z : α) (i : Fin k) : α :=
  if i.val < t then x else if i.val < k - t then y else z

lemma split3_spec {α : Type*} {t : ℕ} {x y z : α} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (ht : 1 ≤ t) (htk : t < k) (hk : k ≤ 3 * t) :
    (∃ i, split3 k t x y z i = x) ∧ (∃ i, split3 k t x y z i = z) ∧
      ∀ w, {i | split3 k t x y z i = w}.ncard ≤ t := by
  refine ⟨⟨⟨0, by omega⟩, by simp [split3]; omega⟩, ⟨⟨k - 1, by omega⟩, ?_⟩, fun w => ?_⟩
  · simp only [split3]; split_ifs <;> first | rfl | omega
  · by_cases hwx : w = x
    · subst hwx
      refine ncard_fiber_le _ _ 0 t t (by omega) fun i hi => ?_
      simp only [split3] at hi
      split_ifs at hi with h1 h2
      · omega
      · exact absurd hi.symm hxy
      · exact absurd hi.symm hxz
    by_cases hwy : w = y
    · subst hwy
      refine ncard_fiber_le _ _ t (k - t) t (by omega) fun i hi => ?_
      simp only [split3] at hi
      split_ifs at hi with h1 h2
      · exact absurd hi hxy
      · omega
      · exact absurd hi.symm hyz
    · refine ncard_fiber_le _ _ (k - t) k t (by omega) fun i hi => ?_
      simp only [split3] at hi
      split_ifs at hi with h1 h2
      · exact absurd hi.symm hwx
      · exact absurd hi.symm hwy
      · omega

/-- Split `Fin k` into two consecutive intervals `[0,k-t)`, `[k-t,k)` labelled `x`, `y`. -/
def split2 (k t : ℕ) {α : Type*} (x y : α) (i : Fin k) : α :=
  if i.val < k - t then x else y

lemma split2_spec {α : Type*} {t : ℕ} {x y : α} (hxy : x ≠ y)
    (_ht : 1 ≤ t) (htk : t < k) (hk : k ≤ 2 * t) :
    (∃ i, split2 k t x y i = x) ∧ (∃ i, split2 k t x y i = y) ∧
      ∀ w, {i | split2 k t x y i = w}.ncard ≤ t := by
  refine ⟨⟨⟨0, by omega⟩, by simp [split2]; omega⟩, ⟨⟨k - 1, by omega⟩, ?_⟩, fun w => ?_⟩
  · simp only [split2]; split_ifs <;> first | rfl | omega
  · by_cases hwx : w = x
    · subst hwx
      refine ncard_fiber_le _ _ 0 (k - t) t (by omega) fun i hi => ?_
      simp only [split2] at hi
      split_ifs at hi with h1
      · omega
      · exact absurd hi.symm hxy
    · refine ncard_fiber_le _ _ (k - t) k t (by omega) fun i hi => ?_
      simp only [split2] at hi
      split_ifs at hi with h1
      · exact absurd hi.symm hwx
      · omega

/-- The group label of a party, given labels for each side. -/
def label {α : Type*} (gL gR : Fin k → α) : Party k → α := Sum.elim gL gR

@[simp] lemma label_inl {α : Type*} (gL gR : Fin k → α) (i : Fin k) : label gL gR (inl i) = gL i := rfl
@[simp] lemma label_inr {α : Type*} (gL gR : Fin k → α) (j : Fin k) : label gL gR (inr j) = gR j := rfl

/-- A union of groups is admissible if its parts on both sides are small enough. -/
lemma mem_thresholds_iff {tL tR : ℕ} (B : Set (Party k)) :
    B ∈ thresholds k tL tR ↔ (inl ⁻¹' B).ncard ≤ tL ∧ (inr ⁻¹' B).ncard ≤ tR := Iff.rfl

lemma label_mem_thresholds {α : Type*} {tL tR : ℕ} (gL gR : Fin k → α) (S : Set α)
    (hL : (gL ⁻¹' S).ncard ≤ tL) (hR : (gR ⁻¹' S).ncard ≤ tR) :
    {p | label gL gR p ∈ S} ∈ thresholds k tL tR := ⟨hL, hR⟩

end Papers.PODC2025.ByzantineStableMatching
