import Papers.PODC2025.ByzantineStableMatching.Problem
import Cslib.Computability.Distributed.Byzantine.LockStep.Cover
import Cslib.Foundations.Combinatorics.Labelling

/-!
# Grouping parties

Instead of first proving impossibility for tiny systems and then scaling up with Lemma 3 (as the
paper does), our impossibility proofs work directly for every `k ≥ 2`: each side is split into a few
*groups* of size at most the threshold (`exists_split`, from `Fintype.exists_fin_labelling_le`),
and the covering arguments are done at the level of groups.
-/

namespace Papers.PODC2025.ByzantineStableMatching

open Cslib.Byzantine.LockStep Sum

variable {k : ℕ}

/-- Each side can be split into `m` groups (labels `Fin m`) of size at most `t`, two given groups
`a ≠ b` being nonempty, as soon as `2 ≤ k ≤ m t`. -/
lemma exists_split {m t : ℕ} (a b : Fin m) (hab : a ≠ b) (hk : 2 ≤ k) (hkt : k ≤ m * t) :
    ∃ g : Fin k → Fin m, (∃ i, g i = a) ∧ (∃ i, g i = b) ∧ ∀ w, {i | g i = w}.ncard ≤ t := by
  obtain ⟨g, hS, hg⟩ := Fintype.exists_fin_labelling_le (α := Fin k) {a, b}
    (by simpa [Finset.card_pair hab]) (by simpa)
  refine ⟨g, hS a (by simp), hS b (by simp), fun w => ?_⟩
  rw [Set.ncard_eq_toFinset_card']
  simpa using hg w

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
