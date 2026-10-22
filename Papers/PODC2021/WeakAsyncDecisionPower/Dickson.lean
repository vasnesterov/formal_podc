import Mathlib

/-!
# Upward-closed sets of star configurations are determined by a cutoff

Abstract configurations of a star are pairs `X = (centre state, leaf state count)` in
`Q × (Q → ℕ)`. The order `StarLE X Y` (claim (2) in the proof of Lemma 3.5): same centre, `X.2 ≤ Y.2`
pointwise, and the same support. By Dickson's lemma this order is a well-quasi-order, so every
upward-closed set has finitely many minimal elements; hence it is determined by cutting the counts
off at some `m` (`exists_cutoff_of_upward_closed`).
-/

namespace Podc.WeakAsyncDecisionPower

variable {Q : Type*}

/-- The order on abstract star configurations used in the proof of Lemma 3.5. -/
def StarLE (X Y : Q × (Q → ℕ)) : Prop :=
  X.1 = Y.1 ∧ (∀ q, X.2 q ≤ Y.2 q) ∧ (∀ q, X.2 q = 0 ↔ Y.2 q = 0)

lemma StarLE.refl (X : Q × (Q → ℕ)) : StarLE X X := ⟨rfl, fun _ => le_rfl, fun _ => Iff.rfl⟩

lemma StarLE.trans {X Y Z : Q × (Q → ℕ)} (h₁ : StarLE X Y) (h₂ : StarLE Y Z) : StarLE X Z :=
  ⟨h₁.1.trans h₂.1, fun q => (h₁.2.1 q).trans (h₂.2.1 q), fun q => (h₁.2.2 q).trans (h₂.2.2 q)⟩

/-- Cutting off the leaf counts at `m`. -/
def cutStar (m : ℕ) (X : Q × (Q → ℕ)) : Q × (Q → ℕ) := (X.1, fun q => min (X.2 q) m)

lemma starLE_cutStar {m : ℕ} (hm : 1 ≤ m) (X : Q × (Q → ℕ)) : StarLE (cutStar m X) X :=
  ⟨rfl, fun _ => min_le_left _ _, fun q => by simp only [cutStar]; omega⟩

/-- Dickson's lemma for `StarLE`. -/
lemma starLE_pwo [Finite Q] : (Set.univ : Set (Q × (Q → ℕ))).PartiallyWellOrderedOn StarLE := by
  classical
  rw [Set.partiallyWellOrderedOn_iff_exists_lt]
  intro f _
  let φ : Q × (Q → ℕ) → (Q × (Q → Bool)) × (Q → ℕ) :=
    fun X => ((X.1, fun q => decide (X.2 q = 0)), X.2)
  have h₁ : (Set.univ : Set (Q × (Q → Bool))).PartiallyWellOrderedOn (· = ·) :=
    Set.finite_univ.partiallyWellOrderedOn
  have h₂ : (Set.univ : Set (Q → ℕ)).PartiallyWellOrderedOn (· ≤ ·) :=
    Set.isPWO_of_wellQuasiOrderedLE _
  have h := h₁.prod h₂
  obtain ⟨m, n, hmn, he, hle⟩ := h.exists_lt (f := fun i => φ (f i)) (fun _ => by simp)
  refine ⟨m, n, hmn, ?_, fun q => hle q, fun q => ?_⟩
  · have := congrArg Prod.fst he
    simpa [φ] using this
  · have := congrFun (congrArg Prod.snd he) q
    simpa [φ] using this

/-- An upward-closed set of abstract star configurations is determined by cutting off at some
`m ≥ 1`. -/
theorem exists_cutoff_of_upward_closed [Finite Q] (U : Set (Q × (Q → ℕ)))
    (hU : ∀ X Y, X ∈ U → StarLE X Y → Y ∈ U) :
    ∃ m, 1 ≤ m ∧ ∀ X, X ∈ U ↔ cutStar m X ∈ U := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  let Mins : Set (Q × (Q → ℕ)) := {M | M ∈ U ∧ ∀ Y ∈ U, StarLE Y M → Y = M}
  have hanti : IsAntichain StarLE Mins := by
    intro A hA B hB hne hAB
    exact hne (hB.2 A hA.1 hAB)
  have hfin : Mins.Finite :=
    hanti.finite_of_partiallyWellOrderedOn (starLE_pwo.mono (Set.subset_univ _))
  -- every element of `U` is above a minimal one
  have hmin : ∀ n, ∀ X ∈ U, ∑ q, X.2 q = n → ∃ M ∈ Mins, StarLE M X := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro X hX hn
      by_cases hXm : X ∈ Mins
      · exact ⟨X, hXm, StarLE.refl X⟩
      · simp only [Mins, Set.mem_ofPred_eq, not_and, not_forall] at hXm
        obtain ⟨Y, hY, hYX, hne⟩ := hXm hX
        have hlt : ∑ q, Y.2 q < n := by
          rw [← hn]
          apply Finset.sum_lt_sum (fun q _ => hYX.2.1 q)
          by_contra hall
          push_neg at hall
          apply hne
          exact Prod.ext hYX.1 (funext fun q => le_antisymm (hYX.2.1 q) (hall q (Finset.mem_univ _)))
        obtain ⟨M, hM, hMY⟩ := ih _ hlt Y hY rfl
        exact ⟨M, hM, hMY.trans hYX⟩
  -- a bound on the minimal elements
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, ∀ M ∈ Mins, ∀ q, M.2 q ≤ m₀ := by
    obtain ⟨b, hb⟩ := (hfin.image fun M => Finset.univ.sup M.2).bddAbove
    exact ⟨b, fun M hM q => (Finset.le_sup (f := M.2) (Finset.mem_univ q)).trans
      (hb ⟨M, hM, rfl⟩)⟩
  refine ⟨m₀ + 1, by omega, fun X => ⟨fun hX => ?_, fun h => hU _ _ h (starLE_cutStar (by omega) X)⟩⟩
  obtain ⟨M, hM, hMX⟩ := hmin _ X hX rfl
  refine hU M _ hM.1 ⟨hMX.1, fun q => ?_, fun q => ?_⟩
  · exact le_min (hMX.2.1 q) ((hm₀ M hM q).trans (Nat.le_succ _))
  · rw [hMX.2.2 q]; simp only [cutStar]; omega

end Podc.WeakAsyncDecisionPower
