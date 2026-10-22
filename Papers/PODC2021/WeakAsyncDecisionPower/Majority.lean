import Papers.PODC2021.WeakAsyncDecisionPower.Cutoff
import Papers.PODC2021.WeakAsyncDecisionPower.NonCounting

/-!
# No `DAf`- or `dAF`-automaton decides majority (Corollary 3.6)

Labels are `Bool` (`true` = `a`, `false` = `b`); `majority G` holds iff more nodes carry `a` than
`b`. The two witnesses are stars with `K + 2` nodes labelled `a` and `K + 1` resp. `K + 2` nodes
labelled `b`: they have the same label count cut off at `K`, but differ on majority.
-/

namespace Podc.WeakAsyncDecisionPower

open Cslib.DistributedAutomata Set

/-- The majority property: more nodes labelled `true` (`a`) than `false` (`b`). -/
def majority (G : LGraph Bool) : Prop := G.count false < G.count true

/-- A star whose centre and `p` leaves are labelled `true` and whose other `q` leaves are labelled
`false`. -/
def twoStar (p q : ℕ) : LGraph Bool :=
  starL (Fin p ⊕ Fin q) true (Sum.elim (fun _ => true) (fun _ => false))

lemma twoStar_count_true (p q : ℕ) : (twoStar p q).count true = p + 1 := by
  rw [twoStar, starL_count, if_pos rfl]
  have : {l : Fin p ⊕ Fin q | Sum.elim (fun _ => true) (fun _ => false) l = true} = range Sum.inl := by
    ext l; cases l <;> simp
  rw [this, ncard_range_of_injective Sum.inl_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  omega

lemma twoStar_count_false (p q : ℕ) : (twoStar p q).count false = q := by
  rw [twoStar, starL_count, if_neg (by decide)]
  have : {l : Fin p ⊕ Fin q | Sum.elim (fun _ => true) (fun _ => false) l = false} =
      range Sum.inr := by
    ext l; cases l <;> simp
  rw [this, ncard_range_of_injective Sum.inr_injective, Nat.card_eq_fintype_card,
    Fintype.card_fin]
  omega

lemma twoStar_admissible (p q : ℕ) (h : 2 ≤ p + q) : (twoStar p q).Admissible ⊤ := by
  have hc : 2 ≤ Nat.card (Fin p ⊕ Fin q) := by simpa using h
  exact starL_admissible _ _ hc

/-- **Corollary 3.6.** No automaton with adversarial scheduling (`DAf`) and no non-counting
automaton (`dAF`, and also `dAf`) decides majority — for any selection constraint. -/
theorem corollary_3_6 {Q : Type} [Finite Q] (A : Automaton Bool Q)
    (hA : A.fair = .adversarial ∨ A.M.β = 1) : ¬ A.Decides ⊤ majority := by
  rintro ⟨hcons, hdec⟩
  have hL : A.IsLabelling ⊤ := by
    intro G H hG hH hc
    rw [hdec G hG, hdec H hH, majority, majority, hc]
  obtain ⟨K, hK⟩ : ∃ K, ∀ G H : LGraph Bool, G.Admissible ⊤ → H.Admissible ⊤ →
      cutoff K G.count = cutoff K H.count → (A.Accepts G ↔ A.Accepts H) := by
    rcases hA with h | h
    · exact ⟨_, fun G H hG hH => lemma_3_4 A h hcons hL hG hH⟩
    · exact lemma_3_5 A h hcons hL
  have h1 := twoStar_admissible (K + 1) (K + 1) (by omega)
  have h2 := twoStar_admissible (K + 1) (K + 2) (by omega)
  have hcut : cutoff K (twoStar (K + 1) (K + 1)).count = cutoff K (twoStar (K + 1) (K + 2)).count := by
    funext b
    cases b <;> simp only [cutoff, twoStar_count_true, twoStar_count_false] <;> omega
  have hm1 : majority (twoStar (K + 1) (K + 1)) := by
    rw [majority, twoStar_count_true, twoStar_count_false]; omega
  have hm2 : ¬ majority (twoStar (K + 1) (K + 2)) := by
    rw [majority, twoStar_count_true, twoStar_count_false]; omega
  exact hm2 ((hdec _ h2).1 ((hK _ _ h1 h2 hcut).1 ((hdec _ h1).2 hm1)))

end Podc.WeakAsyncDecisionPower
