import Papers.PODC2017.PPVerification.Threshold
import Mathlib.Order.Prod.Lex.Basic

/-!
# Proposition 18, first layer: every execution of `P_thr[T₁]` is silent

Ranking function (lexicographic): number of leaders, total absolute value of non-leaders,
number of leaders whose opinion disagrees with their value, number of non-leaders whose opinion
can still be flipped by a value-preserving interaction.
-/

namespace Podc.PPVerification.Threshold

open Cslib.PopulationProtocol Cslib.TransitionSystem

variable {v : ℤ} (c : ℤ)

namespace T1Rank

/-- Weight: leaders. -/
def wL (s : St v) : ℕ := if s.1 = true then 1 else 0

/-- Weight: absolute value of a non-leader. -/
def wA (s : St v) : ℕ := if s.1 = true then 0 else (s.2.1 : ℤ).natAbs

/-- Weight: leaders whose opinion disagrees with their value. -/
def wE (s : St v) : ℕ := if s.1 = true ∧ s.2.2 ≠ decide ((s.2.1 : ℤ) < c) then 1 else 0

/-- Weight: non-leaders with a "wrong" opinion for their sign. -/
def wF (s : St v) : ℕ :=
  if s.1 = false ∧ ((0 < (s.2.1 : ℤ) ∧ s.2.2 = true) ∨ ((s.2.1 : ℤ) ≤ 0 ∧ s.2.2 = false))
  then 1 else 0

/-- Lexicographic decrease of four natural numbers. -/
def Lex4 (a b d e a' b' d' e' : ℕ) : Prop :=
  a' < a ∨ (a' = a ∧ (b' < b ∨ (b' = b ∧ (d' < d ∨ (d' = d ∧ e' < e)))))

/-- The ranking function. -/
def rank (C : Multiset (St v)) : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ :=
  toLex ((C.map wL).sum, toLex ((C.map wA).sum, toLex ((C.map (wE c)).sum, (C.map wF).sum)))

/-- Unfolding the lexicographic order on `ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ`. -/
theorem lex_lt_iff (a b d e a' b' d' e' : ℕ) :
    toLex (a', toLex (b', toLex (d', e'))) < (toLex (a, toLex (b, toLex (d, e))) : ℕ ×ₗ ℕ ×ₗ ℕ ×ₗ ℕ)
      ↔ Lex4 a b d e a' b' d' e' := by
  simp [Prod.Lex.lt_iff, Lex4]

/-- The ranking function decreases on a non-silent `mainT` transition of `T₁`
(stated on the two pre- and post-states). -/
theorem key {m n : Set.Icc (-v) v} {o o' ℓ : Bool} (hc : |c| + 1 ≤ v)
    (h1 : ¬ (ℓ = false ∧ (fV m n : ℤ) = m ∧ (gV m n : ℤ) = n ∧
      decide ((fV m n : ℤ) < c) = o ∧ decide ((fV m n : ℤ) < c) = o'))
    (h2 : ¬ (ℓ = false ∧ c ≤ (m : ℤ) ∧ (n : ℤ) = 0 ∧ o = false ∧ o' = true)) :
    Lex4 (wL ((true, m, o) : St v) + wL ((ℓ, n, o') : St v))
      (wA ((true, m, o) : St v) + wA ((ℓ, n, o') : St v))
      (wE c ((true, m, o) : St v) + wE c ((ℓ, n, o') : St v))
      (wF ((true, m, o) : St v) + wF ((ℓ, n, o') : St v))
      (wL ((true, fV m n, decide ((fV m n : ℤ) < c)) : St v) +
        wL ((false, gV m n, decide ((fV m n : ℤ) < c)) : St v))
      (wA ((true, fV m n, decide ((fV m n : ℤ) < c)) : St v) +
        wA ((false, gV m n, decide ((fV m n : ℤ) < c)) : St v))
      (wE c ((true, fV m n, decide ((fV m n : ℤ) < c)) : St v) +
        wE c ((false, gV m n, decide ((fV m n : ℤ) < c)) : St v))
      (wF ((true, fV m n, decide ((fV m n : ℤ) < c)) : St v) +
        wF ((false, gV m n, decide ((fV m n : ℤ) < c)) : St v)) := by
  obtain ⟨M, hM⟩ := m
  obtain ⟨N, hN⟩ := n
  rw [Set.mem_Icc] at hM hN
  have hc' := abs_le.1 (show |c| ≤ v - 1 by omega)
  simp only [fV, gV, clampV, wL, wA, wE, wF, Lex4] at *
  generalize hβ : decide (max (-v) (min v (M + N)) < c) = β at *
  have hβ' : (max (-v) (min v (M + N)) < c) ↔ β = true := by rw [← hβ]; simp
  cases ℓ <;> cases o <;> cases o' <;> cases β <;> simp at h1 h2 hβ' ⊢ <;> split_ifs <;> omega

end T1Rank

/-- **Proposition 18, condition (a) for `T₁`.** Every (fair or unfair) execution of `P_thr[T₁]`
is silent. -/
theorem t1_silent {Λ : Type*} (a : Λ → ℤ) (ha : ∀ i, |a i| ≤ v) (hc : |c| + 1 ≤ v) :
    ∀ E : Run ((protocol c a ha).restrict (T1 c)).Step, E.Silent := by
  refine MProtocol.restrict_silent_of_measure (T1Rank.rank c) ?_
  rintro ⟨p, q, p', q'⟩ ⟨ht, hnI⟩ hns C hle
  rcases ht with ⟨hp, ht⟩ | ⟨hp, h1, h2⟩
  · simp only at hp ht
    rw [ht] at hns hnI hle ⊢
    obtain ⟨pl, m, o⟩ := p
    obtain ⟨ℓ, n, o'⟩ := q
    simp only at hp
    subst hp
    have hkey := T1Rank.key c (m := m) (n := n) (o := o) (o' := o') (ℓ := ℓ) hc
      (fun ⟨hl, hf, hg, ho, ho'⟩ => hns (MProtocol.silent_of_mem_idTrans
        ⟨by rw [← ho]; simp [mainT, Subtype.ext hf], by rw [← ho']; simp [mainT, hl, Subtype.ext hg]⟩))
      (fun ⟨hl, hm, hn, ho, ho'⟩ => hnI ⟨m, n, hm, hn, by simp [mainT, Transition.pre, hl, ho, ho']⟩)
    have hf : (mainT c (true, m, o) (ℓ, n, o')).Fires C
        (C - (mainT c (true, m, o) (ℓ, n, o')).pre + (mainT c (true, m, o) (ℓ, n, o')).post) :=
      ⟨hle, rfl⟩
    generalize C - (mainT c (true, m, o) (ℓ, n, o')).pre + (mainT c (true, m, o) (ℓ, n, o')).post
      = C' at hf ⊢
    have eL := hf.sum_map T1Rank.wL
    have eA := hf.sum_map T1Rank.wA
    have eE := hf.sum_map (T1Rank.wE c)
    have eF := hf.sum_map T1Rank.wF
    simp only [Transition.pre, Transition.post, mainT, Multiset.insert_eq_cons, Multiset.map_cons,
      Multiset.map_singleton, Multiset.sum_cons, Multiset.sum_singleton] at eL eA eE eF
    rw [T1Rank.rank, T1Rank.rank, T1Rank.lex_lt_iff]
    unfold T1Rank.Lex4 at hkey ⊢
    omega
  · exact absurd (MProtocol.silent_of_mem_idTrans ⟨h1, h2⟩) hns

end Podc.PPVerification.Threshold
