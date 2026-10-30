import Papers.PODC2023.PPDoubleExpThresholds.LargeSym

/-!
# Lemmas 9–12 at all levels (the induction of Appendix A.2)

The lemmas about `AssertProper`, `Zero`, `IncrPair` and `Large` depend on each other across levels
("proof fragments"); `levels` assembles them by induction on the level.
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

/-- All of Lemmas 9–12 at level `i` (with Lemma 11(c) restricted to `j < i`, see
`lemma_11c_false`). -/
structure LevelOK (n i : ℕ) : Prop where
  largeB : LargeB n i
  largeR : ∀ k, Robust n (.large i k)
  apA : APA n i
  apB : APB n i
  apC : APC n i
  apR : Robust n (.assertProper i)
  zeroB : ZeroB n i
  zeroC : ZeroC n i
  zeroR : ∀ k, Robust n (.zero i k)
  incrA : IncrA n i
  incrB : IncrB n i
  incrG : IncrG n i
  incrR : ∀ bx by', RobustOn n (fun j => j < i) (.incrPair i bx by')

/-- The facts about `AssertProper(j)` used at higher levels (also true for `j = 0`). -/
structure APOK (n j : ℕ) : Prop where
  apA : APA n j
  apB : APB n j
  apR : Robust n (.assertProper j)

theorem apOK_zero : APOK n 0 := by
  refine ⟨apa_zero, fun j hj hj0 => by omega, fun j _ _ _ C OF _ => ?_⟩
  obtain ⟨hR, -, hT⟩ := ap_zero C OF
  refine ⟨hT, fun C' OF' b h => ?_⟩
  obtain ⟨h1, h2, -⟩ := (hR C' OF' b).1 h
  subst h1 h2
  exact ⟨rfl, by assumption⟩

theorem LevelOK.apOK {i : ℕ} (h : LevelOK n i) : APOK n i := ⟨h.apA, h.apB, h.apR⟩

theorem robust_of_split {p : Proc} {i : ℕ} (h1 : RobustOn n (fun j => i ≤ j) p)
    (h2 : RobustOn n (fun j => j < i) p) : Robust n p := by
  intro j hj hjn _
  rcases Nat.lt_or_ge j i with h | h
  · exact h2 j hj hjn h
  · exact h1 j hj hjn h

/-- **Lemmas 9–12 hold at every level** `1 ≤ i ≤ n`. -/
theorem levels : ∀ i, 1 ≤ i → i ≤ n → LevelOK n i := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi hin
    -- `AssertProper(i − 1)` and the lower levels
    have apPrev : APOK n (i - 1) := by
      rcases Nat.eq_or_lt_of_le hi with h | h
      · rw [← h]; exact apOK_zero
      · exact (ih (i - 1) (by omega) (by omega) (by omega)).apOK
    -- `Large(x)` at level `i`
    have hLarge : LargeB n i ∧ ∀ k, Robust n (.large i k) := by
      rcases Nat.eq_or_lt_of_le hi with h | h
      · subst h
        have hB := large_one_B hin
        exact ⟨hB, fun k => robust_of_split (large_robust_ge le_rfl hin hB k)
          (fun j hj _ hji => by omega)⟩
      · have L1 := ih (i - 1) (by omega) (by omega) (by omega)
        have ap2 : APOK n (i - 2) := by
          rcases Nat.lt_or_ge i 3 with h3 | h3
          · rw [show i - 2 = 0 by omega]; exact apOK_zero
          · exact (ih (i - 2) (by omega) (by omega) (by omega)).apOK
        have hB := large_B (by omega) hin ap2.apA L1.zeroB L1.incrA
        refine ⟨hB, fun k => robust_of_split (large_robust_ge hi hin hB k) ?_⟩
        intro j hj hjn hji
        rcases Nat.lt_or_ge j (i - 1) with h' | h'
        · exact large_robust_low (by omega) hin ap2.apR ap2.apB L1.zeroR
            (fun bx by' => L1.incrR bx by') k j hj hjn (by omega)
        · exact large_robust_mid (by omega) hin ap2.apA L1.zeroB L1.zeroC L1.incrB k j hj hjn
            (by omega)
    obtain ⟨hLB, hLR⟩ := hLarge
    have hZB := zero_B hi hin apPrev.apA hLB
    have hZC := zero_C (n := n) i
    have hZR := zero_robust hi hin apPrev.apA apPrev.apB apPrev.apR hLB hLR
    exact {
      largeB := hLB
      largeR := hLR
      apA := ap_A hi hin apPrev.apA hLB
      apB := ap_B hi hin apPrev.apA apPrev.apB hLB
      apC := ap_C hi hin apPrev.apA hLB
      apR := ap_robust hi hin apPrev.apR hLR
      zeroB := hZB
      zeroC := hZC
      zeroR := hZR
      incrA := incr_A hi hin hZB hZC
      incrB := incr_B hi hin hZB hZC
      incrG := incr_G hi hin hZB hZC
      incrR := fun bx by' => incr_robust_lt hi hin hZC hZR bx by' }

end Podc.PPDoubleExpThresholds
