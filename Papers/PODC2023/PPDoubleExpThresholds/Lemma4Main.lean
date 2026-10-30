import Papers.PODC2023.PPDoubleExpThresholds.Lemma4c

/-!
# Lemma 4(c)
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

/-- The "good" register configurations of Lemma 4: `n`-proper, or `j`-low and `(j+1)`-empty. -/
def Good (n : ℕ) (C : Reg n → ℕ) : Prop :=
  Proper C n ∨ ∃ J, 1 ≤ J ∧ J ≤ n ∧ Low C J ∧ Empty C (J + 1)

theorem not_proper_succ (C : Reg n → ℕ) : ¬ Proper C (n + 1) := by
  intro h
  obtain ⟨-, -, h1, -, -⟩ := (proper_succ_iff (by omega)).1 h
  have hR0 := ((proper_succ_iff (C := C) (i := n + 1) (by omega)).1 h).2.1
  have : reg n (n + 1) 0 = reg n (n + 1) 1 := by simp [reg]
  rw [this] at hR0
  have := N_pos (i := n + 1) (by omega)
  omega

/-- **Lemma 4(c)**: on a configuration that is not good, `Main` always restarts. -/
theorem lemma_4c {C : Reg n → ℕ} (hC : ¬ Good n C) (OF₀ : Bool) :
    ∀ s, (prog n).Reach₀ ((prog n).init C OF₀) s → (prog n).CanRestart s := by
  classical
  have hex : ∃ j, ¬ Proper C j := ⟨n + 1, not_proper_succ C⟩
  set J := Nat.find hex with hJdef
  have hnJ : ¬ Proper C J := Nat.find_spec hex
  have hJ1 : 1 ≤ J := by
    by_contra h
    apply hnJ
    rw [show J = 0 by omega]
    intro l hl hl0; omega
  have hPJ : Proper C (J - 1) := by
    by_contra h; exact Nat.find_min hex (by omega : J - 1 < J) h
  have hJn : J ≤ n := by
    by_contra h
    apply hC
    exact .inl (hPJ.mono (by omega))
  by_cases hL : Low C J
  · refine lemma_4c_case1 hJ1 hJn hL (fun hE => hC (.inr ⟨J, hJ1, hJn, hL, hE⟩)) OF₀
  by_cases hH : High C J
  · exact lemma_4c_high hJ1 hJn hH OF₀
  -- case 2
  have hsum : psum C J 0 < N J ∨ psum C J 2 < N J := by
    by_contra h
    push Not at h
    exact hH ⟨hPJ, hnJ, h.1, h.2⟩
  have hbad : Bad C J := by
    unfold Bad
    by_contra h
    push Not at h
    exact hL ⟨hPJ, hnJ, by omega, by omega, h.1.2, h.2.2⟩
  rcases hsum with h0 | h2
  · exact lemma_4c_case2 hJ1 hJn (k₀ := 0) (.inl rfl)
      ⟨hPJ, by simp only [psum, bar] at h0; show C (reg n J 1) < N J; omega, hbad⟩ OF₀
  · exact lemma_4c_case2 hJ1 hJn (k₀ := 2) (.inr rfl)
      ⟨hPJ, by simp only [psum, bar] at h2; show C (reg n J 3) < N J; omega, hbad⟩ OF₀

end Podc.PPDoubleExpThresholds
