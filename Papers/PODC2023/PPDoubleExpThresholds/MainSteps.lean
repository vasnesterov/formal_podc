import Papers.PODC2023.PPDoubleExpThresholds.MainAux

/-!
# The abstract steps of `Main`
-/

namespace Podc.PPDoubleExpThresholds

open Program

variable {n : ℕ}

section instrs

variable {j : ℕ} (hj : 1 ≤ j) (hjn : j ≤ n)
include hj hjn

theorem instr_it0 : (prog n).instr .main (5 * j - 4) =
    some (.call (.large j 1) (5 * j - 3) (5 * j - 2)) := by
  have := instr_main_it n hj hjn (r := 0) (by omega)
  simp only [Nat.add_zero] at this; rw [this]; simp [itCode]; omega

theorem instr_it1 : (prog n).instr .main (5 * j - 3) =
    some (.call (.large j 3) (5 * j + 1) (5 * j - 2)) := by
  have := instr_main_it n hj hjn (r := 1) (by omega)
  rw [show 5 * j - 4 + 1 = 5 * j - 3 by omega] at this; rw [this]; simp [itCode]; omega

theorem instr_it2 : (prog n).instr .main (5 * j - 2) =
    some (.call (.assertProper j) (5 * j - 1) (5 * j - 1)) := by
  have := instr_main_it n hj hjn (r := 2) (by omega)
  rw [show 5 * j - 4 + 2 = 5 * j - 2 by omega] at this; rw [this]; simp [itCode]; omega

theorem instr_it3 : (prog n).instr .main (5 * j - 1) =
    some (.call (.assertEmpty (j + 1)) (5 * j) (5 * j)) := by
  have := instr_main_it n hj hjn (r := 3) (by omega)
  rw [show 5 * j - 4 + 3 = 5 * j - 1 by omega] at this; rw [this]; simp [itCode]; omega

theorem instr_it4 : (prog n).instr .main (5 * j) = some (.goto (5 * j - 4)) := by
  have := instr_main_it n hj hjn (r := 4) (by omega)
  rw [show 5 * j - 4 + 4 = 5 * j by omega] at this; rw [this]; simp [itCode]

end instrs

theorem instr_fin0 : (prog n).instr .main (5 * n + 1) = some (.setOF true) := by
  have := instr_main_fin (n := n) (r := 0) (by omega); simpa using this

theorem instr_fin1 : (prog n).instr .main (5 * n + 2) = some (.goto (5 * n + 3)) := by
  have := instr_main_fin (n := n) (r := 1) (by omega); simpa using this

theorem instr_fin2 : (prog n).instr .main (5 * n + 3) =
    some (.call (.assertProper n) (5 * n + 4) (5 * n + 4)) := by
  have := instr_main_fin (n := n) (r := 2) (by omega); simpa using this

theorem instr_fin3 : (prog n).instr .main (5 * n + 4) = some (.goto (5 * n + 2)) := by
  have := instr_main_fin (n := n) (r := 3) (by omega); simpa using this

theorem instr_fin4 : (prog n).instr .main (5 * n + 5) = some (.ret false) := by
  have := instr_main_fin (n := n) (r := 4) (by omega); simpa using this

/-- The positions in `Main`: `pc = 0`, inside the loop of level `j`, or after the loops. -/
theorem main_pc_cases (pc : ℕ) : pc = 0 ∨ (∃ j r, 1 ≤ j ∧ j ≤ n ∧ r < 5 ∧ pc = 5 * j - 4 + r) ∨
    5 * n + 1 ≤ pc := by
  rcases Nat.eq_zero_or_pos pc with h | h
  · exact .inl h
  · rcases Nat.lt_or_ge pc (5 * n + 1) with h' | h'
    · refine .inr (.inl ⟨(pc + 4) / 5, (pc + 4) % 5, by omega, by omega, by omega, by omega⟩)
    · exact .inr (.inr h')

/-- **The abstract steps of `Main`.** -/
theorem main_astep {pc : ℕ} {D : Reg n → ℕ} {OF : Bool} {a' : Loc (Reg n)}
    (hs : (prog n).AStep .main ⟨pc, D, OF⟩ a') :
    (pc = 0 ∧ a' = ⟨1, D, false⟩) ∨
    (∃ j, 1 ≤ j ∧ j ≤ n ∧
      ((pc = 5 * j - 4 ∧ ∃ D' OF' b, (prog n).Returns (.large j 1) D OF D' OF' b ∧
          a' = ⟨cond b (5 * j - 3) (5 * j - 2), D', OF'⟩) ∨
       (pc = 5 * j - 3 ∧ ∃ D' OF' b, (prog n).Returns (.large j 3) D OF D' OF' b ∧
          a' = ⟨cond b (5 * j + 1) (5 * j - 2), D', OF'⟩) ∨
       (pc = 5 * j - 2 ∧ ∃ D' OF' b, (prog n).Returns (.assertProper j) D OF D' OF' b ∧
          a' = ⟨5 * j - 1, D', OF'⟩) ∨
       (pc = 5 * j - 1 ∧ ∃ D' OF' b, (prog n).Returns (.assertEmpty (j + 1)) D OF D' OF' b ∧
          a' = ⟨5 * j, D', OF'⟩) ∨
       (pc = 5 * j ∧ a' = ⟨5 * j - 4, D, OF⟩))) ∨
    (pc = 5 * n + 1 ∧ a' = ⟨5 * n + 2, D, true⟩) ∨
    (pc = 5 * n + 2 ∧ a' = ⟨5 * n + 3, D, OF⟩) ∨
    (pc = 5 * n + 3 ∧ ∃ D' OF' b, (prog n).Returns (.assertProper n) D OF D' OF' b ∧
      a' = ⟨5 * n + 4, D', OF'⟩) ∨
    (pc = 5 * n + 4 ∧ a' = ⟨5 * n + 2, D, OF⟩) := by
  rw [astep_iff] at hs
  rcases main_pc_cases (n := n) pc with rfl | ⟨j, r, hj, hjn, hr, rfl⟩ | h
  · rw [instr_main_zero] at hs; exact .inl ⟨rfl, hs⟩
  · refine .inr (.inl ⟨j, hj, hjn, ?_⟩)
    interval_cases r
    · rw [Nat.add_zero, instr_it0 hj hjn] at hs; exact .inl ⟨by omega, hs⟩
    · rw [show 5 * j - 4 + 1 = 5 * j - 3 by omega, instr_it1 hj hjn] at hs
      exact .inr (.inl ⟨by omega, hs⟩)
    · rw [show 5 * j - 4 + 2 = 5 * j - 2 by omega, instr_it2 hj hjn] at hs
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      exact .inr (.inr (.inl ⟨by omega, D', OF', b, hr, by simp⟩))
    · rw [show 5 * j - 4 + 3 = 5 * j - 1 by omega, instr_it3 hj hjn] at hs
      obtain ⟨D', OF', b, hr, rfl⟩ := hs
      exact .inr (.inr (.inr (.inl ⟨by omega, D', OF', b, hr, by simp⟩)))
    · rw [show 5 * j - 4 + 4 = 5 * j by omega, instr_it4 hj hjn] at hs
      exact .inr (.inr (.inr (.inr ⟨by omega, hs⟩)))
  · obtain ⟨r, rfl⟩ : ∃ r, pc = 5 * n + 1 + r := ⟨pc - (5 * n + 1), by omega⟩
    rcases Nat.lt_or_ge r 5 with hr | hr
    · interval_cases r
      · rw [Nat.add_zero, instr_fin0] at hs; exact .inr (.inr (.inl ⟨rfl, hs⟩))
      · rw [show 5 * n + 1 + 1 = 5 * n + 2 by omega, instr_fin1] at hs
        exact .inr (.inr (.inr (.inl ⟨rfl, hs⟩)))
      · rw [show 5 * n + 1 + 2 = 5 * n + 3 by omega, instr_fin2] at hs
        obtain ⟨D', OF', b, hr, rfl⟩ := hs
        exact .inr (.inr (.inr (.inr (.inl ⟨rfl, D', OF', b, hr, by simp⟩))))
      · rw [show 5 * n + 1 + 3 = 5 * n + 4 by omega, instr_fin3] at hs
        exact .inr (.inr (.inr (.inr (.inr ⟨rfl, hs⟩))))
      · rw [show 5 * n + 1 + 4 = 5 * n + 5 by omega, instr_fin4] at hs; exact hs.elim
    · rw [instr_main_none n (by omega)] at hs; exact hs.elim

end Podc.PPDoubleExpThresholds
