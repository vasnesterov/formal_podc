import Papers.PODC2010.GroupMutexLogRMR.InvLemmas

/-!
# Bounded exit (P3)

The exit section (lines 13–16.14) has no waiting: every step of `p` there moves `p` forward in the
code or back to the remainder section, and steps of other processes do not change `p`'s local
state. Hence `p` returns to the remainder section within 17 of its own steps.
-/

namespace Podc.GroupMutexLogRMR

variable {n : ℕ} {J : Type} [DecidableEq J]

/-- A step of `p` in the exit section moves it forward or to the remainder section. -/
theorem exit_progress (c : Cfg n J) (p : Fin n) (σ : J) (h : PC.btw .l13 .l16_14 (c.loc p).pc) :
    ((c.step p σ).loc p).pc = .rem ∨ (c.loc p).pc.idx < ((c.step p σ).loc p).pc.idx := by
  unfold PC.btw at h
  cases hpc : (c.loc p).pc <;> rw [hpc] at h <;> simp only [PC.idx] at h <;> try omega
  all_goals
    simp only [Cfg.step, hpc]
    repeat' first
      | split
      | (simp [Cfg.go, Cfg.setLoc, Cfg.incC, Cfg.decC, Cfg.llS, Cfg.llEx, Cfg.scS, Cfg.scEx, Cfg.setOut,
          Cfg.setExclear, PC.idx])

/-- Steps of other processes do not change `p`'s local state. -/
theorem step_loc_other (c : Cfg n J) (p q : Fin n) (σ : J) (hq : q ≠ p) :
    (c.step q σ).loc p = c.loc p := by
  simp only [Cfg.step]
  repeat' first
    | split
    | (simp [Cfg.go, Cfg.setLoc, Cfg.incC, Cfg.decC, Cfg.llS, Cfg.llEx, Cfg.scS, Cfg.scEx, Cfg.setOut,
        Cfg.setExclear, Function.update_of_ne hq.symm])

theorem PC.idx_l13 : PC.l13.idx = 24 := rfl
theorem PC.idx_l16_14 : PC.l16_14.idx = 40 := rfl

theorem bounded_exit_aux (p : Fin n) (es : List (Ev n J)) : ∀ c : Cfg n J,
    PC.btw .l13 .l16_14 (c.loc p).pc → 41 - (c.loc p).pc.idx ≤ (es.filter (fun e => e.1 = p)).length →
    ∃ es₁ es₂, es = es₁ ++ es₂ ∧ ((run c es₁).loc p).pc = .rem := by
  induction es with
  | nil => intro c h hk; simp at hk; unfold PC.btw at h; rw [PC.idx_l13, PC.idx_l16_14] at h; omega
  | cons e es ih =>
    intro c h hk
    by_cases hep : e.1 = p
    · have hk' : 41 - (c.loc p).pc.idx ≤ (es.filter (fun e => e.1 = p)).length + 1 := by
        simpa [List.filter_cons, hep] using hk
      have hpr := exit_progress c p e.2 h
      rw [← hep] at hpr
      rcases hpr with hpr | hpr
      · exact ⟨[e], es, rfl, by simpa [run, ← hep] using hpr⟩
      · rw [hep] at hpr
        by_cases hr : ((c.step e.1 e.2).loc p).pc = .rem
        · exact ⟨[e], es, rfl, by simpa [run] using hr⟩
        have hle : ((c.step e.1 e.2).loc p).pc.idx ≤ 40 := by
          cases ((c.step e.1 e.2).loc p).pc <;> simp [PC.idx]
        rw [hep] at hle hr
        obtain ⟨es₁, es₂, h1, h2⟩ := ih (c.step p e.2)
          (by unfold PC.btw at h ⊢; rw [PC.idx_l13, PC.idx_l16_14] at h ⊢; omega)
          (by omega)
        refine ⟨e :: es₁, es₂, by rw [h1]; rfl, ?_⟩
        rw [show e = (p, e.2) from Prod.ext hep rfl]
        exact h2
    · have hk' : 41 - (c.loc p).pc.idx ≤ (es.filter (fun e => e.1 = p)).length := by
        simpa [List.filter_cons, hep] using hk
      have hloc := step_loc_other c p e.1 e.2 hep
      obtain ⟨es₁, es₂, h1, h2⟩ := ih (c.step e.1 e.2) (by rw [hloc]; exact h) (by rw [hloc]; exact hk')
      exact ⟨e :: es₁, es₂, by rw [h1]; rfl, h2⟩

/-- **(P3) Bounded exit**: a process in the exit section that takes 17 steps (whatever the other
processes do in between) has been back in the remainder section. -/
theorem bounded_exit (c : Cfg n J) (p : Fin n) (es : List (Ev n J))
    (h : PC.btw .l13 .l16_14 (c.loc p).pc) (hk : 17 ≤ (es.filter (fun e => e.1 = p)).length) :
    ∃ es₁ es₂, es = es₁ ++ es₂ ∧ ((run c es₁).loc p).pc = .rem :=
  bounded_exit_aux p es c h (by unfold PC.btw at h; rw [PC.idx_l13, PC.idx_l16_14] at h; omega)

end Podc.GroupMutexLogRMR
