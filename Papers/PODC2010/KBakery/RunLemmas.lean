import Papers.PODC2010.KBakery.Invariant

/-!
# Elementary facts about executions
-/

set_option linter.unusedSectionVars false

namespace Podc.KBakery

open Finset

variable {P : Type} [LinearOrder P] [Fintype P]
variable {fife : Bool} {k : ℕ}

namespace Run

variable (r : Run fife k P)

lemma pc_succ_of_ne {t : ℕ} {q : P} (h : r.sched t ≠ q) : (r.s (t + 1)).pc q = (r.s t).pc q := by
  rw [r.step t, stepAt_pc, core_pc_ne (Ne.symm h)]

lemma ticket_succ_of_ne {t : ℕ} {q : P} (h : r.sched t ≠ q) :
    (r.s (t + 1)).ticket q = (r.s t).ticket q := by
  rw [r.step t, stepAt_ticket, core_ticket_ne (Ne.symm h)]

lemma want_succ_of_ne {t : ℕ} {q : P} (h : r.sched t ≠ q) :
    (r.s (t + 1)).want q = (r.s t).want q := by
  rw [r.step t, stepAt_want, core_want_ne (Ne.symm h)]

lemma capture_succ_of_ne {t : ℕ} {q : P} (h : r.sched t ≠ q) :
    (r.s (t + 1)).capture q = (r.s t).capture q := by
  rw [r.step t, stepAt_capture, core_capture_ne (Ne.symm h)]

lemma ticket_le_succ (t : ℕ) (q : P) : (r.s t).ticket q ≤ (r.s (t + 1)).ticket q := by
  rw [r.step t]; exact ticket_mono (r.inv t) (r.adm t) q

lemma ticket_mono {t t' : ℕ} (h : t ≤ t') (q : P) : (r.s t).ticket q ≤ (r.s t').ticket q := by
  induction h with
  | refl => rfl
  | step _ ih => exact ih.trans (r.ticket_le_succ _ q)

/-- Tickets change only at line 15. -/
lemma ticket_succ_of_not_d15 {t : ℕ} {q : P} (h : ∀ acc rem, (r.s t).pc q ≠ .d15 acc rem) :
    (r.s (t + 1)).ticket q = (r.s t).ticket q := by
  by_cases hq : r.sched t = q
  · rw [r.step t, stepAt_ticket, hq, core_ticket_self_of_ne_d15 h]
  · exact r.ticket_succ_of_ne hq

/-- A process in the waiting room stays there or enters the CS. -/
lemma waiting_succ {t : ℕ} {q : P} (h : ((r.s t).pc q).InWaiting) :
    ((r.s (t + 1)).pc q).InWaiting ∨ (r.s (t + 1)).pc q = .cs := by
  by_cases hq : r.sched t = q
  · rw [r.step t, stepAt_pc, hq]
    rcases hpc : (r.s t).pc q with _ | rem' | ⟨acc', rem'⟩ | rem' | ⟨pred, cap⟩ | ⟨pred, rem'⟩ |
      ⟨pred, rem', cap⟩ | rem' | _ | rem' <;> simp only [hpc, PC.InWaiting] at h <;>
      simp only [core, hpc] <;> (try split_ifs) <;> (try cases fife) <;> simp [PC.InWaiting]
  · rw [r.pc_succ_of_ne hq]; exact Or.inl h

lemma not_d15_of_waiting {c : PC P} (h : c.InWaiting) : ∀ acc rem, c ≠ .d15 acc rem := by
  intro acc rem hc; subst hc; simp [PC.InWaiting] at h

lemma post15_of_waiting {c : PC P} (h : c.InWaiting) : c.Post15 := by
  cases c <;> simp_all [PC.InWaiting, PC.Post15]

/-- In the waiting room the ticket is fixed, until the CS. -/
lemma waiting_interval {t₀ t₁ : ℕ} {q : P} (h₀ : ((r.s t₀).pc q).InWaiting)
    (hcs : ∀ t, t₀ ≤ t → t ≤ t₁ → (r.s t).pc q ≠ .cs) :
    ∀ t, t₀ ≤ t → t ≤ t₁ → ((r.s t).pc q).InWaiting ∧ (r.s t).ticket q = (r.s t₀).ticket q := by
  intro t h0 h1
  induction t, h0 using Nat.le_induction with
  | base => exact ⟨h₀, rfl⟩
  | succ t ht ih =>
    obtain ⟨hw, htk⟩ := ih (by omega)
    refine ⟨?_, ?_⟩
    · rcases r.waiting_succ hw with h | h
      · exact h
      · exact absurd h (hcs (t + 1) (by omega) h1)
    · rw [r.ticket_succ_of_not_d15 (not_d15_of_waiting hw), htk]

end Run

end Podc.KBakery
