import Papers.PODC2013.ConstantBarriersMutex.Progress
import Papers.PODC2013.ConstantBarriersMutex.Stuck

/-!
# The waiting section (statements 23–27) guarantees an exit after the barrier

The key use of statement 25 (`await exits − e ≥ 2 ∨ lock ∈ {p, −1}`): a process that completes
its barrier (statement 22) at time `ta` and never enters the critical section afterwards forces
some process to enter the critical section after `ta` (`Run.waiting_entry`). Without the
`exits − e ≥ 2` disjunct the process could wait at statement 27 although the lock owner read the
tree before `ta`.
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

namespace Run

variable (r : Run h) {p : Proc h}

/-- Program counters of a process that has completed its barrier at `ta` while no process
entered the critical section since `ta` and the lock is never handed to it. -/
def WaitOK (ta t : ℕ) (p : Proc h) : Prop :=
  match (r.s t).pc p with
  | .e23 | .e24 => True
  | .e25a e | .e25b e => (r.s ta).ent ≤ e + 1
  | .e26 => (r.s t).mem.lock = none
  | _ => False

/-- Measure for the waiting section when the lock is free. -/
def waitμ : PC h → ℕ
  | .e23 => 1
  | .e24 => 4
  | .e25a _ => 3
  | .e25b _ => 2
  | .e26 => 1
  | _ => 0

lemma waitOK_buf {ta t : ℕ} (hw : r.WaitOK ta t p) : (r.s t).buf p = [] := by
  have hL := (r.inv t).loc p
  unfold WaitOK at hw; unfold LI at hL
  cases hpc : (r.s t).pc p <;> simp only [hpc] at hw hL <;> first | exact hL.1 | exact hw.elim

lemma waitOK_cases {ta t : ℕ} (hw : r.WaitOK ta t p) :
    (r.s t).pc p = .e23 ∨ (r.s t).pc p = .e24 ∨
      (∃ e, (r.s t).pc p = .e25a e ∧ (r.s ta).ent ≤ e + 1) ∨
      (∃ e, (r.s t).pc p = .e25b e ∧ (r.s ta).ent ≤ e + 1) ∨
      ((r.s t).pc p = .e26 ∧ (r.s t).mem.lock = none) := by
  unfold WaitOK at hw
  cases hpc : (r.s t).pc p <;> simp only [hpc] at hw <;> first | exact hw.elim | simp [hw]

/-- **Statement 25 at work.** A process that completes its barrier at `ta` and never enters the
critical section afterwards: some process enters the critical section after `ta`. -/
theorem waiting_entry (hf : r.Fair) {ta : ℕ} (hpc : (r.s ta).pc p = .e23)
    (hno : ∀ t ≥ ta, (r.s t).pc p ≠ .cs) : ∃ t ≥ ta, (r.s (t + 1)).ent = (r.s t).ent + 1 := by
  by_contra hG
  push_neg at hG
  have hG' : ∀ t ≥ ta, (r.s (t + 1)).ent = (r.s t).ent := fun t ht => by
    rcases r.ent_succ t with h1 | h1
    · exact h1
    · exact absurd h1 (hG t ht)
  have hentc : ∀ t ≥ ta, (r.s t).ent = (r.s ta).ent := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => rfl
    | succ t ht ih => rw [hG' t ht, ih]
  have hE : ∀ t ≥ ta, ((r.s t).pc p).Entry := r.entry_forever (by rw [hpc]; simp [PC.Entry]) hno
  -- the lock is never handed to `p`
  have hnl : ∀ t ≥ ta, (r.s t).mem.lock ≠ some p := by
    intro t ht hl
    obtain ⟨t', ht', hcs⟩ := r.handed_enters hf hl (hE t ht)
    exact hno t' (by omega) hcs
  -- the invariant of the waiting section
  have hok : ∀ t ≥ ta, r.WaitOK ta t p := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => unfold WaitOK; rw [hpc]; trivial
    | succ t ht ih =>
      have hb := r.waitOK_buf ih
      have hI := r.inv t
      have hex := hI.exits_le_ent
      have hent := hentc t ht
      by_cases he : r.ev t = .step p
      · have hs : r.s (t + 1) = (r.s t).stepProc p := by rw [r.next_eq, he]; rfl
        have hcs := hno (t + 1) (by omega)
        rw [hs] at hcs
        unfold WaitOK; rw [hs]
        rcases r.waitOK_cases ih with hpc' | hpc' | ⟨e, hpc', h1⟩ | ⟨e, hpc', h1⟩ | ⟨hpc', h1⟩
        · simp only [Cfg.stepProc, hpc', Cfg.cas, hb, Mem.view_nil] at hcs ⊢
          split_ifs at hcs ⊢ <;> simp_all
        · simp [Cfg.stepProc, hpc', Cfg.goto, Cfg.view, hb]; omega
        · simp only [Cfg.stepProc, hpc', Cfg.goto, Cfg.view, hb, Mem.view_nil]
          split_ifs with h2
          · exfalso; omega
          · simp [h1]
        · simp only [Cfg.stepProc, hpc', Cfg.goto, Cfg.view, hb, Mem.view_nil]
          split_ifs with h2
          · simp only [Function.update_self]
            rcases h2 with h2 | h2
            · exact absurd h2 (hnl t ht)
            · exact h2
          · simp [h1]
        · simp [Cfg.stepProc, hpc', Cfg.cas, hb, h1] at hcs
      · have hpc2 : (r.s (t + 1)).pc p = (r.s t).pc p := r.pc_succ_of_ne he
        unfold WaitOK at ih ⊢
        rw [hpc2]
        revert ih; cases (r.s t).pc p <;> simp only [imp_self, IsEmpty.forall_iff]
        intro h1
        rcases r.lock_none_succ h1 with h2 | h2
        · exact h2
        · exact absurd h2 (hG t ht)
  -- the lock eventually stays free
  obtain ⟨T', hT', hfree⟩ := r.lock_none_of_no_entry hf (T := ta) hG'
  obtain ⟨t, ht, hcs⟩ := exists_good_of_measure r.ev p
    (hf.inf_steps (T := ta) (fun t ht h' => by have := hE t ht; rw [h'] at this; exact this))
    (fun t => (r.s t).pc p = .cs) (fun t => T' ≤ t) (fun t => waitμ ((r.s t).pc p)) T' le_rfl
    (fun t ht _ hG2 => by
      refine ⟨by omega, ?_⟩
      have ih := hok t (by omega)
      have hb := r.waitOK_buf ih
      have hfr := hfree t ht
      by_cases he : r.ev t = .step p
      · have hs : r.s (t + 1) = (r.s t).stepProc p := by rw [r.next_eq, he]; rfl
        rw [hs] at hG2 ⊢
        rcases r.waitOK_cases ih with hpc' | hpc' | ⟨e, hpc', h1⟩ | ⟨e, hpc', h1⟩ | ⟨hpc', h1⟩
        · simp [Cfg.stepProc, hpc', Cfg.cas, hb, hfr] at hG2
        · simp [Cfg.stepProc, hpc', Cfg.goto, waitμ]
        · have hex := (r.inv t).exits_le_ent
          have := hentc t (by omega)
          simp only [Cfg.stepProc, hpc', Cfg.goto, Cfg.view, hb, Mem.view_nil]
          split_ifs with h2
          · exfalso; omega
          · simp [waitμ]
        · simp [Cfg.stepProc, hpc', Cfg.goto, Cfg.view, hb, hfr, waitμ]
        · simp [Cfg.stepProc, hpc', Cfg.cas, hb, hfr] at hG2
      · rw [r.pc_succ_of_ne he]; exact ⟨le_rfl, fun h' => absurd h' he⟩)
  exact hno t (by omega) hcs

end Run

end Podc.ConstantBarriersMutex
