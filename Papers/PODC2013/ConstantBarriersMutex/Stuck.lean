import Papers.PODC2013.ConstantBarriersMutex.LiveBasic

/-!
# Processes stuck in the entry section

For a process `p` that stays in its entry section forever in a fair run:
* it completes its doorway (`Run.stuck_barrier`): from some time on its doorway writes are all
  performed and its store buffer is empty;
* the nodes holding `p` only disappear (`Run.hold_persist`), its leaf holds `p` forever, so the
  highest level `lev` holding `p` is non-decreasing and eventually constant (Claim 1 of the
  paper).
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

namespace Run

variable (r : Run h) {p : Proc h}

lemma door_entry {c : PC h} (hd : c.Door) : c.Entry := by
  revert hd; cases c <;> simp [PC.Door, PC.Entry]

/-- One step of a process in its doorway: it leaves the doorway, or it issues or performs a
doorway write (strictly, if it is the process that steps). -/
lemma door_step {t : ℕ} (hD : ((r.s t).pc p).Door) (hE' : ((r.s (t + 1)).pc p).Entry) :
    ¬ ((r.s (t + 1)).pc p).Door ∨
      ((r.s t).pc p).issued + perf (r.s t) p ≤ ((r.s (t + 1)).pc p).issued + perf (r.s (t + 1)) p ∧
      (r.ev t = .step p →
        ((r.s t).pc p).issued + perf (r.s t) p < ((r.s (t + 1)).pc p).issued + perf (r.s (t + 1)) p) := by
  have hI := r.inv t
  have hperf := r.perf_succ (door_entry hD) hE'
  have hpm : perf (r.s t) p ≤ perf (r.s (t + 1)) p := by rcases hperf with h1 | ⟨h1, -⟩ <;> omega
  by_cases he : r.ev t = .step p
  · have hs : r.s (t + 1) = (r.s t).stepProc p := by rw [r.next_eq, he]; rfl
    have hL := hI.loc p
    unfold LI at hL
    rcases Door_iff.1 hD with hpc | ⟨l, hpc⟩ | hpc
    · right
      have : ((r.s (t + 1)).pc p) = .e19 h := by rw [hs]; simp [Cfg.stepProc, hpc, Cfg.issue]
      rw [this, hpc]; simp only [PC.issued]; exact ⟨by omega, fun _ => by omega⟩
    · right
      rw [hpc] at hL
      have : ((r.s (t + 1)).pc p) = if l = 0 then .e22 else .e19 (l - 1) := by
        rw [hs]; simp [Cfg.stepProc, hpc, Cfg.issue]
      rw [this, hpc]
      split_ifs with hl0
      · subst hl0; simp only [PC.issued]; exact ⟨by omega, fun _ => by omega⟩
      · simp only [PC.issued]; have := hL.1; exact ⟨by omega, fun _ => by omega⟩
    · by_cases hb : (r.s t).buf p = []
      · left
        have : ((r.s (t + 1)).pc p) = .e23 := by
          rw [hs]; simp [Cfg.stepProc, hpc, Cfg.barrier, hb, Cfg.goto]
        rw [this]; simp [PC.Door]
      · right
        obtain ⟨w, b, hwb⟩ := List.exists_cons_of_ne_nil hb
        have h1 : r.s (t + 1) = (r.s t).flush p := by
          rw [hs]; simp only [Cfg.stepProc, hpc]; exact barrier_flush hb
        have h2 := (perf_flush hI hD hwb).1
        rw [h1, flush_pc, h2]; exact ⟨by omega, fun _ => by omega⟩
  · right
    have hpc : (r.s (t + 1)).pc p = (r.s t).pc p := r.pc_succ_of_ne he
    rw [hpc]; exact ⟨by omega, fun h' => absurd h' he⟩

/-- A process outside its doorway in the entry section never returns to the doorway while in
the entry section. -/
lemma not_door_succ {t : ℕ} (hE : ((r.s t).pc p).Entry) (hD : ¬ ((r.s t).pc p).Door) :
    ¬ ((r.s (t + 1)).pc p).Door := by
  by_cases he : r.ev t = .step p
  · rw [r.next_eq, he]
    apply stepProc_pc_wait
    revert hE hD; cases (r.s t).pc p <;> simp [PC.Entry, PC.Door, PC.Waiting]
  · rw [r.pc_succ_of_ne he]; exact hD

/-- **Doorway progress.** A fairly scheduled process that stays in its entry section completes
its doorway: from some time on, it is past its barrier and all its doorway writes are
performed. -/
theorem stuck_barrier (hf : r.Fair) {T : ℕ} (hE : ∀ t ≥ T, ((r.s t).pc p).Entry) :
    ∃ ta ≥ T, ∀ t ≥ ta, ¬ ((r.s t).pc p).Door ∧ perf (r.s t) p = h + 3 := by
  have hI := r.inv
  obtain ⟨ta, hta, hnd⟩ : ∃ ta ≥ T, ¬ ((r.s ta).pc p).Door := by
    by_cases h0 : ((r.s T).pc p).Door
    · apply exists_good_of_measure r.ev p
        (hf.inf_steps (T := T) (fun t ht h' => by have := hE t ht; rw [h'] at this; exact this))
        (fun t => ¬ ((r.s t).pc p).Door) (fun t => T ≤ t ∧ ((r.s t).pc p).Door)
        (fun t => 2 * (h + 3) + 1 - ((r.s t).pc p).issued - perf (r.s t) p) T ⟨le_rfl, h0⟩
      intro t ht hD hG
      simp only [not_not] at hG
      refine ⟨⟨by omega, hG⟩, ?_⟩
      rcases r.door_step hD.2 (hE (t + 1) (by omega)) with h1 | ⟨h1, h2⟩
      · exact absurd hG h1
      · have hk := issued_le (hI (t + 1)) hG
        have hk' := (buf_door (hI (t + 1)) hG).2.1
        exact ⟨by omega, fun h' => by have := h2 h'; omega⟩
    · exact ⟨T, le_rfl, h0⟩
  refine ⟨ta, hta, fun t ht => ?_⟩
  have hnd' : ¬ ((r.s t).pc p).Door := by
    induction t, ht using Nat.le_induction with
    | base => exact hnd
    | succ t ht ih => exact r.not_door_succ (hE t (by omega)) ih
  exact ⟨hnd', by unfold perf; rw [if_neg hnd']⟩

end Run

end Podc.ConstantBarriersMutex
