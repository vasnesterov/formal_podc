import Papers.PODC2013.ConstantBarriersMutex.Doorway
import Papers.PODC2013.ConstantBarriersMutex.BoundedWaitingQueue

/-!
# Control flow facts for the liveness proof
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

lemma Inv.exits_le_ent {s : Cfg h} (hI : Inv s) : s.mem.exits ≤ s.ent ∧ s.ent ≤ s.mem.exits + 1 := by
  by_cases h1 : ∃ g, s.pc g = .cs ∨ s.pc g = .x31 ∨ s.pc g = .x32
  · obtain ⟨g, hg⟩ := h1; have := hI.ex1 g hg; omega
  · by_cases h2 : ∃ g v, .exits v ∈ s.buf g
    · obtain ⟨g, v, hv⟩ := h2; have := hI.ex2 g v hv; omega
    · push_neg at h1 h2
      have := hI.ex3 (fun g => ⟨(h1 g).1, (h1 g).2.1, (h1 g).2.2, h2 g⟩); omega

/-- The only way into the entry section is statement 17 from the remainder section; right after
it, no doorway write is performed. -/
lemma next_into_entry {s : Cfg h} (hI : Inv s) (e : Ev h) {p : Proc h} (hE : ¬ (s.pc p).Entry)
    (hE' : ((s.next e).pc p).Entry) : s.pc p = .rem ∧ perf (s.next e) p = 0 := by
  have he : e = .step p := BW.eq_step_of_pc_ne s e (fun h' => hE (h' ▸ hE'))
  subst he
  have hL := hI.loc p
  cases hpc : s.pc p <;> simp only [hpc, PC.Entry, not_true_eq_false] at hE <;>
    simp only [Cfg.next, Cfg.stepProc, hpc] at hE' ⊢
  case rem =>
    unfold LI at hL; rw [hpc] at hL
    refine ⟨by simp, ?_⟩
    unfold perf; simp [Cfg.issue, PC.Door, PC.issued, hL.1]
  case x50 o =>
    exfalso
    rcases BW.barrier_cases s p .rem with ⟨-, hb⟩ | ⟨w, b, -, hb⟩ <;> rw [hb] at hE' <;>
      simp [hpc, PC.Entry] at hE'
  case x35 l cands =>
    exfalso
    rcases cands with _ | ⟨c, rest⟩ <;> simp only at hE' <;> revert hE' <;> split_ifs <;>
      simp [PC.Entry, Cfg.goto]
  case x45 =>
    exfalso; revert hE'; split <;> simp [PC.Entry, Cfg.issue, Cfg.goto]
  all_goals exfalso; revert hE'; (try split_ifs) <;>
    simp [PC.Entry, Cfg.issue, Cfg.goto]

namespace Run

variable (r : Run h) {p : Proc h}

lemma entry_succ {t : ℕ} (hE : ((r.s t).pc p).Entry) :
    ((r.s (t + 1)).pc p).Entry ∨ (r.s (t + 1)).pc p = .cs := by
  by_cases hc : (r.s (t + 1)).pc p = .cs
  · exact Or.inr hc
  · left; rw [r.next_eq] at hc ⊢; exact BW.entry_step (r.inv t) _ hE hc

/-- A process in its entry section that never enters the CS stays in the entry section. -/
lemma entry_forever {T : ℕ} (hE : ((r.s T).pc p).Entry) (hno : ∀ t ≥ T, (r.s t).pc p ≠ .cs) :
    ∀ t ≥ T, ((r.s t).pc p).Entry := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => exact hE
  | succ t ht ih =>
    rcases r.entry_succ ih with h1 | h1
    · exact h1
    · exact absurd h1 (hno _ (by omega))

/-- A process in the entry section at `t₀` that is not in it at `t₁ ≥ t₀` entered the CS in
between. -/
lemma cs_of_leave_entry {t₀ t₁ : ℕ} (h01 : t₀ ≤ t₁) (hE : ((r.s t₀).pc p).Entry)
    (hE' : ¬ ((r.s t₁).pc p).Entry) : ∃ t, t₀ < t ∧ t ≤ t₁ ∧ (r.s t).pc p = .cs := by
  induction t₁, h01 using Nat.le_induction with
  | base => exact absurd hE hE'
  | succ t ht ih =>
    by_cases hEt : ((r.s t).pc p).Entry
    · rcases r.entry_succ hEt with h1 | h1
      · exact absurd h1 hE'
      · exact ⟨t + 1, by omega, le_rfl, h1⟩
    · obtain ⟨t', h1, h2, h3⟩ := ih hEt
      exact ⟨t', h1, by omega, h3⟩

/-- The start of the current passage: a process in its entry section at `T` has been in it since
some `σ ≤ T`, and no doorway write was performed at `σ`. -/
lemma passage_start {T : ℕ} (hE : ((r.s T).pc p).Entry) :
    ∃ σ ≤ T, perf (r.s σ) p = 0 ∧ ∀ t, σ ≤ t → t ≤ T → ((r.s t).pc p).Entry := by
  induction T with
  | zero => rw [r.init] at hE; simp [Cfg.init, PC.Entry] at hE
  | succ T ih =>
    by_cases hEt : ((r.s T).pc p).Entry
    · obtain ⟨σ, h1, h2, h3⟩ := ih hEt
      refine ⟨σ, by omega, h2, fun t ht1 ht2 => ?_⟩
      rcases Nat.lt_or_ge t (T + 1) with hlt | hge
      · exact h3 t ht1 (by omega)
      · rw [show t = T + 1 by omega]; exact hE
    · have hE2 := hE; rw [r.next_eq] at hE2
      obtain ⟨-, h2⟩ := next_into_entry (r.inv T) _ hEt hE2
      refine ⟨T + 1, le_rfl, by rw [r.next_eq]; exact h2, fun t ht1 ht2 => ?_⟩
      rw [show t = T + 1 by omega]; exact hE

end Run

end Podc.ConstantBarriersMutex
