import Papers.PODC2013.ConstantBarriersMutex.Safety

/-!
# Basic facts about executions (runs)
-/

namespace Podc.ConstantBarriersMutex

variable {h : ℕ}

namespace Run

variable (r : Run h)

lemma next_eq (t : ℕ) : r.s (t + 1) = (r.s t).next (r.ev t) := r.step t

/-- A step of `p` only changes the program counter of `p`. -/
lemma stepProc_pc_ne (s : Cfg h) {p q : Proc h} (hq : q ≠ p) : (s.stepProc p).pc q = s.pc q := by
  unfold Cfg.stepProc
  split <;> (try split) <;> (try split) <;>
    simp [Cfg.issue, Cfg.goto, Cfg.cas, Cfg.barrier, Cfg.flush, Function.update_of_ne hq] <;>
    (try split) <;> (try split) <;> simp [Function.update_of_ne hq]

/-- A step of `p` only changes the store buffer of `p`. -/
lemma stepProc_buf_ne (s : Cfg h) {p q : Proc h} (hq : q ≠ p) :
    (s.stepProc p).buf q = s.buf q := by
  unfold Cfg.stepProc
  split <;> (try split) <;> (try split) <;>
    simp [Cfg.issue, Cfg.goto, Cfg.cas, Cfg.barrier, Cfg.flush, Function.update_of_ne hq] <;>
    (try split) <;> (try split) <;> simp [Function.update_of_ne hq]

lemma flush_buf_ne' (s : Cfg h) {p q : Proc h} (hq : q ≠ p) : (s.flush p).buf q = s.buf q := by
  unfold Cfg.flush; split <;> simp [Function.update_of_ne hq]

/-- The program counter of `q` changes only at steps of `q`. -/
lemma pc_succ_of_ne {t : ℕ} {q : Proc h} (h' : r.ev t ≠ .step q) :
    (r.s (t + 1)).pc q = (r.s t).pc q := by
  rw [r.next_eq]
  rcases he : r.ev t with p | p
  · have hqp : q ≠ p := by rintro rfl; exact h' he
    exact stepProc_pc_ne _ hqp
  · simp [Cfg.next]

/-- The store buffer of `q` changes only at events of `q`. -/
lemma buf_succ_of_ne {t : ℕ} {q : Proc h} (h1 : r.ev t ≠ .step q) (h2 : r.ev t ≠ .flush q) :
    (r.s (t + 1)).buf q = (r.s t).buf q := by
  rw [r.next_eq]
  rcases he : r.ev t with p | p
  · have hqp : q ≠ p := by rintro rfl; exact h1 he
    exact stepProc_buf_ne _ hqp
  · have hqp : q ≠ p := by rintro rfl; exact h2 he
    exact flush_buf_ne' _ hqp

/-- The ghost counter of CS entries is monotone and increases by at most one. -/
lemma ent_succ (t : ℕ) : (r.s (t + 1)).ent = (r.s t).ent ∨ (r.s (t + 1)).ent = (r.s t).ent + 1 := by
  rw [r.next_eq]
  rcases r.ev t with p | p
  · simp only [Cfg.next, Cfg.stepProc]
    split <;> (try split) <;> (try split) <;>
      simp [Cfg.issue, Cfg.goto, Cfg.cas, Cfg.barrier, Cfg.flush] <;>
      (try split) <;> (try split) <;> simp
  · simp [Cfg.next]

lemma ent_mono {t t' : ℕ} (h' : t ≤ t') : (r.s t).ent ≤ (r.s t').ent := by
  induction t', h' using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih => rcases r.ent_succ m with h1 | h1 <;> omega

/-- An increase of the ghost counter is a CS entry. -/
lemma ent_succ_entry {t : ℕ} (h' : (r.s (t + 1)).ent = (r.s t).ent + 1) :
    ∃ p, (r.s t).pc p ≠ .cs ∧ (r.s (t + 1)).pc p = .cs := by
  rw [r.next_eq] at h' ⊢
  rcases he : r.ev t with p | p <;> rw [he] at h'
  · refine ⟨p, ?_, ?_⟩ <;> revert h' <;> simp only [Cfg.next, Cfg.stepProc] <;>
      cases hp : (r.s t).pc p <;>
      simp [Cfg.issue, Cfg.goto, Cfg.cas, Cfg.barrier, Cfg.flush, hp] <;>
      (try split) <;> (try split) <;> simp_all
  · simp [Cfg.next] at h'

/-- Steps other than barriers and CASes do not change memory. -/
lemma stepProc_mem (s : Cfg h) (p : Proc h) (h1 : s.pc p ≠ .e22) (h2 : s.pc p ≠ .e23)
    (h3 : s.pc p ≠ .e26) (h4 : ∀ o, s.pc p ≠ .x50 o) : (s.stepProc p).mem = s.mem := by
  unfold Cfg.stepProc
  cases hp : s.pc p <;> simp_all [Cfg.issue, Cfg.goto] <;> (try split) <;> (try split) <;>
    (try simp) <;> (try simp_all)

/-- `lock` leaves `−1` only by a successful CAS, which is a CS entry. -/
lemma lock_none_succ {t : ℕ} (hn : (r.s t).mem.lock = none) :
    (r.s (t + 1)).mem.lock = none ∨ (r.s (t + 1)).ent = (r.s t).ent + 1 := by
  have hI := r.inv t
  have hnh : ∀ p, ¬ Holds (r.s t) p := fun p hh => by rw [hI.holds_lock hh] at hn; cases hn
  have hflush : ∀ p, ((r.s t).flush p).mem.lock = none := by
    intro p
    unfold Cfg.flush; split
    · exact hn
    · rename_i w b hwb
      have := (hI.nonholder_buf (hnh p) w (by simp [hwb])).lock
      cases w <;> simp_all [W.isLock, Mem.write]
  rw [r.next_eq]
  rcases r.ev t with p | p
  · simp only [Cfg.next]
    have hL := hI.loc p
    by_cases hc : (r.s t).pc p = .e23 ∨ (r.s t).pc p = .e26
    · right
      have hb : (r.s t).buf p = [] := by
        unfold LI at hL; rcases hc with hc | hc <;> rw [hc] at hL <;> exact hL.1
      rcases hc with hc | hc <;> simp [Cfg.stepProc, hc, Cfg.cas, hb, hn]
    · by_cases hbar : (r.s t).pc p = .e22 ∨ ∃ o, (r.s t).pc p = .x50 o
      · left
        rcases hbar with hbar | ⟨o, hbar⟩ <;> simp only [Cfg.stepProc, hbar, Cfg.barrier] <;>
          split <;> simp [hn, hflush]
      · left
        push_neg at hc hbar
        rw [stepProc_mem _ _ hbar.1 hc.1 hc.2 hbar.2]; exact hn
  · left; exact hflush p

end Run

/-- Progress by a measure (cf. `Podc.KBakery.exists_good_of_measure`): if from time `T₀` on, as
long as `Good` does not hold, the domain `Dom` is preserved, `μ` never increases and strictly
decreases at every step of `q`, and `q` takes infinitely many steps, then `Good` eventually
holds. -/
lemma exists_good_of_measure (ev : ℕ → Ev h) (q : Proc h)
    (hinf : ∀ T, ∃ t ≥ T, ev t = .step q)
    (Good Dom : ℕ → Prop) (μ : ℕ → ℕ) (T₀ : ℕ) (h₀ : Dom T₀)
    (hstep : ∀ t ≥ T₀, Dom t → ¬ Good (t + 1) →
      Dom (t + 1) ∧ μ (t + 1) ≤ μ t ∧ (ev t = .step q → μ (t + 1) < μ t)) :
    ∃ t ≥ T₀, Good t := by
  by_contra H
  push_neg at H
  have hD : ∀ t ≥ T₀, Dom t := by
    intro t ht
    induction t, ht using Nat.le_induction with
    | base => exact h₀
    | succ t ht ih => exact (hstep t ht ih (H (t + 1) (by omega))).1
  have hmono : ∀ t ≥ T₀, ∀ t' ≥ t, μ t' ≤ μ t := by
    intro t ht t' ht'
    induction t', ht' using Nat.le_induction with
    | base => exact le_rfl
    | succ t' ht' ih =>
      exact (hstep t' (by omega) (hD t' (by omega)) (H (t' + 1) (by omega))).2.1.trans ih
  have hdec : ∀ n : ℕ, ∃ t ≥ T₀, μ t + n ≤ μ T₀ := by
    intro n
    induction n with
    | zero => exact ⟨T₀, le_rfl, by simp⟩
    | succ n ih =>
      obtain ⟨t, ht, hμ⟩ := ih
      obtain ⟨t', ht', hs⟩ := hinf t
      have h1 := (hstep t' (by omega) (hD t' (by omega)) (H (t' + 1) (by omega))).2.2 hs
      have h2 := hmono t ht t' ht'
      exact ⟨t' + 1, by omega, by omega⟩
  obtain ⟨t, -, ht⟩ := hdec (μ T₀ + 1)
  omega

namespace Run

variable {r : Run h}

/-- Under fairness, a process that stays outside the remainder section takes infinitely many
steps. -/
lemma Fair.inf_steps (hf : r.Fair) {q : Proc h} {T : ℕ} (hT : ∀ t ≥ T, (r.s t).pc q ≠ .rem) :
    ∀ T', ∃ t ≥ T', r.ev t = .step q := by
  intro T'
  obtain ⟨t, ht, he⟩ := hf q (max T T') (hT _ (le_max_left _ _))
  exact ⟨t, le_trans (le_max_right _ _) ht, he⟩

end Run

end Podc.ConstantBarriersMutex
