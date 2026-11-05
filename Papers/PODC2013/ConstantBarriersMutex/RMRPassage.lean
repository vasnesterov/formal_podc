import Papers.PODC2013.ConstantBarriersMutex.RMRBound

/-!
# Lemma 10 along runs (assuming the invariant at every time)

The statements here take the invariant `∀ t, Inv (r.s t)` as a hypothesis; `RMRMain.lean`
discharges it with `Run.inv`.
-/

-- The case analyses below use generic tactic combinators; some branches do not need every
-- simp lemma or tactic.
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unreachableTactic false

namespace Podc.ConstantBarriersMutex

open Finset

variable {h : ℕ}

/-! ### Telescoping -/

/-- Telescoping a potential: if every event in `[a, b)` costs at most the decrease of `Φ`, the
total cost is at most `Φ a − Φ b`. -/
lemma sum_add_le_of_step (cost Φ : ℕ → ℕ) {a b : ℕ} (hab : a ≤ b)
    (hstep : ∀ t, a ≤ t → t < b → cost t + Φ (t + 1) ≤ Φ t) :
    ∑ t ∈ Ico a b, cost t + Φ b ≤ Φ a := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hab ih =>
    rw [sum_Ico_succ_top hab]
    have h1 := ih fun t h1 h2 => hstep t h1 (by omega)
    have h2 := hstep b hab (by omega)
    omega

/-- Amortized bound with a charge `ch t` that is non-zero only when the potential is zero. -/
lemma sum_le_of_potential (cost Φ ch : ℕ → ℕ) (M : ℕ) (h0 : Φ 0 ≤ M)
    (hch : ∀ t, ch t ≠ 0 → Φ t = 0 ∧ ch t ≤ M)
    (hstep : ∀ t, cost t + Φ (t + 1) ≤ Φ t + ch t) {t₁ t₂ : ℕ}
    (hno : ∀ t, t₁ < t → t < t₂ → ch t = 0) :
    ∑ t ∈ Ico t₁ t₂, cost t ≤ M := by
  have hΦ : ∀ t, Φ t ≤ M := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih =>
      have := hstep t
      by_cases hc : ch t = 0
      · omega
      · have := hch t hc; omega
  rcases Nat.lt_or_ge t₁ t₂ with hlt | hge
  · rw [sum_eq_sum_Ico_succ_bot hlt]
    have hrest := sum_add_le_of_step cost Φ (a := t₁ + 1) (b := t₂) hlt
      fun t h1 h2 => by have := hstep t; rw [hno t (by omega) h2] at this; omega
    have h1 := hstep t₁
    by_cases hc : ch t₁ = 0
    · have := hΦ t₁; omega
    · have := hch t₁ hc; omega
  · rw [Ico_eq_empty_of_le hge]; simp

/-! ### The cache along a run -/

lemma Run.cache_succ (r : Run h) (t : ℕ) :
    r.cache (t + 1) = (r.cache t).upd (r.s t) (r.ev t) := rfl

/-- The potential along a run. -/
noncomputable def Run.potential (r : Run h) (p : Proc h) (t : ℕ) : ℕ :=
  ConstantBarriersMutex.pot (r.cache t) (r.s t) p

lemma Run.potential_step (r : Run h) (hinv : ∀ t, Inv (r.s t)) (p : Proc h) (t : ℕ) :
    r.cost p t + r.potential p (t + 1) ≤
      r.potential p t + (if (r.s t).pc p = .rem then rmrBound h else 0) := by
  have := (hinv t).pot_step (r.x45_of_inv hinv t) (r.cache t) (r.ev t) p
  rw [← r.step t, ← r.cache_succ] at this
  exact this

/-- Lemma 10 (RMR part), assuming the invariant. -/
theorem Run.rmr_le_of_inv (r : Run h) (hinv : ∀ t, Inv (r.s t)) (p : Proc h) {t₁ t₂ : ℕ}
    (hw : r.WithinPassage p t₁ t₂) : r.rmr p t₁ t₂ ≤ rmrBound h := by
  classical
  refine sum_le_of_potential (r.cost p) (r.potential p)
    (fun t => if (r.s t).pc p = .rem then rmrBound h else 0) (rmrBound h) ?_ ?_
    (r.potential_step hinv p) ?_
  · simp [Run.potential, pot, r.init, Cfg.init]
  · intro t ht
    split_ifs at ht ⊢ with hr
    · exact ⟨by simp [Run.potential, pot, hr], le_rfl⟩
    · exact absurd rfl ht
  · intro t h1 h2; simp [hw t h1 h2]

/-! ### Barriers (no invariant needed) -/

/-- Barrier potential: barriers still to complete in the current passage. -/
def barrierPot : PC h → ℕ
  | .rem => 0
  | .e18 | .e19 _ | .e22 => 2
  | _ => 1

lemma barrier_own (s : Cfg h) (p : Proc h) :
    (if s.BarrierDone p then 1 else 0) + barrierPot ((s.stepProc p).pc p) =
      barrierPot (s.pc p) + (if s.pc p = .rem then 2 else 0) := by
  rcases hpc : s.pc p with _ | _ | l | _ | _ | _ | e | e | _ | _ | _ | _ | _ | ⟨l, j, acc⟩ |
    ⟨l, (_ | ⟨q, cands⟩)⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | ⟨l, q, r⟩ | _ | _ | _ | nx | nx | nx | o <;>
    simp only [Cfg.stepProc, hpc, Cfg.BarrierDone, barrierPot, issue_pc, goto_pc,
      Function.update_self, reduceCtorEq, false_or, or_false, ↓reduceIte, exists_false,
      false_and, barrier_pc, Cfg.cas_pc_self, exists_eq', true_or, true_and]
  all_goals first
    | rfl
    | (split_ifs <;> simp_all [barrierPot])
    | (rcases hq : (s.view p).promQ with _ | ⟨a, b⟩ <;> simp [hq, barrierPot])

lemma barrier_step (s : Cfg h) (e : Ev h) (p : Proc h) :
    (if e = .step p ∧ s.BarrierDone p then 1 else 0) + barrierPot ((s.next e).pc p) =
      barrierPot (s.pc p) + (if e = .step p ∧ s.pc p = .rem then 2 else 0) := by
  by_cases he : e = .step p
  · subst he
    simp only [Cfg.next, true_and]
    convert barrier_own s p
  · have hpc : (s.next e).pc p = s.pc p := by
      by_cases ha : e.actor = p
      · cases e with
        | step q => simp [Ev.actor] at ha; exact absurd (congrArg Ev.step ha) he
        | flush q => simp [Cfg.next]
      · exact s.pc_next_of_ne_actor e ha
    simp [he, hpc]

/-- A complete passage of `p`: `p` starts it by its step at time `t₁` in the remainder section
and is back in the remainder section at time `t₂` for the first time. -/
def Run.Passage (r : Run h) (p : Proc h) (t₁ t₂ : ℕ) : Prop :=
  t₁ < t₂ ∧ (r.s t₁).pc p = .rem ∧ r.ev t₁ = .step p ∧ (r.s t₂).pc p = .rem ∧
    r.WithinPassage p t₁ t₂

lemma Run.barriers_add (r : Run h) (p : Proc h) {t₁ t₂ : ℕ} (h12 : t₁ ≤ t₂) :
    r.barriers p t₁ t₂ + barrierPot ((r.s t₂).pc p) = barrierPot ((r.s t₁).pc p) +
      2 * ((Ico t₁ t₂).filter (fun t => r.ev t = .step p ∧ (r.s t).pc p = .rem)).card := by
  unfold Run.barriers
  induction t₂, h12 using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
    rw [card_filter, card_filter, sum_Ico_succ_top hb, sum_Ico_succ_top hb]
    rw [card_filter, card_filter] at ih
    have := barrier_step (r.s b) (r.ev b) p
    rw [← r.step b] at this
    have h1 : (if r.ev b = .step p ∧ (r.s b).pc p = .rem then 2 else 0) =
        2 * (if r.ev b = .step p ∧ (r.s b).pc p = .rem then 1 else 0) := by split_ifs <;> rfl
    omega

/-- In an interval within one passage, the only possible step in the remainder section is the
first event. -/
lemma Run.card_remSteps_le (r : Run h) (p : Proc h) {t₁ t₂ : ℕ}
    (hw : r.WithinPassage p t₁ t₂) :
    ((Ico t₁ t₂).filter (fun t => r.ev t = .step p ∧ (r.s t).pc p = .rem)).card ≤
      (if (r.s t₁).pc p = .rem then 1 else 0) := by
  have hsub : (Ico t₁ t₂).filter (fun t => r.ev t = .step p ∧ (r.s t).pc p = .rem) ⊆
      if (r.s t₁).pc p = .rem then {t₁} else ∅ := by
    intro t ht
    simp only [mem_filter, mem_Ico] at ht
    rcases Nat.lt_or_ge t₁ t with hlt | hge
    · exact absurd ht.2.2 (hw t hlt ht.1.2)
    · obtain rfl : t = t₁ := by omega
      simp [ht.2.2]
  refine (card_le_card hsub).trans ?_
  split_ifs <;> simp

/-- Lemma 10 (barrier part): within (a part of) one passage, at most two barriers complete. -/
theorem Run.barriers_le (r : Run h) (p : Proc h) {t₁ t₂ : ℕ} (hw : r.WithinPassage p t₁ t₂) :
    r.barriers p t₁ t₂ ≤ 2 := by
  rcases Nat.lt_or_ge t₂ t₁ with hlt | hge
  · simp [Run.barriers, Ico_eq_empty_of_le hlt.le]
  · have h1 := r.barriers_add p hge
    have h2 := r.card_remSteps_le p hw
    by_cases hr : (r.s t₁).pc p = .rem
    · simp only [hr, ite_true, barrierPot] at h1 h2; omega
    · simp only [hr, ite_false] at h2
      have : barrierPot ((r.s t₁).pc p) ≤ 2 := by unfold barrierPot; split <;> omega
      omega

/-- Lemma 10 (barrier part): a complete passage completes exactly two barriers (statements 22
and 50). -/
theorem Run.barriers_passage (r : Run h) (p : Proc h) {t₁ t₂ : ℕ} (hP : r.Passage p t₁ t₂) :
    r.barriers p t₁ t₂ = 2 := by
  obtain ⟨hlt, h1, he, h2, hw⟩ := hP
  have hadd := r.barriers_add p hlt.le
  have hcard : ((Ico t₁ t₂).filter (fun t => r.ev t = .step p ∧ (r.s t).pc p = .rem)).card = 1 := by
    apply le_antisymm
    · simpa [h1] using r.card_remSteps_le p hw
    · exact card_pos.2 ⟨t₁, by simp [hlt, he, h1]⟩
  rw [h1, h2, hcard] at hadd
  simp only [barrierPot] at hadd
  omega

/-! ### The busy-waiting statements 25 and 27 separately -/

lemma Cfg.pc_next_of_ne_step (s : Cfg h) {e : Ev h} {p : Proc h} (he : e ≠ .step p) :
    (s.next e).pc p = s.pc p := by
  by_cases ha : e.actor = p
  · cases e with
    | step q => simp [Ev.actor] at ha; exact absurd (congrArg Ev.step ha) he
    | flush q => simp [Cfg.next]
  · exact s.pc_next_of_ne_actor e ha

/-- `p` is at statement 25. -/
def PC.At25 : PC h → Prop
  | .e25a _ | .e25b _ => True
  | _ => False

lemma Cfg.at25_next (s : Cfg h) (e : Ev h) (p : Proc h) (hp : (s.pc p).At25) :
    ((s.next e).pc p).At25 ∨ (s.next e).pc p = .e26 := by
  by_cases he : e = .step p
  · subst he
    simp only [Cfg.next, Cfg.stepProc]
    rcases hpc : s.pc p <;> simp only [hpc, PC.At25] at hp ⊢ <;>
      simp only [goto_pc, Function.update_self] <;> split_ifs <;> simp [PC.At25]
  · rw [s.pc_next_of_ne_step he]; exact Or.inl hp

lemma pot_at25 (c : Cache h) (s : Cfg h) (p : Proc h)
    (hp : (s.pc p).At25 ∨ s.pc p = .e26) : 3 + exB h ≤ pot c s p := by
  rcases hp with hp | hp
  · unfold pot; split <;> simp_all [PC.At25]
  · simp [pot, hp]

/-- **Statement 25, assuming the invariant**: the RMRs incurred by `p` while busy-waiting at
statement 25 (from the step after statement 24 until it leaves statement 25) are at most `6`. -/
theorem Run.stmt25_rmr_le_of_inv (r : Run h) (hinv : ∀ t, Inv (r.s t)) (p : Proc h)
    {t₀ t₂ : ℕ} (h0 : (r.s t₀).pc p = .e24) (he : r.ev t₀ = .step p)
    (hin : ∀ t, t₀ < t → t < t₂ → ((r.s t).pc p).At25) : r.rmr p (t₀ + 1) t₂ ≤ 6 := by
  rcases Nat.lt_or_ge (t₀ + 1) t₂ with hlt | hge
  · have htel := sum_add_le_of_step (r.cost p) (r.potential p) hlt.le fun t h1 h2 => by
      have := r.potential_step hinv p t
      have hr : (r.s t).pc p ≠ .rem := by
        intro h'; have := hin t (by omega) h2; rw [h'] at this; exact this
      simpa [hr] using this
    -- the potential right after statement 24
    have hb : (r.s t₀).buf p = [] := by have := (hinv t₀).loc p; simp only [LI, h0] at this; exact this.1
    have hs1 : r.s (t₀ + 1) = (r.s t₀).goto p (.e25a (r.s t₀).mem.exits) := by
      rw [r.step t₀, he]; simp [Cfg.next, Cfg.stepProc, h0, Cfg.view, hb]
    have hrd : (r.s t₀).rdVar p = some .exits := by simp [Cfg.rdVar, h0]
    have hcx : r.cache (t₀ + 1) p .exits = true := by
      rw [r.cache_succ, he, upd_self_read _ _ hb hrd]; simp
    have hΦ1 : r.potential p (t₀ + 1) ≤ 9 + exB h := by
      have := phi25_entry (r.cache (t₀ + 1)) ((r.s t₀).goto p (.e25a (r.s t₀).mem.exits)) p hcx
      simp only [goto_mem] at this
      simp only [Run.potential, hs1, pot, goto_pc, Function.update_self]
      omega
    have hΦ2 : 3 + exB h ≤ r.potential p t₂ := by
      apply pot_at25
      obtain ⟨t, rfl⟩ : ∃ t, t₂ = t + 1 := ⟨t₂ - 1, by omega⟩
      rw [r.step t]
      exact (r.s t).at25_next _ p (hin t (by omega) (by omega))
    unfold Run.rmr; omega
  · simp [Run.rmr, Ico_eq_empty_of_le hge]

/-- **Statement 27, assuming the invariant**: the RMRs incurred by `p` while busy-waiting at
statement 27 are at most `2`. -/
theorem Run.stmt27_rmr_le_of_inv (r : Run h) (hinv : ∀ t, Inv (r.s t)) (p : Proc h)
    {t₀ t₂ : ℕ} (hin : ∀ t, t₀ ≤ t → t < t₂ → (r.s t).pc p = .e27) : r.rmr p t₀ t₂ ≤ 2 := by
  rcases Nat.lt_or_ge t₀ t₂ with hlt | hge
  · have htel := sum_add_le_of_step (r.cost p) (r.potential p) hlt.le fun t h1 h2 => by
      have := r.potential_step hinv p t
      simpa [hin t h1 h2] using this
    have hΦ1 : r.potential p t₀ ≤ 2 + exB h := by
      have := phi27_le (r.cache t₀) (r.s t₀) p
      simp only [Run.potential, pot, hin t₀ le_rfl hlt]; omega
    have hΦ2 : exB h ≤ r.potential p t₂ := by
      obtain ⟨t, rfl⟩ : ∃ t, t₂ = t + 1 := ⟨t₂ - 1, by omega⟩
      have ht := hin t (by omega) (by omega)
      have : (r.s (t + 1)).pc p = .e27 ∨ (r.s (t + 1)).pc p = .cs := by
        rw [r.step t]
        by_cases he : r.ev t = .step p
        · rw [he]; simp only [Cfg.next, Cfg.stepProc, ht]; split_ifs <;> simp [ht]
        · rw [(r.s t).pc_next_of_ne_step he]; exact Or.inl ht
      rcases this with h' | h' <;> simp [Run.potential, pot, h']
    unfold Run.rmr; omega
  · simp [Run.rmr, Ico_eq_empty_of_le hge]

end Podc.ConstantBarriersMutex
