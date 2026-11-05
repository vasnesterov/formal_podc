import Papers.PODC2019.RMESubLogBoth.Invariant
import Papers.PODC2019.RMESubLogBoth.StepPC

/-!
# Mutual exclusion, wait-free exit, critical-section re-entry (Lemmas 4, 6, 7, 8)
-/

namespace Podc.RMESubLogBoth

variable {k : ℕ}

/-- A process in the CS holds the right to the CS. -/
lemma inH_of_cs {c : Cfg k} {own : ℕ → ℕ} (hL : ∀ q, LI c own q) {p : Fin k} {x : ℕ}
    (h : c.pc p = .cs x) : c.node p = some x ∧ c.InH x := by
  have := hL p; unfold LI at this; rw [h] at this
  exact ⟨this.1, ⟨p, this.1⟩, .inl this.2.1⟩

/-- **Lemma 4 (Mutual Exclusion).** At most one process is in the CS in every reachable
configuration. -/
theorem mutual_exclusion {c : Cfg k} (hc : Reach c) {p q : Fin k} (hp : c.InCS p)
    (hq : c.InCS q) : p = q := by
  obtain ⟨own, hG, hL⟩ := inv_reach hc
  obtain ⟨x, hx⟩ := hp
  obtain ⟨y, hy⟩ := hq
  obtain ⟨hnx, hHx⟩ := inH_of_cs hL hx
  obtain ⟨hny, hHy⟩ := inH_of_cs hL hy
  have := hG.hUniq x y hHx hHy; subst this
  exact hG.node_inj hnx hny

/-- While the node of `p` is marked `&InCS` (e.g. after `p` crashed in the CS), no other process
is in the CS. -/
theorem no_other_cs {c : Cfg k} (hc : Reach c) {p q : Fin k} {x : ℕ} (hn : c.node p = some x)
    (hx : c.pred x = .incs) (hq : c.InCS q) : q = p := by
  obtain ⟨own, hG, hL⟩ := inv_reach hc
  obtain ⟨y, hy⟩ := hq
  obtain ⟨hny, hHy⟩ := inH_of_cs hL hy
  have := hG.hUniq x y ⟨⟨p, hn⟩, .inl hx⟩ hHy; subst this
  exact hG.node_inj hny hn

/-- Steps of another process do not change the `Pred` field of `p`'s node. -/
lemma Step.pred_other {c c' : Cfg k} (hI : Inv c) {q : Fin k} (h : Step c q c') {p : Fin k}
    (hpq : p ≠ q) {x : ℕ} (hn : c.node p = some x) : c'.pred x = c.pred x := by
  obtain ⟨own, hG, hL⟩ := hI
  have hne : ∀ y, c.node q = some y → x ≠ y := fun y hy hxy =>
    hpq (hG.node_inj hn (hxy ▸ hy))
  have hLq := hL q
  unfold LI at hLq
  cases h with
  | l14 y m h' => rw [h'] at hLq; simp [Function.update_apply, hne y hLq.1]
  | l18w y h' => rw [h'] at hLq; simp [Function.update_apply, hne y hLq.1]
  | l49 y m h' => rw [h'] at hLq; simp [Function.update_apply, hne y hLq.1]
  | l26 y h' => rw [h'] at hLq; simp [Function.update_apply, hne y hLq.1]
  | cs y h' => rw [h'] at hLq; simp [Function.update_apply, hne y hLq.1]
  | _ => simp [Cfg.setPc]

/-! ### Counting the steps of a process -/

/-- The number of (normal) steps of `p` in the time interval `[t, t')`. -/
def stepsOf (r : Run k) (p : Fin k) (t t' : ℕ) : ℕ :=
  ((Finset.Ico t t').filter (fun s => r.ev s = .step p)).card

lemma stepsOf_succ (r : Run k) (p : Fin k) {t t' : ℕ} (h : t ≤ t') :
    stepsOf r p t (t' + 1) = stepsOf r p t t' + if r.ev t' = .step p then 1 else 0 := by
  unfold stepsOf
  rw [Nat.Ico_succ_right_eq_insert_Ico h, Finset.filter_insert]
  split_ifs with he
  · rw [Finset.card_insert_of_notMem (by simp)]
  · rfl

lemma stepsOf_self (r : Run k) (p : Fin k) (t : ℕ) : stepsOf r p t t = 0 := by simp [stepsOf]

/-- **Lemma 6 (Wait-free Exit).** A process in the Exit section (after line 27) that takes
steps without crashing returns to the remainder section within `2` of its steps. -/
theorem wait_free_exit (r : Run k) (p : Fin k) (t : ℕ)
    (h : (∃ x, (r.cfg t).pc p = .l28 x) ∨ (r.cfg t).pc p = .l29) (t' : ℕ) (htt : t ≤ t')
    (hnc : ∀ s, t ≤ s → s < t' → r.ev s ≠ .crash p) (hst : 2 ≤ stepsOf r p t t') :
    ∃ s, t < s ∧ s ≤ t' ∧ (r.cfg s).pc p = .rem := by
  have key : ∀ u, t ≤ u → u ≤ t' → (∃ s, t < s ∧ s ≤ u ∧ (r.cfg s).pc p = .rem) ∨
      ((∃ x, (r.cfg u).pc p = .l28 x) ∧ stepsOf r p t u = 0) ∨
      ((r.cfg u).pc p = .l29 ∧ stepsOf r p t u ≤ 1) := by
    intro u hu hu'
    induction u, hu using Nat.le_induction with
    | base =>
      rw [stepsOf_self]
      rcases h with h | h
      · exact .inr (.inl ⟨h, rfl⟩)
      · exact .inr (.inr ⟨h, by omega⟩)
    | succ u hu ih =>
      have hn := r.next u
      rw [stepsOf_succ r p hu]
      rcases ih (by omega) with ⟨s, hs1, hs2, hs3⟩ | ⟨⟨x, hx⟩, h0⟩ | ⟨hx, h1⟩
      · exact .inl ⟨s, hs1, by omega, hs3⟩
      · by_cases he : r.ev u = .step p
        · rw [he] at hn
          have := step_l28 hn hx
          exact .inr (.inr ⟨this, by simp [he, h0]⟩)
        · have := Next.pc_other hn he (hnc u hu (by omega))
          exact .inr (.inl ⟨⟨x, by rw [this, hx]⟩, by simp [he, h0]⟩)
      · by_cases he : r.ev u = .step p
        · rw [he] at hn
          exact .inl ⟨u + 1, by omega, le_rfl, step_l29 hn hx⟩
        · have := Next.pc_other hn he (hnc u hu (by omega))
          exact .inr (.inr ⟨by rw [this, hx], by simp [he]; omega⟩)
  rcases key t' htt le_rfl with h1 | ⟨-, h2⟩ | ⟨-, h2⟩
  · exact h1
  · omega
  · omega

/-- The state of a process that crashed in the CS and has not re-entered it yet. -/
def CrashedInCS (c : Cfg k) (p : Fin k) (x : ℕ) : Prop :=
  c.node p = some x ∧ c.pred x = .incs ∧
    (c.pc p = .l10 ∨ c.pc p = .l18 x ∨ c.pc p = .l19 x)

lemma crashedInCS_next {c c' : Cfg k} (hc : Reach c) {e : Ev k} (h : Next c e c') {p : Fin k}
    {x : ℕ} (hC : CrashedInCS c p x) :
    CrashedInCS c' p x ∨ (e = .step p ∧ c'.pc p = .cs x ∧ c.pc p = .l19 x) := by
  obtain ⟨hn, hx, hpc⟩ := hC
  cases e with
  | crash q =>
    change c' = c.crash q at h; subst h
    left
    refine ⟨hn, hx, ?_⟩
    by_cases hq : p = q
    · subst hq; left; simp [Cfg.crash, Cfg.setPc]
    · simp only [Cfg.crash, Cfg.setPc, Function.update_apply, hq, if_false]; exact hpc
  | step q =>
    have h' : Step c q c' := h
    by_cases hq : p = q
    · subst hq
      rcases hpc with hpc | hpc | hpc
      · left
        rcases step_l10 h' (.inr hpc) with ⟨hn', -⟩ | ⟨y, hy, h2⟩
        · rw [hn] at hn'; cases hn'
        · rw [hn] at hy; cases hy
          have hnode : c'.node p = c.node p := by
            cases h' <;> simp_all [Cfg.setPc]
          have hpred : c'.pred x = c.pred x := by
            cases h' <;> simp_all [Cfg.setPc]
          exact ⟨hnode ▸ hn, hpred ▸ hx, .inr (.inl h2)⟩
      · left
        cases h' with
        | l18 y h2 =>
          rw [hpc] at h2; cases h2
          simp only [Cfg.setPc, Function.update_self, hx, reduceCtorEq, if_false]
          exact ⟨hn, hx, .inr (.inr (by simp))⟩
        | _ => simp_all
      · right
        cases h' with
        | l19 y h2 =>
          rw [hpc] at h2; cases h2
          simp [Cfg.setPc, hx, hpc]
        | _ => simp_all
    · left
      exact ⟨by rw [Step.node_other h' hq, hn], by rw [Step.pred_other (inv_reach hc) h' hq hn, hx],
        by rw [Step.pc_other h' hq]; exact hpc⟩

/-- **Lemma 8 (Critical Section Reentry).** If `p` crashes while in the CS, no other process is
in the CS from the crash until `p` re-enters the CS. -/
theorem cs_reentry (r : Run k) (p : Fin k) (t : ℕ) (x : ℕ) (hcs : (r.cfg t).pc p = .cs x)
    (hcr : r.ev t = .crash p) (s : ℕ) (hts : t < s)
    (hno : ∀ u, t < u → u ≤ s → ¬ (r.cfg u).InCS p) (q : Fin k) (hq : (r.cfg s).InCS q) :
    q = p := by
  have h0 : CrashedInCS (r.cfg (t + 1)) p x := by
    have hn := r.next t
    rw [hcr] at hn; change r.cfg (t + 1) = (r.cfg t).crash p at hn
    obtain ⟨own, -, hL⟩ := inv_reach (r.reach t)
    have := hL p; unfold LI at this; rw [hcs] at this
    rw [hn]; exact ⟨this.1, this.2.1, .inl (by simp [Cfg.crash, Cfg.setPc])⟩
  have key : ∀ u, t + 1 ≤ u → u ≤ s → CrashedInCS (r.cfg u) p x := by
    intro u hu hus
    induction u, hu using Nat.le_induction with
    | base => exact h0
    | succ u hu ih =>
      rcases crashedInCS_next (r.reach u) (r.next u) (ih (by omega)) with h | ⟨-, h, -⟩
      · exact h
      · exact absurd ⟨x, h⟩ (hno (u + 1) (by omega) hus)
  obtain ⟨hn, hx, -⟩ := key s (by omega) le_rfl
  exact no_other_cs (r.reach s) hn hx hq

/-- **Lemma 7 (Wait-free CSR).** If `p` crashes while in the CS, it re-enters the CS within `3`
of its subsequent steps, provided it does not crash again. -/
theorem wait_free_csr (r : Run k) (p : Fin k) (t : ℕ) (x : ℕ) (hcs : (r.cfg t).pc p = .cs x)
    (hcr : r.ev t = .crash p) (t' : ℕ) (htt : t + 1 ≤ t')
    (hnc : ∀ s, t + 1 ≤ s → s < t' → r.ev s ≠ .crash p) (hst : 3 ≤ stepsOf r p (t + 1) t') :
    ∃ s, t < s ∧ s ≤ t' ∧ (r.cfg s).InCS p := by
  have h0 : CrashedInCS (r.cfg (t + 1)) p x := by
    have hn := r.next t
    rw [hcr] at hn; change r.cfg (t + 1) = (r.cfg t).crash p at hn
    obtain ⟨own, -, hL⟩ := inv_reach (r.reach t)
    have := hL p; unfold LI at this; rw [hcs] at this
    rw [hn]; exact ⟨this.1, this.2.1, .inl (by simp [Cfg.crash, Cfg.setPc])⟩
  -- rank: line 10 ↦ 3, line 18 ↦ 2, line 19 ↦ 1
  let ρ : Cfg k → ℕ := fun c => match c.pc p with
    | .l10 => 3
    | .l18 _ => 2
    | _ => 1
  have key : ∀ u, t + 1 ≤ u → u ≤ t' → (∃ s, t < s ∧ s ≤ u ∧ (r.cfg s).InCS p) ∨
      (CrashedInCS (r.cfg u) p x ∧ stepsOf r p (t + 1) u + ρ (r.cfg u) ≤ 3) := by
    intro u hu hu'
    induction u, hu using Nat.le_induction with
    | base => right; refine ⟨h0, ?_⟩; rw [stepsOf_self]; simp only [ρ]; split <;> omega
    | succ u hu ih =>
      rcases ih (by omega) with h1 | ⟨hC, hle⟩
      · obtain ⟨s, hs1, hs2, hs3⟩ := h1; exact .inl ⟨s, hs1, by omega, hs3⟩
      · rw [stepsOf_succ r p hu]
        rcases crashedInCS_next (r.reach u) (r.next u) hC with hC' | ⟨-, h2, -⟩
        · right; refine ⟨hC', ?_⟩
          by_cases he : r.ev u = .step p
          · -- a step of `p` moves it forward
            have hn := r.next u; rw [he] at hn
            obtain ⟨hn0, -, hpc⟩ := hC
            obtain ⟨-, -, hpc'⟩ := hC'
            simp only [he, if_true]
            rcases hpc with hpc | hpc | hpc
            · rcases step_l10 hn (.inr hpc) with ⟨h3, -⟩ | ⟨y, -, h3⟩
              · rw [hn0] at h3; cases h3
              · simp only [ρ, hpc, h3, if_true] at hle ⊢; simp at hle ⊢; omega
            · rcases step_l18 hn hpc with h3 | h3
              · rcases hpc' with h4 | h4 | h4 <;> rw [h3] at h4 <;> cases h4
              · simp only [ρ, hpc, h3] at hle ⊢; simp at hle ⊢; omega
            · rcases step_l19 hn hpc with h3 | h3 | ⟨v, h3⟩ <;>
                rcases hpc' with h4 | h4 | h4 <;> rw [h3] at h4 <;> cases h4
          · have := Next.pc_other (r.next u) he (hnc u hu (by omega))
            simp only [he, if_false, add_zero, ρ, this] at hle ⊢; exact hle
        · exact .inl ⟨u + 1, by omega, le_rfl, ⟨x, h2⟩⟩
  rcases key t' htt le_rfl with h1 | ⟨-, h2⟩
  · exact h1
  · simp only [ρ] at h2; split at h2 <;> omega

end Podc.RMESubLogBoth
