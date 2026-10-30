import Papers.PODC2020.RecoverableMutexRMR.Invariant

/-!
# Safety: Lemma 2.1 (selected items), Lemma 2.3, mutual exclusion (Lemma 2.11), critical
section re-entry, and the bound on skipped tickets (Lemma 2.10)
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

/-! ### Lemma 2.1 (state invariants), Lemma 2.3 -/

/-- Lemma 2.1 (4): `Token ∈ {0, …, C}`. -/
theorem lemma2_1_4 (e : ℕ → Ev P) (t : ℕ) : (exec e t).T ≤ (exec e t).C :=
  (inv_exec e t).T_le

/-- Lemma 2.1 (7): a process in the critical section has `W[p] = (w, true)` with `w ≠ 0`. -/
theorem lemma2_1_7 (e : ℕ → Ev P) (t : ℕ) (p : P) (h : (exec e t).pc p = .cs) :
    ∃ w, w ≠ 0 ∧ (exec e t).W p = (w, true) := by
  have hI := inv_exec e t
  have hL := hI.loc p; simp only [LI, h] at hL
  refine ⟨((exec e t).W p).1, ?_, Prod.ext rfl hL.2⟩
  rw [(hI.grant p hL.2).1]; omega

/-- Lemma 2.1 (8): the CAS of line 5 always succeeds (`W[p] = (0,false)` when it is executed). -/
theorem lemma2_1_8 (e : ℕ → Ev P) (t : ℕ) (p : P) (c : ℕ) (h : (exec e t).pc p = .l5 c) :
    (exec e t).W p = (0, false) := by
  have hL := (inv_exec e t).loc p; simp only [LI, h] at hL; exact hL.2.1

/-- Lemma 2.1 (9): the ticket read at line 23 is positive. -/
theorem lemma2_1_9 (e : ℕ → Ev P) (t : ℕ) (p : P) (h : (exec e t).pc p = .w23) :
    ((exec e t).W p).1 ≠ 0 := by
  have hL := (inv_exec e t).loc p; simp only [LI, h] at hL; exact hL.2

/-- Lemma 2.1 (11): if `Token = ℓ`, then `A[1..ℓ]` are all nonzero. -/
theorem lemma2_1_11 (e : ℕ → Ev P) (t : ℕ) (x : ℕ) (hx : x ≠ 0) (hxT : x ≤ (exec e t).T) :
    (exec e t).A x ≠ .empty :=
  (inv_exec e t).A_tok x hx hxT

/-- Lemma 2.1 (16): at most one entry of `W[1..n]` contains `(−, true)`. -/
theorem lemma2_1_16 (e : ℕ → Ev P) (t : ℕ) (p q : P) (hp : ((exec e t).W p).2 = true)
    (hq : ((exec e t).W q).2 = true) : p = q := by
  have hI := inv_exec e t
  have h1 := (hI.grant p hp).2; rw [(hI.grant q hq).2] at h1
  cases h1; rfl

/-- Lemma 2.3: `D_t + |I_t| − C_t ≥ 0`. -/
theorem lemma2_3 (e : ℕ → Ev P) (t : ℕ) : 0 ≤ Phi (exec e t) (ghost e t) :=
  (inv_exec e t).phi_nonneg

/-! ### Mutual exclusion -/

/-- **Lemma 2.11 (Mutual exclusion).** At any time at most one process is in the critical
section. -/
theorem mutual_exclusion (e : ℕ → Ev P) (t : ℕ) (p q : P) (hp : (exec e t).pc p = .cs)
    (hq : (exec e t).pc q = .cs) : p = q := by
  have hI := inv_exec e t
  have hLp := hI.loc p; simp only [LI, hp] at hLp
  have hLq := hI.loc q; simp only [LI, hq] at hLq
  exact lemma2_1_16 e t p q hLp.2 hLq.2

/-! ### Steps of other processes -/

namespace Safety

lemma step_pc_other (s : Cfg P) {p q : P} (h : q ≠ p) : (s.step q).pc p = s.pc p := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp [Cfg.setPc, Function.update_of_ne (Ne.symm h)]

lemma step_X_other (s : Cfg P) {p q : P} (h : q ≠ p) : (s.step q).X p = s.X p := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp [Cfg.setPc, Function.update_of_ne (Ne.symm h)]

lemma step_W_snd_other (s : Cfg P) {p q : P} (h : q ≠ p) (hW : (s.W p).2 = true) :
    ((s.step q).W p).2 = true := by
  unfold Cfg.step
  split <;> (try split_ifs) <;> simp [Cfg.setPc, Function.update_of_ne (Ne.symm h), hW]
  all_goals (rw [Function.update_apply]; split_ifs <;> simp_all)

lemma crash_other (s : Cfg P) {p q : P} (h : q ≠ p) :
    (s.crash q).pc p = s.pc p ∧ (s.crash q).X p = s.X p ∧ (s.crash q).W p = s.W p := by
  unfold Cfg.crash; split_ifs <;> simp [Cfg.setPc, Function.update_of_ne (Ne.symm h)]

/-- The recovery states after a crash in the critical section. -/
def RecCS (s : Cfg P) (p : P) : Prop :=
  (s.pc p = .r15 ∨ s.pc p = .r16 ∨ s.pc p = .r18) ∧ s.X p = false ∧ (s.W p).2 = true

/-- Progress of `p` along `r15 → r16 → r18 → cs`. -/
def lvl : PC P → ℕ
  | .r16 => 1
  | .r18 => 2
  | .cs => 3
  | _ => 0

lemma recCS_next (s : Cfg P) (p : P) (h : RecCS s p) (ev : Ev P) :
    (s.next ev).pc p = .cs ∨ (RecCS (s.next ev) p ∧
      (ev ≠ .crash p → lvl (s.pc p) ≤ lvl ((s.next ev).pc p)) ∧
      (ev = .step p → lvl (s.pc p) < lvl ((s.next ev).pc p))) := by
  obtain ⟨hpc, hX, hW⟩ := h
  cases ev with
  | step q =>
    by_cases hq : q = p
    · subst hq
      rcases hpc with hpc | hpc | hpc
      · right; simp [Cfg.next, Cfg.step, hpc, RecCS, hX, hW, lvl]
      · right; simp [Cfg.next, Cfg.step, hpc, RecCS, hX, hW, lvl]
      · left; simp [Cfg.next, Cfg.step, hpc, hW]
    · right
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · simp only [Cfg.next, step_pc_other s hq]; exact hpc
      · simp only [Cfg.next, step_X_other s hq]; exact hX
      · exact step_W_snd_other s hq hW
      · intro _; simp [Cfg.next, step_pc_other s hq]
      · intro h; cases h; exact absurd rfl hq
  | crash q =>
    right
    by_cases hq : q = p
    · subst hq
      have hne : s.pc q ≠ .rem := by rcases hpc with h | h | h <;> simp [h]
      simp only [Cfg.next, Cfg.crash, hne, if_false]
      refine ⟨⟨by simp, by simp [hX], by simp [hW]⟩, by simp, by simp⟩
    · obtain ⟨a, b, c⟩ := crash_other s hq
      simp only [Cfg.next, RecCS, a, b, c]
      exact ⟨⟨hpc, hX, hW⟩, fun _ => le_rfl, by simp⟩

end Safety

open Safety

/-- After a crash of `p` in the critical section and until `p` is back in the critical section,
`p` is in `Recover()` with `Exit[p] = false` and `W[p] = (−, true)`. -/
lemma recCS_of_crash (e : ℕ → Ev P) (p : P) (t₀ : ℕ) (hcs : (exec e t₀).pc p = .cs)
    (hcr : e t₀ = .crash p) (t : ℕ) (ht : t₀ < t)
    (hnot : ∀ u, t₀ < u → u ≤ t → (exec e u).pc p ≠ .cs) :
    RecCS (exec e t) p := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases h0 : t = t₀
    · subst h0
      have hL := (inv_exec e t).loc p; simp only [LI, hcs] at hL
      simp only [exec_succ, hcr, Cfg.next, Cfg.crash, hcs]
      exact ⟨by simp, by simp [hL.1], by simp [hL.2]⟩
    · have ih' := ih (by omega) (fun u h1 h2 => hnot u h1 (by omega))
      rcases recCS_next _ p ih' (e t) with h | ⟨h1, -⟩
      · exact absurd h (hnot (t + 1) (by omega) le_rfl)
      · exact h1

lemma filter_Ioo_succ (e : ℕ → Ev P) (p : P) (t₀ t : ℕ) (ht : t₀ ≤ t) :
    ((Finset.Ioo t₀ (t + 1)).filter (fun u => e u = .step p)).card ≤
      ((Finset.Ioo t₀ t).filter (fun u => e u = .step p)).card +
        (if e t = .step p ∧ t₀ < t then 1 else 0) := by
  have hsub : (Finset.Ioo t₀ (t + 1)).filter (fun u => e u = .step p) ⊆
      (if e t = .step p ∧ t₀ < t then {t} else ∅) ∪
        (Finset.Ioo t₀ t).filter (fun u => e u = .step p) := by
    intro u hu
    simp only [Finset.mem_filter, Finset.mem_Ioo] at hu
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioo]
    by_cases hut : u = t
    · subst hut; left; rw [if_pos ⟨hu.2, hu.1.1⟩]; simp
    · right; exact ⟨⟨hu.1.1, by omega⟩, hu.2⟩
  refine (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans ?_)
  split_ifs <;> simp [add_comm]

/-- Without further crashes of `p`, each step of `p` advances it along `r15 → r16 → r18 → cs`. -/
lemma recCS_level (e : ℕ → Ev P) (p : P) (t₀ : ℕ) (hcs : (exec e t₀).pc p = .cs)
    (hcr : e t₀ = .crash p) (t : ℕ) (ht : t₀ < t)
    (hnot : ∀ u, t₀ < u → u ≤ t → (exec e u).pc p ≠ .cs)
    (hnocr : ∀ u, t₀ < u → u < t → e u ≠ .crash p) :
    ((Finset.Ioo t₀ t).filter (fun u => e u = .step p)).card ≤ lvl ((exec e t).pc p) := by
  induction t with
  | zero => omega
  | succ t ih =>
    by_cases h0 : t = t₀
    · subst h0
      have : (Finset.Ioo t (t + 1)).filter (fun u => e u = .step p) = ∅ := by
        ext u; simp
      rw [this]; simp
    · have ih' := ih (by omega) (fun u h1 h2 => hnot u h1 (by omega))
        (fun u h1 h2 => hnocr u h1 (by omega))
      have hR := recCS_of_crash e p t₀ hcs hcr t (by omega) (fun u h1 h2 => hnot u h1 (by omega))
      have hc := filter_Ioo_succ e p t₀ t (by omega)
      rcases recCS_next _ p hR (e t) with h | ⟨-, h2, h3⟩
      · exact absurd h (hnot (t + 1) (by omega) le_rfl)
      · rw [exec_succ]
        have h2' := h2 (hnocr t (by omega) (by omega))
        split_ifs at hc with he
        · have := h3 he.1; omega
        · omega

/-- **Critical section re-entry.** If `p` crashes in the critical section, then no other process
enters the critical section before `p` re-enters it. -/
theorem cs_reentry (e : ℕ → Ev P) (p : P) (t₀ : ℕ) (hcs : (exec e t₀).pc p = .cs)
    (hcr : e t₀ = .crash p) (t : ℕ) (ht : t₀ < t)
    (hnot : ∀ u, t₀ < u → u ≤ t → (exec e u).pc p ≠ .cs) (q : P) :
    (exec e t).pc q ≠ .cs := by
  intro hq
  have h := recCS_of_crash e p t₀ hcs hcr t ht hnot
  have hLq := (inv_exec e t).loc q; simp only [LI, hq] at hLq
  have := lemma2_1_16 e t p q h.2.2 hLq.2
  subst this
  rcases h.1 with h | h | h <;> rw [h] at hq <;> cases hq

/-- **Lemma 2.14 (Wait-free critical section re-entry)**, with bound `b = 3`: if `p` crashes in
the critical section, it is back in the critical section as soon as it has taken 3 steps
(whatever the other processes and further crashes of `p` do in between). -/
theorem cs_reentry_waitfree (e : ℕ → Ev P) (p : P) (t₀ : ℕ) (hcs : (exec e t₀).pc p = .cs)
    (hcr : e t₀ = .crash p) (t : ℕ) (ht : t₀ < t)
    (hsteps : 3 ≤ ((Finset.Ioo t₀ t).filter (fun u => e u = .step p)).card)
    (hnocr : ∀ u, t₀ < u → u < t → e u ≠ .crash p) :
    ∃ u, t₀ < u ∧ u ≤ t ∧ (exec e u).pc p = .cs := by
  by_contra hno
  push Not at hno
  have h := recCS_of_crash e p t₀ hcs hcr t ht hno
  have h2 := recCS_level e p t₀ hcs hcr t ht hno hnocr
  have : lvl ((exec e t).pc p) ≤ 2 := by
    rcases h.1 with h' | h' | h' <;> simp [h', lvl]
  omega

end Podc.RecoverableMutexRMR
