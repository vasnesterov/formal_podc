import Papers.PODC2020.RecoverableMutexRMR.Safety

/-!
# Wait-free recovery (Lemma 2.12) and wait-free recovery to exit (Lemma 2.15)
-/

set_option linter.unusedSectionVars false

namespace Podc.RecoverableMutexRMR

variable {P : Type} [DecidableEq P] [Fintype P]

open Safety

/-- Generic progress counting: while `J` holds and the target `Tg` is not reached, every event
other than a crash of `p` keeps `J`, does not decrease the level `lv`, and every step of `p`
increases it. -/
lemma progress_steps (e : ℕ → Ev P) (p : P) (J Tg : Cfg P → Prop) (lv : Cfg P → ℕ)
    (hstep : ∀ s ev, J s → ¬ Tg (s.next ev) → ev ≠ .crash p →
      J (s.next ev) ∧ lv s ≤ lv (s.next ev) ∧ (ev = .step p → lv s < lv (s.next ev)))
    (t₁ : ℕ) (h1 : J (exec e t₁)) (t : ℕ) (ht : t₁ ≤ t)
    (hT : ∀ u, t₁ < u → u ≤ t → ¬ Tg (exec e u)) (hnc : ∀ u, t₁ ≤ u → u < t → e u ≠ .crash p) :
    J (exec e t) ∧
      ((Finset.Ico t₁ t).filter (fun u => e u = .step p)).card + lv (exec e t₁) ≤
        lv (exec e t) := by
  induction t with
  | zero =>
    have : t₁ = 0 := by omega
    subst this; exact ⟨h1, by simp⟩
  | succ t ih =>
    by_cases h0 : t + 1 = t₁
    · subst h0; exact ⟨h1, by simp⟩
    have ih' := ih (by omega) (fun u a b => hT u a (by omega)) (fun u a b => hnc u a (by omega))
    obtain ⟨hJ, hJ1, hJ2⟩ := hstep _ (e t) ih'.1 (hT (t + 1) (by omega) le_rfl)
      (hnc t (by omega) (by omega))
    refine ⟨hJ, ?_⟩
    have hsub : (Finset.Ico t₁ (t + 1)).filter (fun u => e u = .step p) ⊆
        (if e t = .step p then {t} else ∅) ∪ (Finset.Ico t₁ t).filter (fun u => e u = .step p) := by
      intro u hu
      simp only [Finset.mem_filter, Finset.mem_Ico] at hu
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ico]
      by_cases hut : u = t
      · subst hut; left; rw [if_pos hu.2]; simp
      · right; exact ⟨⟨hu.1.1, by omega⟩, hu.2⟩
    have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    have := ih'.2
    rw [exec_succ]
    split_ifs at hc with he
    · have := hJ2 he; simp at hc; omega
    · simp at hc; omega

/-- Levels inside `Recover()`. -/
def recLvl (k : PC P) : ℕ :=
  match k with
  | .r16 => 1
  | .r18 => 2
  | _ => 0

/-- **Lemma 2.12 (Wait-free recovery)**, with bound 3: a process that is in `Recover()` and takes
3 steps without crashing has left `Recover()` by then. -/
theorem wait_free_recovery (e : ℕ → Ev P) (p : P) (t₁ : ℕ) (h1 : (exec e t₁).pc p |>.IsRecover)
    (t : ℕ) (ht : t₁ ≤ t) (hnc : ∀ u, t₁ ≤ u → u < t → e u ≠ .crash p)
    (hsteps : 3 ≤ ((Finset.Ico t₁ t).filter (fun u => e u = .step p)).card) :
    ∃ u, t₁ < u ∧ u ≤ t ∧ ¬ ((exec e u).pc p).IsRecover := by
  by_contra hno
  push Not at hno
  have key := progress_steps e p (fun s => (s.pc p).IsRecover) (fun s => ¬ (s.pc p).IsRecover)
    (fun s => recLvl (s.pc p)) ?_ t₁ h1 t ht (fun u a b => by simpa using hno u a b) hnc
  · have : recLvl ((exec e t).pc p) ≤ 2 := by
      unfold recLvl; split <;> omega
    omega
  · intro s ev hJ hTg hev
    simp only [not_not] at hTg
    refine ⟨hTg, ?_⟩
    cases ev with
    | crash q =>
      have hq : q ≠ p := by rintro rfl; exact hev rfl
      obtain ⟨a, -, -⟩ := crash_other s hq
      simp only [Cfg.next, a]; exact ⟨le_rfl, by simp⟩
    | step q =>
      by_cases hq : q = p
      · subst hq
        cases hk : s.pc q <;> simp only [PC.IsRecover, hk] at hJ
        all_goals
          simp only [Cfg.next, Cfg.step, hk] at hTg ⊢
          (try split_ifs at hTg ⊢) <;> simp_all [Cfg.setPc, PC.IsRecover, recLvl]
      · simp only [Cfg.next, step_pc_other s hq]
        exact ⟨le_rfl, fun h => by cases h; exact absurd rfl hq⟩

/-- The program counters "after the first and before the last shared-memory operation of
`Exit()`" (after line 9, before line 12 has been executed). -/
def PC.InExitBody {P : Type} : PC P → Prop
  | .x10 | .x12 => True
  | .m34 .ex | .m35 .ex _ | .m36 .ex _ _ | .m38 .ex _ _ _ | .m40 .ex _ _ | .m41 .ex _ _
  | .m42 .ex _ | .m46 .ex _ | .m47 .ex _ | .m48 .ex _ => True
  | _ => False

lemma X_of_inExitBody {s : Cfg P} {g : Ghost P} (hI : Inv s g) {p : P}
    (h : (s.pc p).InExitBody) : s.X p = true := by
  have hL := hI.loc p
  cases hk : s.pc p with
  | x10 => simpa [LI, hk] using hL
  | x12 => simp only [LI, hk] at hL; exact hL.1
  | m34 r | m35 r _ | m36 r _ _ | m38 r _ _ _ | m40 r _ _ | m41 r _ _ | m42 r _ | m46 r _
  | m47 r _ | m48 r _ =>
    rw [hk] at h
    cases r with
    | wr w => exact h.elim
    | ex => simp only [LI, hk, RetInv] at hL; first | exact hL.1 | exact hL.1.1
  | _ => rw [hk] at h; exact h.elim

/-- **Lemma 2.15 (Wait-free recovery to exit)**, with bound 2: if `p` crashes after its first
and before its last shared-memory operation of `Exit()`, then it is back at the beginning of
`Exit()` (line 9) as soon as it has taken 2 steps without crashing. -/
theorem wait_free_recovery_to_exit (e : ℕ → Ev P) (p : P) (t₀ : ℕ)
    (hex : ((exec e t₀).pc p).InExitBody) (hcr : e t₀ = .crash p)
    (t : ℕ) (ht : t₀ + 1 ≤ t) (hnc : ∀ u, t₀ + 1 ≤ u → u < t → e u ≠ .crash p)
    (hsteps : 2 ≤ ((Finset.Ico (t₀ + 1) t).filter (fun u => e u = .step p)).card) :
    ∃ u, t₀ + 1 < u ∧ u ≤ t ∧ (exec e u).pc p = .x9 := by
  have hX := X_of_inExitBody (inv_exec e t₀) hex
  have hne : (exec e t₀).pc p ≠ .rem := by
    intro h; rw [h] at hex; exact hex
  have h1 : (exec e (t₀ + 1)).pc p = .r15 ∧ (exec e (t₀ + 1)).X p = true := by
    simp [exec_succ, hcr, Cfg.next, Cfg.crash, hne, hX]
  by_contra hno
  push Not at hno
  let J : Cfg P → Prop := fun s => (s.pc p = .r15 ∨ s.pc p = .r16) ∧ s.X p = true
  have key := progress_steps e p J (fun s => s.pc p = .x9)
    (fun s => recLvl (s.pc p)) ?_ (t₀ + 1) ⟨Or.inl h1.1, h1.2⟩ t ht
    (fun u a b => hno u a b) hnc
  · have : recLvl ((exec e t).pc p) ≤ 1 := by
      rcases key.1.1 with h | h <;> simp [h, recLvl]
    omega
  · intro s ev hJ hTg hev
    obtain ⟨hpc, hXs⟩ := hJ
    cases ev with
    | crash q =>
      have hq : q ≠ p := by rintro rfl; exact hev rfl
      obtain ⟨a, b, -⟩ := crash_other s hq
      simp only [Cfg.next, J, a, b]; exact ⟨⟨hpc, hXs⟩, le_rfl, by simp⟩
    | step q =>
      by_cases hq : q = p
      · subst hq
        rcases hpc with hk | hk
        · simp [Cfg.next, Cfg.step, hk, J, hXs, recLvl]
        · simp [Cfg.next, Cfg.step, hk, hXs] at hTg
      · simp only [Cfg.next, J, step_pc_other s hq, step_X_other s hq]
        exact ⟨⟨hpc, hXs⟩, le_rfl, fun h => by cases h; exact absurd rfl hq⟩

end Podc.RecoverableMutexRMR
