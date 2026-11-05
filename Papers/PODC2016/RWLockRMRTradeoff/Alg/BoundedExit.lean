import Papers.PODC2016.RWLockRMRTradeoff.Alg.Safety

/-!
# Bounded Exit for the algorithms `A_f` (Lemma 10 of Hendler, PODC 2016)

The exit code of a reader (lines 40–54) and of the writer (lines 25–26; `WL.Exit` is omitted in
the single-writer model) contains no waiting, so a process that leaves the critical section
returns to the remainder section within a bounded number of its own steps, whatever the other
processes do. This holds for every variant (`ReadOrder`, `Line47`) and every group assignment.

We measure the remaining exit steps by `RLocal.exitRank` / `WLocal.exitRank` (`none` outside the
exit section and the CS) and show that each own step decreases the rank and other processes' steps
do not change it.
-/

namespace Podc.RWLockRMRTradeoff.Alg

variable {n G : ℕ}

/-- Remaining steps of a reader in the critical section or its exit section (at most 5:
lines 40, 41, 51 (two reads), 52). -/
def RLocal.exitRank (l : RLocal) : Option ℕ :=
  match l.pc with
  | .rem => some 0
  | .cs => some 5
  | .l41 => some 4
  | .l43 => some 2
  | .l44 => some 1
  | .l51a => if l.ret36 then none else some 3
  | .l51b => if l.ret36 then none else some 2
  | .l52 => if l.ret36 then none else some 1
  | _ => none

/-- Remaining steps of the writer in the critical section or its exit section (lines 25, 26). -/
def WLocal.exitRank (w : WLocal G) : Option ℕ :=
  match w.pc with
  | .rem => some 0
  | .cs => some 2
  | .l26 => some 1
  | _ => none

lemma RLocal.exitRank_zero {l : RLocal} (h : l.exitRank = some 0) : l.pc = .rem := by
  unfold RLocal.exitRank at h
  split at h <;> (try split at h) <;> simp_all

lemma WLocal.exitRank_zero {w : WLocal G} (h : w.exitRank = some 0) : w.pc = .rem := by
  unfold WLocal.exitRank at h
  split at h <;> simp_all

/-- An own step of a reader in its CS or exit section decreases its exit rank. -/
lemma rstep_exitRank (cfg : Cfg n G) (s : State n G) (p : Fin n) {k : ℕ}
    (h : (s.r p).exitRank = some (k + 1)) :
    ∃ k', ((rstep cfg p s).r p).exitRank = some k' ∧ k' ≤ k := by
  revert h
  rsplit (
    intro h
    simp only [RLocal.exitRank, hpc, Function.update_self] at h ⊢
    (try split_ifs at h ⊢) <;> simp_all)

lemma step_exitRank_other (cfg : Cfg n G) (s : State n G) (p : Fin n) (who : Who n)
    (h : who ≠ .reader p) : (step cfg who s).r p = s.r p := by
  cases who with
  | writer => exact congrFun (wstep_r s) p
  | reader q => exact rstep_r_ne cfg s q p (fun e => h (e ▸ rfl))

/-- **Lemma 10 (Bounded Exit), readers.** If reader `p` is in the critical section or its exit
section with exit rank `k` (`k ≤ 5`), then in every execution fragment in which `p` takes at least
`k` steps, `p` reaches the remainder section (after some prefix of the fragment). -/
theorem boundedExit_reader (cfg : Cfg n G) (p : Fin n) :
    ∀ (sched : List (Who n)) (s : State n G) (k : ℕ), (s.r p).exitRank = some k →
      k ≤ sched.count (.reader p) →
      ∃ l₁ l₂, sched = l₁ ++ l₂ ∧ ((run cfg l₁ s).r p).pc = .rem := by
  intro sched
  induction sched with
  | nil =>
    intro s k hk hc
    simp only [List.count_nil, Nat.le_zero] at hc
    subst hc
    exact ⟨[], [], rfl, RLocal.exitRank_zero hk⟩
  | cons who rest ih =>
    intro s k hk hc
    cases k with
    | zero => exact ⟨[], who :: rest, rfl, RLocal.exitRank_zero hk⟩
    | succ k =>
      by_cases hw : who = .reader p
      · subst hw
        obtain ⟨k', hk', hle⟩ := rstep_exitRank cfg s p hk
        rw [List.count_cons_self] at hc
        obtain ⟨l₁, l₂, h1, h2⟩ := ih (rstep cfg p s) k' hk' (by omega)
        exact ⟨.reader p :: l₁, l₂, by rw [h1]; rfl, h2⟩
      · rw [List.count_cons_of_ne hw] at hc
        have hk' : ((step cfg who s).r p).exitRank = some (k + 1) := by
          rw [step_exitRank_other cfg s p who hw]; exact hk
        obtain ⟨l₁, l₂, h1, h2⟩ := ih (step cfg who s) (k + 1) hk' hc
        exact ⟨who :: l₁, l₂, by rw [h1]; rfl, h2⟩

/-- An own step of the writer in its CS or exit section decreases its exit rank. -/
lemma wstep_exitRank (s : State n G) {k : ℕ} (h : s.w.exitRank = some (k + 1)) :
    ∃ k', (wstep s).w.exitRank = some k' ∧ k' ≤ k := by
  revert h
  wsplit (intro h; simp_all [WLocal.exitRank]; try omega)

lemma step_w_other (cfg : Cfg n G) (s : State n G) (p : Fin n) :
    (step cfg (.reader p) s).w = s.w := rstep_w cfg p s

/-- **Lemma 10 (Bounded Exit), writer** (without `WL.Exit`, which the single-writer model omits):
a writer in the CS or its exit section with exit rank `k ≤ 2` reaches the remainder section in
every execution fragment in which it takes at least `k` steps. -/
theorem boundedExit_writer (cfg : Cfg n G) :
    ∀ (sched : List (Who n)) (s : State n G) (k : ℕ), s.w.exitRank = some k →
      k ≤ sched.count .writer →
      ∃ l₁ l₂, sched = l₁ ++ l₂ ∧ (run cfg l₁ s).w.pc = .rem := by
  intro sched
  induction sched with
  | nil =>
    intro s k hk hc
    simp only [List.count_nil, Nat.le_zero] at hc
    subst hc
    exact ⟨[], [], rfl, WLocal.exitRank_zero hk⟩
  | cons who rest ih =>
    intro s k hk hc
    cases k with
    | zero => exact ⟨[], who :: rest, rfl, WLocal.exitRank_zero hk⟩
    | succ k =>
      cases who with
      | writer =>
        obtain ⟨k', hk', hle⟩ := wstep_exitRank s hk
        rw [List.count_cons_self] at hc
        obtain ⟨l₁, l₂, h1, h2⟩ := ih (wstep s) k' hk' (by omega)
        exact ⟨.writer :: l₁, l₂, by rw [h1]; rfl, h2⟩
      | reader q =>
        rw [List.count_cons_of_ne (by simp)] at hc
        have hk' : (step cfg (.reader q) s).w.exitRank = some (k + 1) := by
          rw [step_w_other]; exact hk
        obtain ⟨l₁, l₂, h1, h2⟩ := ih (step cfg (.reader q) s) (k + 1) hk' hc
        exact ⟨.reader q :: l₁, l₂, by rw [h1]; rfl, h2⟩

/-- A reader in the critical section has exit rank 5: it returns to the remainder section within
5 of its own steps. -/
theorem boundedExit_reader_cs (cfg : Cfg n G) (p : Fin n) (s : State n G)
    (h : (s.r p).pc = .cs) (sched : List (Who n)) (hc : 5 ≤ sched.count (.reader p)) :
    ∃ l₁ l₂, sched = l₁ ++ l₂ ∧ ((run cfg l₁ s).r p).pc = .rem :=
  boundedExit_reader cfg p sched s 5 (by simp [RLocal.exitRank, h]) hc

/-- The writer in the critical section returns to the remainder section within 2 of its own
steps. -/
theorem boundedExit_writer_cs (cfg : Cfg n G) (s : State n G) (h : s.w.pc = .cs)
    (sched : List (Who n)) (hc : 2 ≤ sched.count .writer) :
    ∃ l₁ l₂, sched = l₁ ++ l₂ ∧ (run cfg l₁ s).w.pc = .rem :=
  boundedExit_writer cfg sched s 2 (by simp [WLocal.exitRank, h]) hc

end Podc.RWLockRMRTradeoff.Alg
