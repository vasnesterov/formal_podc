import Papers.PODC2019.AbortableMutexAmortized.RMR

/-!
# Theorem 5.4: amortized `O(1)` RMRs per attempt, `O(1)` Exit, Fast Abort

* `theorem_5_4_dsm`: in DSM, every finite execution from the initial configuration incurs at most
  `8 · (number of attempts)` RMRs.
* `theorem_5_4_cc`: in CC (initially empty caches), at most `12 · (number of attempts)` RMRs.
* `theorem_5_4_exit`: a process in the CS (line 7) is back in the Remainder after at most 2 own
  steps, whatever the other processes do; every step costs at most one RMR in both models
  (`dsmCost_le_one`, `ccCost_le_one`).
* `theorem_5_4_fastAbort`: a process outside the Remainder that only takes aborting steps is back
  in the Remainder after at most 5 own steps, whatever the other processes do.

An *attempt* is a step taken at line 1 (the start of the Try section).

The proof follows the paper's ("lines outside the loop are executed at most once per attempt"),
made precise with the total potential `Θ = Φ + Σ_p c(PC_p)`, where `c(PC_p)` is the amortized budget
the current attempt of `p` still has; every step except a line-1 step has
`cost + ΔΘ ≤ 0`, and a line-1 step has `cost + ΔΘ ≤ K`.
-/

namespace Podc.AbortableMutexAmortized

variable {n : ℕ}

/-- A step of `p` does not change the program counter of any other process. -/
theorem step_pc_ne (s : State n) {p q : Fin n} (ab : Bool) (hq : q ≠ p) :
    (step s p ab).pc q = s.pc q := by
  cases hpc : s.pc p <;> cases ab <;>
    simp [step, hpc, fasPred, line9, wake, hq] <;> split_ifs <;> simp [hq]

/-! ## Executions with costs -/

/-- Number of attempts in the schedule `ls` from `s`: steps taken at line 1. -/
def attempts : State n → List (Fin n × Bool) → ℕ
  | _, [] => 0
  | s, l :: ls => (if s.pc l.1 = .l1 then 1 else 0) + attempts (step s l.1 l.2) ls

/-- Total DSM cost (number of RMRs) of the schedule `ls` from `s`. -/
def dsmTotal (home : Var n → Option (Fin n)) : State n → List (Fin n × Bool) → ℕ
  | _, [] => 0
  | s, l :: ls => dsmCost home s l.1 l.2 + dsmTotal home (step s l.1 l.2) ls

/-- Total CC cost (number of RMRs) of the schedule `ls` from `s` with caches `C`. -/
def ccTotal : State n → Cache n → List (Fin n × Bool) → ℕ
  | _, _, [] => 0
  | s, C, l :: ls => ccCost C l.1 (access s l.1 l.2) +
      ccTotal (step s l.1 l.2) (ccUpd C l.1 (access s l.1 l.2)) ls

/-! ## Remaining budgets -/

/-- Remaining amortized DSM budget of an attempt at line `pc`. -/
def cD : PC → ℤ
  | .l1 => 0 | .l2 => 7 | .l3 => 6 | .l4 | .l5 | .l6 | .l9 => 5
  | .l7 => 3 | .l8 => 2 | .l10 => 4 | .l11 => 2

/-- Remaining amortized CC budget of an attempt at line `pc`. -/
def cC : PC → ℤ
  | .l1 => 0 | .l2 => 10 | .l3 => 9 | .l4 | .l5 | .l6 | .l9 => 8
  | .l7 => 6 | .l8 => 5 | .l10 => 7 | .l11 => 5

theorem cD_nonneg (pc : PC) : 0 ≤ cD pc := by cases pc <;> simp [cD]
theorem cC_nonneg (pc : PC) : 0 ≤ cC pc := by cases pc <;> simp [cC]

theorem cD_step (s : State n) (p : Fin n) (ab : Bool) :
    boundD (lineOf s p ab) + cD ((step s p ab).pc p) - cD (s.pc p) ≤
      if s.pc p = .l1 then 8 else 0 := by
  cases hpc : s.pc p <;> cases ab <;>
    simp only [step, hpc, lineOf, fasPred, line9, wake, Bool.false_eq_true, ite_true, ite_false] <;>
    generalize s.node (s.pred p) = w1 <;> generalize s.node (s.mynode p) = w2 <;>
    generalize s.go p = g <;> cases w1 <;> cases w2 <;> cases g <;>
    simp [loopPC, boundD, cD, hpc] <;> split_ifs <;> simp

theorem cC_step (s : State n) (p : Fin n) (ab : Bool) :
    boundC (lineOf s p ab) + ind (s.pc p = .l1) + cC ((step s p ab).pc p) - cC (s.pc p) ≤
      if s.pc p = .l1 then 12 else 0 := by
  cases hpc : s.pc p <;> cases ab <;>
    simp only [step, hpc, lineOf, fasPred, line9, wake, Bool.false_eq_true, ite_true, ite_false] <;>
    generalize s.node (s.pred p) = w1 <;> generalize s.node (s.mynode p) = w2 <;>
    generalize s.go p = g <;> cases w1 <;> cases w2 <;> cases g <;>
    simp [loopPC, boundC, cC, hpc, ind] <;> split_ifs <;> simp

theorem sum_c_step (c : PC → ℤ) (s : State n) (p : Fin n) (ab : Bool) :
    ∑ q, c ((step s p ab).pc q) - ∑ q, c (s.pc q) = c ((step s p ab).pc p) - c (s.pc p) :=
  sum_sub_eq_of_ne p fun q hq => by rw [step_pc_ne s ab hq]

/-! ## DSM -/

/-- Total DSM potential: `ΦDSM` plus the remaining budgets of the current attempts. -/
def ThetaD (s : State n) : ℤ := PhiD s + ∑ q, cD (s.pc q)

theorem PhiD_nonneg (s : State n) : 0 ≤ PhiD s :=
  Finset.sum_nonneg fun q _ => by
    unfold phiD; linarith [ind_nonneg (s.go q = true), ind_nonneg (s.pc q = .l6),
      ind_nonneg (abd s q)]

theorem ThetaD_nonneg (s : State n) : 0 ≤ ThetaD s := by
  unfold ThetaD
  linarith [PhiD_nonneg s, Finset.sum_nonneg fun q (_ : q ∈ Finset.univ) => cD_nonneg (s.pc q)]

theorem ThetaD_init : ThetaD (init : State n) = 0 := by
  simp [ThetaD, PhiD, phiD, init, abd, ind, cD]

theorem amortTheta_D {home : Var n → Option (Fin n)} (hhome : ∀ q, home (.go q) = some q)
    {s : State n} (h : Inv s) (p : Fin n) (ab : Bool) :
    (dsmCost home s p ab : ℤ) + ThetaD (step s p ab) - ThetaD s ≤
      if s.pc p = .l1 then 8 else 0 := by
  have h1 := lemma_5_2 hhome h p ab
  have h2 := cD_step s p ab
  have h3 := sum_c_step cD s p ab
  unfold amortD at h1; unfold ThetaD; linarith

theorem dsmTotal_le {home : Var n → Option (Fin n)} (hhome : ∀ q, home (.go q) = some q)
    {s : State n} (hs : Reachable s) (ls : List (Fin n × Bool)) :
    (dsmTotal home s ls : ℤ) + ThetaD (run s ls) ≤ ThetaD s + 8 * attempts s ls := by
  induction ls generalizing s with
  | nil => simp [dsmTotal, run, attempts]
  | cons l ls ih =>
    have h1 := ih (hs.step l.1 l.2)
    have hA := amortTheta_D hhome hs.inv l.1 l.2
    simp only [dsmTotal, run, attempts]
    split_ifs at hA ⊢ <;> push_cast <;> linarith

/-- **Theorem 5.4** (amortized RMR complexity, DSM): if every `go_p` lies in `p`'s memory
partition (nodes and `tail` anywhere), every finite execution of Algorithm 1 from the initial
configuration incurs at most `8` RMRs per attempt (an attempt starts with a step at line 1). -/
theorem theorem_5_4_dsm {home : Var n → Option (Fin n)} (hhome : ∀ q, home (.go q) = some q)
    (ls : List (Fin n × Bool)) : dsmTotal home init ls ≤ 8 * attempts init ls := by
  have h1 := dsmTotal_le hhome Reachable.init ls
  rw [ThetaD_init] at h1
  have h2 := ThetaD_nonneg (run init ls)
  have : (dsmTotal home init ls : ℤ) ≤ 8 * attempts init ls := by linarith
  exact_mod_cast this

/-! ## CC -/

/-- `ΦCC` with `1{notcached(p)}` replaced by `1{notcached(p) ∧ PC_p ≠ 1}` (the paper: "at the cost
of charging one unit to a process that is newly joining the protocol, we think of `go_p` as
initially residing in `p`'s cache"). -/
def phiC' (s : State n) (C : Cache n) (q : Fin n) : ℤ :=
  3 * ind (s.go q = true) + ind (s.pc q = .l6) + ind (abd s q) +
    ind (C q (.go q) = false ∧ s.pc q ≠ .l1)

/-- See `phiC'`. -/
def PhiC' (s : State n) (C : Cache n) : ℤ := ∑ q, phiC' s C q

/-- The difference `ΦCC − ΦCC'`. -/
def N1 (s : State n) (C : Cache n) : ℤ := ∑ q, ind (C q (.go q) = false ∧ s.pc q = .l1)

theorem PhiC_eq' (s : State n) (C : Cache n) : PhiC s C = PhiC' s C + N1 s C := by
  unfold PhiC PhiC' N1
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q _ => ?_
  unfold phiC phiC'
  have : ind (C q (.go q) = false) =
      ind (C q (.go q) = false ∧ s.pc q ≠ .l1) + ind (C q (.go q) = false ∧ s.pc q = .l1) := by
    unfold ind; split_ifs <;> simp_all
  rw [this]; ring

theorem ccUpd_false {C : Cache n} {p q : Fin n} (a : Var n × Bool) {y : Var n} (hq : q ≠ p)
    (h : C q y = false) : ccUpd C p a q y = false := by
  unfold ccUpd; split_ifs <;> simp [hq, h]

theorem N1_step (s : State n) (C : Cache n) (p : Fin n) (ab : Bool) :
    N1 s C - N1 (step s p ab) (ccUpd C p (access s p ab)) ≤ ind (s.pc p = .l1) := by
  have := sum_sub_le (g := fun q => ind (C q (.go q) = false ∧ s.pc q = .l1))
    (f := fun q => ind (ccUpd C p (access s p ab) q (.go q) = false ∧ (step s p ab).pc q = .l1))
    (b := fun q => if q = p then ind (s.pc p = .l1) else 0) fun q => by
      by_cases hq : q = p
      · subst hq
        simp only [ite_true]
        linarith [ind_mono (fun (h : C q (.go q) = false ∧ s.pc q = .l1) => h.2),
          ind_nonneg (ccUpd C q (access s q ab) q (.go q) = false ∧ (step s q ab).pc q = .l1)]
      · simp only [hq, ite_false]
        linarith [ind_mono (fun (h : C q (.go q) = false ∧ s.pc q = .l1) =>
          (⟨ccUpd_false _ hq h.1, by rw [step_pc_ne s ab hq]; exact h.2⟩ :
            ccUpd C p (access s p ab) q (.go q) = false ∧ (step s p ab).pc q = .l1))]
  simpa [N1] using this

/-- Total CC potential: `ΦCC'` plus the remaining budgets of the current attempts. -/
def ThetaC (s : State n) (C : Cache n) : ℤ := PhiC' s C + ∑ q, cC (s.pc q)

theorem ThetaC_nonneg (s : State n) (C : Cache n) : 0 ≤ ThetaC s C := by
  unfold ThetaC PhiC'
  have h1 : 0 ≤ ∑ q, phiC' s C q := Finset.sum_nonneg fun q _ => by
    unfold phiC'; linarith [ind_nonneg (s.go q = true), ind_nonneg (s.pc q = .l6),
      ind_nonneg (abd s q), ind_nonneg (C q (.go q) = false ∧ s.pc q ≠ .l1)]
  linarith [Finset.sum_nonneg fun q (_ : q ∈ Finset.univ) => cC_nonneg (s.pc q)]

theorem ThetaC_init : ThetaC (init : State n) emptyCache = 0 := by
  simp [ThetaC, PhiC', phiC', init, abd, ind, cC]

theorem amortTheta_C {s : State n} (h : Inv s) (C : Cache n) (p : Fin n) (ab : Bool) :
    (ccCost C p (access s p ab) : ℤ) + ThetaC (step s p ab) (ccUpd C p (access s p ab)) -
      ThetaC s C ≤ if s.pc p = .l1 then 12 else 0 := by
  have h1 := lemma_5_3 h C p ab
  have h2 := cC_step s p ab
  have h3 := sum_c_step cC s p ab
  have h4 := N1_step s C p ab
  unfold amortC at h1; rw [PhiC_eq', PhiC_eq'] at h1
  unfold ThetaC; linarith

theorem ccTotal_le {s : State n} (hs : Reachable s) (C : Cache n) (ls : List (Fin n × Bool)) :
    ∃ C', (ccTotal s C ls : ℤ) + ThetaC (run s ls) C' ≤ ThetaC s C + 12 * attempts s ls := by
  induction ls generalizing s C with
  | nil => exact ⟨C, by simp [ccTotal, run, attempts]⟩
  | cons l ls ih =>
    obtain ⟨C', h1⟩ := ih (hs.step l.1 l.2) (ccUpd C l.1 (access s l.1 l.2))
    have hA := amortTheta_C hs.inv C l.1 l.2
    refine ⟨C', ?_⟩
    simp only [ccTotal, run, attempts]
    split_ifs at hA ⊢ <;> push_cast <;> linarith

/-- **Theorem 5.4** (amortized RMR complexity, CC): with initially empty caches, every finite
execution of Algorithm 1 from the initial configuration incurs at most `12` RMRs per attempt
(an attempt starts with a step at line 1). -/
theorem theorem_5_4_cc (ls : List (Fin n × Bool)) :
    ccTotal init emptyCache ls ≤ 12 * attempts init ls := by
  obtain ⟨C', h1⟩ := ccTotal_le Reachable.init emptyCache ls
  rw [ThetaC_init] at h1
  have h2 := ThetaC_nonneg (run init ls) C'
  have : (ccTotal init emptyCache ls : ℤ) ≤ 12 * attempts init ls := by linarith
  exact_mod_cast this

/-! ## Worst-case Exit and Fast Abort -/

/-- Number of own steps (aborting steps in the Try section, any steps in the Exit and Abort
sections) a process at line `pc` still needs to reach the Remainder section. -/
def abortMeasure : PC → ℕ
  | .l1 => 0 | .l2 => 5 | .l3 => 4 | .l4 | .l5 | .l6 | .l9 => 3
  | .l7 | .l10 => 2 | .l8 | .l11 => 1

theorem abortMeasure_le (pc : PC) : abortMeasure pc ≤ 5 := by cases pc <;> simp [abortMeasure]

/-- An aborting step of a process outside the Remainder decreases `abortMeasure`. -/
theorem abort_step (s : State n) (p : Fin n) (hpc : s.pc p ≠ .l1) :
    abortMeasure ((step s p true).pc p) < abortMeasure (s.pc p) := by
  cases hpc' : s.pc p <;>
    simp only [step, hpc', fasPred, line9, wake, ite_true] <;>
    generalize s.node (s.pred p) = w1 <;> generalize s.node (s.mynode p) = w2 <;>
    cases w1 <;> cases w2 <;>
    simp_all [loopPC, abortMeasure]

/-- A step of a process in the Exit section (lines 7, 8) keeps it in the Exit section or brings
it to the Remainder, and decreases `abortMeasure`. -/
theorem exit_step (s : State n) (p : Fin n) (ab : Bool) (hpc : s.pc p = .l7 ∨ s.pc p = .l8) :
    ((step s p ab).pc p = .l1 ∨ (step s p ab).pc p = .l7 ∨ (step s p ab).pc p = .l8) ∧
      abortMeasure ((step s p ab).pc p) < abortMeasure (s.pc p) := by
  rcases hpc with hpc | hpc <;> simp [step, hpc, wake, abortMeasure] <;> split_ifs <;> simp <;> tauto

/-- If every own step of `p` is allowed (`A`) and strictly decreases `μ` while staying in the
region `R`, and other processes' steps do not touch `p`'s program counter, then `p` takes fewer
than `μ (PC_p)` steps while staying outside the Remainder. -/
theorem run_own_lt (μ : PC → ℕ) (R : PC → Prop) (A : Bool → Prop) {p : Fin n}
    (hdec : ∀ (s : State n) ab, A ab → R (s.pc p) → s.pc p ≠ .l1 →
      R ((step s p ab).pc p) ∧ μ ((step s p ab).pc p) < μ (s.pc p))
    (hpos : ∀ pc, R pc → pc ≠ .l1 → 0 < μ pc) :
    ∀ (s : State n) (ls : List (Fin n × Bool)), (∀ l ∈ ls, l.1 = p → A l.2) → R (s.pc p) →
      (∀ k ≤ ls.length, (run s (ls.take k)).pc p ≠ .l1) →
      ls.countP (fun l => l.1 = p) < μ (s.pc p) := by
  intro s ls
  induction ls generalizing s with
  | nil => intro _ hR hn; simpa using hpos _ hR (by simpa [run] using hn 0 (by simp))
  | cons l ls ih =>
    intro hA hR hn
    have h0 : s.pc p ≠ .l1 := by simpa [run] using hn 0 (by simp)
    have hn' : ∀ k ≤ ls.length, (run (step s l.1 l.2) (ls.take k)).pc p ≠ .l1 := fun k hk => by
      simpa [run] using hn (k + 1) (by simp; omega)
    have hA' : ∀ l' ∈ ls, l'.1 = p → A l'.2 := fun l' hl' => hA l' (by simp [hl'])
    rw [List.countP_cons]
    by_cases hl : l.1 = p
    · obtain ⟨q, b⟩ := l
      simp only at hl; subst hl
      obtain ⟨hR', hlt⟩ := hdec s b (hA (q, b) (by simp) rfl) hR h0
      have := ih (step s q b) hA' hR' hn'
      simp; omega
    · have he : (step s l.1 l.2).pc p = s.pc p := step_pc_ne s l.2 (Ne.symm hl)
      have := ih _ hA' (he ▸ hR) hn'
      rw [he] at this
      simp [hl]; omega

/-- **Theorem 5.4** (worst-case `O(1)` Exit): a process in the CS (at line 7, about to execute
the Exit section) is back in the Remainder section after at most 2 of its own steps, whatever
the other processes do; each step costs at most one RMR in both models (`dsmCost_le_one`,
`ccCost_le_one`). -/
theorem theorem_5_4_exit (s : State n) (p : Fin n) (hpc : s.pc p = .l7)
    (ls : List (Fin n × Bool)) (h2 : 2 ≤ ls.countP (fun l => l.1 = p)) :
    ∃ k ≤ ls.length, (run s (ls.take k)).pc p = .l1 := by
  by_contra hne
  push Not at hne
  have := run_own_lt abortMeasure (fun pc => pc = .l1 ∨ pc = .l7 ∨ pc = .l8) (fun _ => True)
    (fun s ab _ hR h1 => by
      have hpc : s.pc p = .l7 ∨ s.pc p = .l8 := by tauto
      exact exit_step s p ab hpc)
    (fun pc hR h1 => by rcases hR with h | h | h <;> simp_all [abortMeasure])
    s ls (fun _ _ _ => trivial) (Or.inr (Or.inl hpc)) hne
  rw [hpc] at this; simp [abortMeasure] at this; omega

/-- **Theorem 5.4** (Fast Abort): a process outside the Remainder section that receives the
abort signal (all of its steps are aborting steps) is back in the Remainder section after at
most 5 of its own steps, whatever the other processes do (each step costs at most one RMR in
both models). -/
theorem theorem_5_4_fastAbort (s : State n) (p : Fin n) (ls : List (Fin n × Bool))
    (hab : ∀ l ∈ ls, l.1 = p → l.2 = true) (h5 : 5 ≤ ls.countP (fun l => l.1 = p)) :
    ∃ k ≤ ls.length, (run s (ls.take k)).pc p = .l1 := by
  by_contra hne
  push Not at hne
  have := run_own_lt abortMeasure (fun _ => True) (fun ab => ab = true)
    (fun s ab hab _ h1 => by subst hab; exact ⟨trivial, abort_step s p h1⟩)
    (fun pc _ h1 => by cases pc <;> simp_all [abortMeasure])
    s ls hab trivial hne
  have := abortMeasure_le (s.pc p)
  omega

end Podc.AbortableMutexAmortized
