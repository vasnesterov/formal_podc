import Papers.PODC2010.GroupMutexLogRMR.Model

/-!
# A deadlock of the final algorithm (Figure 3): starvation freedom fails

Two processes, two sessions `0, 1` (`S = (0,0,0)` initially).

1. `p₀` (session 0) runs alone through its whole attempt: it joins side 0 (lines 1.5–1.6,
   because `S = (0, 0̄̄, −)`), enters and leaves the CS, and stops just before line 16.6, i.e.
   after its `LL(Ex)` at line 16.3. It is still counted in `C[0,0]`.
2. `p₁` (session 0) runs a whole attempt: it joins side 0 as well and passes line 8 (`Out[0] = 0`).
   At lines 9–10 it finds `Ex = false` and performs a *successful* `SC(Ex, false)`, which kills
   `p₀`'s link on `Ex`. In its exit section it finds `C[0,0] = 1` (because of `p₀`) at line 16.8 and
   returns to the remainder section without promoting anybody.
3. `p₁` starts a new attempt with session 1 (side 1). In `Promote-Try` it finds `C[0,0] = 1` and
   does not touch `S`; it waits at line 8 for `Out[1] = 1`.
4. `p₀` finishes: `C[0,0] = 0`, `Min(Q) = (1,1)`, so it tries `SC(Ex, 0)` at line 16.9 — which fails
   because of `p₁`'s `SC` at line 10. `p₀` returns to the remainder section.

Now `S = (0,0,0)`, `Out[1] = 0`, and the only active process `p₁` waits at line 8 forever: nobody
will ever write `Out[1]`. The paper's proof of Claim 4 (case "the successful SC was performed by
some process at Line 10") assumes that SC happened after `q[16.6]`; here it happened between
`q[16.3]` and `q[16.6]`.
-/

namespace Podc.GroupMutexLogRMR

open Cfg

/-- The events of the deadlocking execution. -/
def deadSched : List (Ev 2 (Fin 2)) :=
  -- 1. p₀ (session 0): start, lines 1.1 … 16.5 (28 steps); now at 16.6
  [(0, 0)] ++ List.replicate 28 (0, 0) ++
  -- 2. p₁ (session 0): a whole attempt (start + 1.1 … 16.8)
  [(1, 0)] ++ List.replicate 31 (1, 0) ++
  -- 3. p₁ (session 1): start + 1.1, 1.2, 1.3, 1.4, 1.5, 1.7, 2, 3, 4, 5.1, 5.2, 5.3, 6
  [(1, 1)] ++ List.replicate 13 (1, 1) ++
  -- 4. p₀: 16.6, 16.7, 16.8, 16.9 (failed SC)
  List.replicate 4 (0, 0)

/-- The deadlocked configuration. -/
@[irreducible] def deadCfg : Cfg 2 (Fin 2) := run (Cfg.init 2 0) deadSched


theorem deadCfg_reachable : Reachable 0 deadCfg := ⟨deadSched, by unfold deadCfg; rfl⟩

theorem deadCfg_p0 : (deadCfg.loc 0).pc = .rem := by decide +kernel
theorem deadCfg_p1 : (deadCfg.loc 1).pc = .l8 ∧ (deadCfg.loc 1).s = 1 ∧ (deadCfg.loc 1).d = true := by
  decide +kernel
theorem deadCfg_out : deadCfg.Out 1 = false := by decide +kernel
theorem deadCfg_S : deadCfg.S = (0, false, 0) := by decide +kernel
theorem deadCfg_C : deadCfg.C 0 false = 0 ∧ deadCfg.C 0 true = 0 := by decide +kernel
theorem deadCfg_minQ : minQ deadCfg.Q = some (1, true) := by decide +kernel

/-- A process waiting at line 8 whose `Out` flag is not its side does not change the configuration. -/
theorem step_l8_stuck {n : ℕ} {J : Type} [DecidableEq J] (c : Cfg n J) (p : Fin n) (σ : J)
    (h : (c.loc p).pc = .l8) (hout : c.Out (c.loc p).s ≠ (c.loc p).d) : c.step p σ = c := by
  simp [Cfg.step, h, hout]

theorem deadCfg_step (σ : Fin 2) : deadCfg.step 1 σ = deadCfg := by
  apply step_l8_stuck _ _ _ deadCfg_p1.1
  rw [deadCfg_p1.2.1, deadCfg_p1.2.2, deadCfg_out]; decide

/-- Running only `p₁` from `deadCfg` never changes the configuration. -/
theorem deadCfg_run_p1 (es : List (Ev 2 (Fin 2))) (h : ∀ e ∈ es, e.1 = 1) : run deadCfg es = deadCfg := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨p, σ⟩ := e
    obtain rfl : p = 1 := h (p, σ) (by simp)
    show run (deadCfg.step 1 σ) es = deadCfg
    rw [deadCfg_step]
    exact ih (fun x hx => h x (by simp [hx]))

theorem fin2_cases (q : Fin 2) : q = 0 ∨ q = 1 := by omega

/-! ## Liveness properties (P2) and their refutation -/

variable {n : ℕ} {J : Type} [DecidableEq J]

/-- Fairness: every process takes infinitely many steps, unless from some time on it stays in the
remainder section forever (processes may stay in, or crash in, the remainder section). -/
def Sched.Fair (s₀ : J) (σ : Sched n J) : Prop :=
  ∀ p : Fin n, (∀ T, ∃ t ≥ T, (σ t).1 = p) ∨ ∃ T, ∀ t ≥ T, ((σ.cfg s₀ t).loc p).pc = .rem

/-- (P2) Starvation freedom: in every fair execution in which no process stays in the CS
forever, every process in the trying section eventually enters the CS. -/
def StarvationFree (n : ℕ) (J : Type) [DecidableEq J] (s₀ : J) : Prop :=
  ∀ σ : Sched n J, σ.Fair s₀ →
    (∀ p T, ∃ t ≥ T, ((σ.cfg s₀ t).loc p).pc ≠ .cs) →
    ∀ p t, ((σ.cfg s₀ t).loc p).pc.trying → ∃ t' ≥ t, ((σ.cfg s₀ t').loc p).pc = .cs

/-- The deadlocking schedule: `deadSched`, then `p₁` forever. -/
def deadSigma : Sched 2 (Fin 2) := fun t => if h : t < deadSched.length then deadSched[t] else (1, 0)

theorem deadSched_length : deadSched.length = 79 := by decide

theorem deadSigma_cfg_ge (t : ℕ) (ht : deadSched.length ≤ t) : deadSigma.cfg 0 t = deadCfg := by
  have hsplit : (List.range t).map deadSigma =
      deadSched ++ List.replicate (t - deadSched.length) (1, 0) := by
    apply List.ext_getElem
    · simp; omega
    · intro i h1 h2
      simp only [List.getElem_map, List.getElem_range, deadSigma]
      by_cases hi : i < deadSched.length
      · rw [List.getElem_append_left hi, dite_eq_left_of_eq_true (eq_true hi)]
      · rw [List.getElem_append_right (by omega), List.getElem_replicate, dite_eq_right_of_eq_false (eq_false hi)]
  have h0 : run (Cfg.init 2 0) deadSched = deadCfg := by unfold deadCfg; rfl
  have h1 : run (Cfg.init 2 0) (deadSched ++ List.replicate (t - deadSched.length) (1, 0)) =
      run (run (Cfg.init 2 0) deadSched) (List.replicate (t - deadSched.length) (1, 0)) :=
    List.foldl_append
  rw [Sched.cfg, hsplit, h1, h0]
  exact deadCfg_run_p1 _ (fun e he => by rw [(List.mem_replicate.1 he).2])

theorem deadSigma_fair : deadSigma.Fair 0 := by
  intro p
  rcases fin2_cases p with rfl | rfl
  · right; exact ⟨79, fun t ht => by rw [deadSigma_cfg_ge t (by rw [deadSched_length]; exact ht)]; exact deadCfg_p0⟩
  · left
    intro T
    refine ⟨max T 79, le_max_left _ _, ?_⟩
    simp only [deadSigma]
    rw [dite_eq_right_of_eq_false (eq_false (by rw [deadSched_length]; omega))]

/-- **Lemma 3 (Starvation freedom, P2) of the paper is false**: in the fair execution
`deadSigma` (two processes, two sessions) process `p₁` stays in the trying section forever,
although nobody stays in the CS. -/
theorem starvationFree_false : ¬ StarvationFree 2 (Fin 2) 0 := by
  intro h
  have hge := deadSigma_cfg_ge
  rw [deadSched_length] at hge
  obtain ⟨t', ht', hcs⟩ := h deadSigma deadSigma_fair
    (fun p T => ⟨max T 79, le_max_left _ _, by
      rw [hge _ (le_max_right _ _)]
      rcases fin2_cases p with rfl | rfl
      · rw [deadCfg_p0]; decide
      · rw [deadCfg_p1.1]; decide⟩)
    1 79 (by rw [hge _ le_rfl, deadCfg_p1.1]; trivial)
  rw [hge _ ht', deadCfg_p1.1] at hcs
  exact absurd hcs (by decide)

/-! ## Claim 3, Lemma 2 (concurrent entering as stated in the paper) and Invariant 8 -/

/-- `k` solo steps of `p`. -/
def soloRun (c : Cfg n J) (p : Fin n) (σ : J) : ℕ → Cfg n J
  | 0 => c
  | k + 1 => (soloRun c p σ k).step p σ

/-- Claim 3 of the paper: a process at line 8 with no active conflicting process has
`Out[s] = d`. -/
def Claim3 (n : ℕ) (J : Type) [DecidableEq J] (s₀ : J) : Prop :=
  ∀ c : Cfg n J, Reachable s₀ c → ∀ p, (c.loc p).pc = .l8 →
    (∀ q, (c.loc q).active → (c.loc q).s = (c.loc p).s) → c.Out (c.loc p).s = (c.loc p).d

/-- Lemma 2 of the paper (concurrent entering, in the paper's formulation): there is a bound
`b` such that a process in the trying section enters the CS within `b` of its own steps in the
absence of active conflicting processes (here: even running solo). -/
def ConcurrentEnteringPaper (n : ℕ) (J : Type) [DecidableEq J] (s₀ : J) : Prop :=
  ∃ b : ℕ, ∀ c : Cfg n J, Reachable s₀ c → ∀ p, (c.loc p).pc.trying →
    (∀ q, (c.loc q).active → (c.loc q).s = (c.loc p).s) →
    ∀ σ, ∃ k ≤ b, ((soloRun c p σ k).loc p).pc = .cs

/-- **Claim 3 of the paper is false.** -/
theorem claim3_false : ¬ Claim3 2 (Fin 2) 0 := by
  intro h
  have := h deadCfg deadCfg_reachable 1 deadCfg_p1.1 (fun q hq => by
    rcases fin2_cases q with rfl | rfl
    · exact absurd deadCfg_p0 hq
    · rfl)
  rw [deadCfg_p1.2.1, deadCfg_p1.2.2, deadCfg_out] at this
  exact absurd this (by decide)

theorem soloRun_deadCfg (σ : Fin 2) (k : ℕ) : soloRun deadCfg 1 σ k = deadCfg := by
  induction k with
  | zero => rfl
  | succ k ih => rw [soloRun, ih, deadCfg_step]

/-- **Lemma 2 (concurrent entering) as stated in the paper is false**: from `deadCfg` the only
active process `p₁` never enters the CS, however many steps it takes. -/
theorem concurrentEnteringPaper_false : ¬ ConcurrentEnteringPaper 2 (Fin 2) 0 := by
  rintro ⟨b, hb⟩
  obtain ⟨k, -, hk⟩ := hb deadCfg deadCfg_reachable 1 (by rw [deadCfg_p1.1]; trivial)
    (fun q hq => by
      rcases fin2_cases q with rfl | rfl
      · exact absurd deadCfg_p0 hq
      · rfl) 0
  rw [soloRun_deadCfg, deadCfg_p1.1] at hk
  exact absurd hk (by decide)

/-- Invariant 8 of the paper: if `p` of session `s` and side `d` is at line 8, `Min(Q) = (s,d)`,
`S = (s',d',−)`, `C[s',d'] = 0` and `s ≠ s'`, then some process of session `s'` is in the exit
section or at lines 1.8–5.4. -/
def Invariant8 (n : ℕ) (J : Type) [DecidableEq J] (s₀ : J) : Prop :=
  ∀ c : Cfg n J, Reachable s₀ c → ∀ p, (c.loc p).pc = .l8 →
    minQ c.Q = some ((c.loc p).s, (c.loc p).d) → c.C c.S.1 c.S.2.1 = 0 → (c.loc p).s ≠ c.S.1 →
    ∃ q, (c.loc q).s = c.S.1 ∧
      (c.loc q).pc ∈ [.l13, .l14, .l15, .l16_1, .l16_2, .l16_3, .l16_4, .l16_5, .l16_6, .l16_7,
        .l16_8, .l16_9, .l16_10, .l16_11, .l16_12, .l16_13, .l16_14,
        .l1_7, .l2, .l3, .l4, .l5_1, .l5_2, .l5_3, .l5_4]

/-- **Invariant 8 of the paper is false.** -/
theorem invariant8_false : ¬ Invariant8 2 (Fin 2) 0 := by
  intro h
  obtain ⟨q, -, hq⟩ := h deadCfg deadCfg_reachable 1 deadCfg_p1.1
    (by rw [deadCfg_minQ, deadCfg_p1.2.1, deadCfg_p1.2.2])
    (by rw [deadCfg_S]; exact deadCfg_C.1) (by rw [deadCfg_p1.2.1, deadCfg_S]; decide)
  rcases fin2_cases q with rfl | rfl
  · rw [deadCfg_p0] at hq; simp at hq
  · rw [deadCfg_p1.1] at hq; simp at hq

end Podc.GroupMutexLogRMR
