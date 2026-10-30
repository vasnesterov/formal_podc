import Papers.PODC2026.GeneralizedCAS.Bounds

/-!
# Algorithm 1: executions as sequences of states ("time")

The step-complexity proof of Appendix B.2 reasons about *times*: positions in an execution.
`Trace` is a finite execution of length `N` given as a sequence of configurations `C n` with
ghost variables `G n` and labels `lbl n` (time `n` is the `n`-th step; `C n` is the state before
it). This file proves the basic temporal facts used in Appendix B:

* the invariants hold at every time (`Trace.inv`, `Trace.inv2`);
* monotonicity: done (Observation B.1.8), `ts`, `k`;
* the local state of a process changes only at its own steps (`Trace.loc_eq`);
* how `A` and `S` can change (`Trace.A_change`, `Trace.S_change`);
* the recorded times of the lines executed in the current iteration (`Trace.tinv`).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Podc.GeneralizedCAS

open Cslib.SharedMemory

variable {T : ObjSpec} [LinearOrder T.Op] {P : Type} [DecidableEq P]
variable (cellInit : ℕ → CellVal T.Resp)

variable (T P) in
/-- A finite execution of length `N` with the ghost variables, indexed by time. -/
structure Trace where
  N : ℕ
  C : ℕ → Cfg T P
  G : ℕ → Ghost T P
  lbl : ℕ → Label P T
  zeroC : C 0 = (alg T P cellInit).initCfg
  zeroG : G 0 = ginit T P
  stepC : ∀ n < N, (alg T P cellInit).step (C n) (lbl n) = some (C (n + 1))
  stepG : ∀ n < N, G (n + 1) = augStep (C n) (lbl n) (G n)

namespace Trace

variable {cellInit} (tr : Trace T P cellInit)

theorem invs {n : ℕ} (hn : n ≤ tr.N) : CInv (tr.C n) (tr.G n) ∧ Inv2 (tr.C n) (tr.G n) := by
  induction n with
  | zero => rw [tr.zeroC, tr.zeroG]; exact ⟨cinv_init cellInit, inv2_init cellInit⟩
  | succ n ih =>
    obtain ⟨hI, hJ⟩ := ih (by omega)
    have hs := tr.stepC n (by omega)
    rw [tr.stepG n (by omega)]
    exact ⟨hI.step cellInit hs, hJ.step cellInit hI hs⟩

theorem inv {n : ℕ} (hn : n ≤ tr.N) : CInv (tr.C n) (tr.G n) := (tr.invs hn).1
theorem inv2 {n : ℕ} (hn : n ≤ tr.N) : Inv2 (tr.C n) (tr.G n) := (tr.invs hn).2

theorem clock {n : ℕ} (hn : n ≤ tr.N) : (tr.G n).clock = n := by
  induction n with
  | zero => rw [tr.zeroG]; rfl
  | succ n ih =>
    rw [tr.stepG n (by omega)]
    have := ih (by omega)
    cases h : tr.lbl n with
    | inv p o => simp [augStep, this]
    | ret p r => simp [augStep, this]
    | tau p =>
      simp only [augStep]
      split <;> (try split_ifs) <;> (try split) <;> simp [this]

/-- Monotonicity along the trace, from a one-step property. -/
theorem mono {Q : ℕ → Prop} (hstep : ∀ n < tr.N, Q n → Q (n + 1)) {n m : ℕ} (hnm : n ≤ m)
    (hm : m ≤ tr.N) (hn : Q n) : Q m := by
  induction m, hnm using Nat.le_induction with
  | base => exact hn
  | succ m _ ih => exact hstep m (by omega) (ih (by omega))

/-- **Observation B.1.8** along the trace. -/
theorem done_mono {τ n m : ℕ} (hnm : n ≤ m) (hm : m ≤ tr.N)
    (h : Done (tr.C n) (tr.G n) τ) : Done (tr.C m) (tr.G m) τ :=
  tr.mono (Q := fun n => Done (tr.C n) (tr.G n) τ)
    (fun n hn hd => by
      rw [tr.stepG n hn]; exact done_step cellInit (tr.inv hn.le) (tr.stepC n hn) hd) hnm hm h

theorem ts_mono {τ n m : ℕ} {x : P × ℕ × T.Op} (hnm : n ≤ m) (hm : m ≤ tr.N)
    (h : (tr.G n).ts τ = some x) : (tr.G m).ts τ = some x :=
  tr.mono (Q := fun n => (tr.G n).ts τ = some x)
    (fun n hn hd => by
      rw [tr.stepG n hn]; exact ts_step cellInit (tr.inv hn.le) (tr.stepC n hn) hd) hnm hm h

theorem k_mono {q : P} {n m : ℕ} (hnm : n ≤ m) (hm : m ≤ tr.N) : (tr.G n).k q ≤ (tr.G m).k q := by
  induction m, hnm using Nat.le_induction with
  | base => exact le_rfl
  | succ m _ ih =>
    rw [tr.stepG m (by omega)]; exact (ih (by omega)).trans (k_step q)

/-- Discrete intermediate value theorem. -/
theorem exists_rise {Q : ℕ → Prop} {a b : ℕ} (hab : a ≤ b) (ha : ¬ Q a) (hb : Q b) :
    ∃ m, a ≤ m ∧ m < b ∧ ¬ Q m ∧ Q (m + 1) := by
  induction b, hab using Nat.le_induction with
  | base => exact absurd hb ha
  | succ b hab ih =>
    by_cases hQ : Q b
    · obtain ⟨m, h1, h2, h3, h4⟩ := ih hQ; exact ⟨m, h1, by omega, h3, h4⟩
    · exact ⟨b, hab, by omega, hQ, hb⟩

/-! ### One step -/

theorem step_tau {n : ℕ} (hn : n < tr.N) {p : P} (hl : tr.lbl n = .tau p) :
    (tr.C n).pend p ≠ none ∧ ((tr.C n).loc p).IsMem ∧ (tr.C (n + 1)).pend = (tr.C n).pend ∧
    (tr.C (n + 1)).M = (effect ((tr.C n).loc p) (tr.C n).M).1 ∧
    (tr.C (n + 1)).loc = Function.update (tr.C n).loc p (effect ((tr.C n).loc p) (tr.C n).M).2 := by
  have := tr.stepC n hn; rw [hl] at this; exact step_tau_eff cellInit this

/-- Steps of other processes do not change the local state of `p` nor its ghost variables. -/
theorem step_other {n : ℕ} (hn : n < tr.N) {p : P} (hl : (tr.lbl n).proc ≠ p) :
    (tr.C (n + 1)).loc p = (tr.C n).loc p ∧ (tr.C (n + 1)).pend p = (tr.C n).pend p ∧
    (tr.G (n + 1)).lt p = (tr.G n).lt p ∧ (tr.G (n + 1)).it p = (tr.G n).it p ∧
    (tr.G (n + 1)).ns p = (tr.G n).ns p ∧ (tr.G (n + 1)).k p = (tr.G n).k p := by
  have hs := tr.stepC n hn
  rw [tr.stepG n hn]
  cases h : tr.lbl n with
  | inv q o =>
    rw [h] at hs hl; have hq : p ≠ q := fun e => hl (by simp [Label.proc, e])
    obtain ⟨-, hpend, -, hloc⟩ := step_inv_eff cellInit hs
    simp [hloc, hpend, augStep, Function.update_of_ne hq]
  | ret q r =>
    rw [h] at hs hl; have hq : p ≠ q := fun e => hl (by simp [Label.proc, e])
    obtain ⟨-, -, hpend, -, hloc⟩ := step_ret_eff cellInit hs
    simp [hloc, hpend, augStep, Function.update_of_ne hq]
  | tau q =>
    rw [h] at hs hl; have hq : p ≠ q := fun e => hl (by simp [Label.proc, e])
    obtain ⟨-, -, hpend, -, hloc⟩ := step_tau_eff cellInit hs
    simp only [hloc, hpend, Function.update_of_ne hq, true_and]
    simp only [augStep]
    split <;> (try split_ifs) <;> (try split) <;> simp [Function.update_of_ne hq]

/-- If `p` takes no step during `[n, m)`, its local state and ghost variables are unchanged. -/
theorem frozen {p : P} {n m : ℕ} (hnm : n ≤ m) (hm : m ≤ tr.N)
    (hno : ∀ i, n ≤ i → i < m → (tr.lbl i).proc ≠ p) :
    (tr.C m).loc p = (tr.C n).loc p ∧ (tr.C m).pend p = (tr.C n).pend p ∧
    (tr.G m).lt p = (tr.G n).lt p ∧ (tr.G m).it p = (tr.G n).it p ∧
    (tr.G m).ns p = (tr.G n).ns p ∧ (tr.G m).k p = (tr.G n).k p := by
  induction m, hnm using Nat.le_induction with
  | base => simp
  | succ m hnm ih =>
    obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ih (by omega) (fun i h1 h2 => hno i h1 (by omega))
    obtain ⟨b1, b2, b3, b4, b5, b6⟩ := tr.step_other (n := m) (by omega) (hno m hnm (by omega))
    exact ⟨b1.trans a1, b2.trans a2, b3.trans a3, b4.trans a4, b5.trans a5, b6.trans a6⟩

/-- How `A` can change: by a successful GCAS on line 8 or line 15. -/
theorem A_change {n : ℕ} (hn : n < tr.N) (h : (tr.C (n + 1)).M.A ≠ (tr.C n).M.A) :
    ∃ q, tr.lbl n = .tau q ∧ (tr.C (n + 1)).M.A = ((tr.C n).loc q).mine ∧
      ((((tr.C n).loc q).pc = .l8 ∧ ((tr.C n).loc q).mine < (tr.C n).M.A) ∨
       (((tr.C n).loc q).pc = .l15 ∧ (tr.C n).M.A = ((tr.C n).loc q).ann)) := by
  have hs := tr.stepC n hn
  cases hl : tr.lbl n with
  | inv q o =>
    rw [hl] at hs; obtain ⟨-, -, hmem, -⟩ := step_inv_eff cellInit hs
    exact absurd (by simp [Cfg.M, hmem]) h
  | ret q r =>
    rw [hl] at hs; obtain ⟨-, -, -, hmem, -⟩ := step_ret_eff cellInit hs
    exact absurd (by simp [Cfg.M, hmem]) h
  | tau q =>
    rw [hl] at hs; obtain ⟨-, -, -, hM, -⟩ := step_tau_eff cellInit hs
    refine ⟨q, rfl, ?_⟩
    rw [hM] at h ⊢
    cases hpc : ((tr.C n).loc q).pc <;> simp [effect, hpc] at h ⊢ <;> (try split_ifs at h ⊢) <;>
      simp_all

/-- How `S` can change: by a successful CAS on line 13. -/
theorem S_change {n : ℕ} (hn : n < tr.N) (h : (tr.C (n + 1)).M.S ≠ (tr.C n).M.S) :
    ∃ q, tr.lbl n = .tau q ∧ ((tr.C n).loc q).pc = .l13 ∧ (tr.C n).M.S = ((tr.C n).loc q).snap ∧
      (tr.C (n + 1)).M.S = ((tr.C n).loc q).newS := by
  have hs := tr.stepC n hn
  cases hl : tr.lbl n with
  | inv q o =>
    rw [hl] at hs; obtain ⟨-, -, hmem, -⟩ := step_inv_eff cellInit hs
    exact absurd (by simp [Cfg.M, hmem]) h
  | ret q r =>
    rw [hl] at hs; obtain ⟨-, -, -, hmem, -⟩ := step_ret_eff cellInit hs
    exact absurd (by simp [Cfg.M, hmem]) h
  | tau q =>
    rw [hl] at hs; obtain ⟨-, -, -, hM, -⟩ := step_tau_eff cellInit hs
    refine ⟨q, rfl, ?_⟩
    rw [hM] at h ⊢
    cases hpc : ((tr.C n).loc q).pc <;> simp [effect, hpc] at h ⊢ <;> (try split_ifs at h ⊢) <;>
      simp_all

open Classical in
/-- The ghost variables of the stepping process after a memory step. -/
theorem step_tau_ghost {n : ℕ} (hn : n < tr.N) {p : P} (hl : tr.lbl n = .tau p) :
    (tr.G (n + 1)).lt p = Function.update ((tr.G n).lt p) ((tr.C n).loc p).pc n ∧
    (tr.G (n + 1)).k p = (tr.G n).k p ∧
    (tr.G (n + 1)).it p = (if ((tr.C n).loc p).pc = .l13 ∨ ((tr.C n).loc p).pc = .l15 then
      (tr.G n).it p + 1 else (tr.G n).it p) := by
  rw [tr.stepG n hn, hl]
  have hc := tr.clock hn.le
  simp only [augStep]
  split <;> rename_i hpc <;> (try split_ifs) <;> (try split) <;> simp [hc, hpc] <;> simp_all

/-- The recorded times of the lines executed by `p` in its current iteration, and what `p` read
at these times. -/
structure IterTimes (n : ℕ) (p : P) : Prop where
  a : ((tr.C n).loc p).pc.Loop → ((tr.C n).loc p).pc ≠ .l5 →
    (tr.G n).lt p .l5 < n ∧ tr.lbl ((tr.G n).lt p .l5) = .tau p ∧
    ((tr.C ((tr.G n).lt p .l5)).loc p).pc = .l5 ∧
    (tr.G ((tr.G n).lt p .l5)).it p = (tr.G n).it p ∧ (tr.G ((tr.G n).lt p .l5)).k p = (tr.G n).k p ∧
    (tr.C ((tr.G n).lt p .l5)).M.cell ((tr.C n).loc p).me = ⟨((tr.C n).loc p).t, .null⟩
  b : ((tr.C n).loc p).pc.HasSnap →
    (tr.G n).lt p .l5 < (tr.G n).lt p .l6 ∧ (tr.G n).lt p .l6 < n ∧
    tr.lbl ((tr.G n).lt p .l6) = .tau p ∧ ((tr.C ((tr.G n).lt p .l6)).loc p).pc = .l6 ∧
    ((tr.C n).loc p).snap = (tr.C ((tr.G n).lt p .l6)).M.S
  c : ((tr.C n).loc p).pc.Copied →
    (tr.G n).lt p .l6 < (tr.G n).lt p .l7 ∧ (tr.G n).lt p .l7 < n ∧
    tr.lbl ((tr.G n).lt p .l7) = .tau p ∧ ((tr.C ((tr.G n).lt p .l7)).loc p).pc = .l7 ∧
    ((tr.C ((tr.G n).lt p .l7)).loc p).snap = ((tr.C n).loc p).snap
  d : (((tr.C n).loc p).pc = .l9 ∨ ((tr.C n).loc p).pc.HasAnn) →
    (tr.G n).lt p .l7 < (tr.G n).lt p .l8 ∧ (tr.G n).lt p .l8 < n ∧
    tr.lbl ((tr.G n).lt p .l8) = .tau p ∧ ((tr.C ((tr.G n).lt p .l8)).loc p).pc = .l8 ∧
    ((tr.C ((tr.G n).lt p .l8)).loc p).mine = ((tr.C n).loc p).mine
  e : ((tr.C n).loc p).pc.HasAnn →
    (tr.G n).lt p .l8 < (tr.G n).lt p .l9 ∧ (tr.G n).lt p .l9 < n ∧
    tr.lbl ((tr.G n).lt p .l9) = .tau p ∧ ((tr.C ((tr.G n).lt p .l9)).loc p).pc = .l9 ∧
    ((tr.C n).loc p).ann = (tr.C ((tr.G n).lt p .l9)).M.A
  f : (((tr.C n).loc p).pc = .l13 ∨ ((tr.C n).loc p).pc = .l15) →
    (tr.G n).lt p .l9 < (tr.G n).lt p .l10 ∧ (tr.G n).lt p .l10 < n ∧
    tr.lbl ((tr.G n).lt p .l10) = .tau p ∧ ((tr.C ((tr.G n).lt p .l10)).loc p).pc = .l10 ∧
    ((tr.C ((tr.G n).lt p .l10)).loc p).ann = ((tr.C n).loc p).ann ∧
    ((tr.C ((tr.G n).lt p .l10)).M.cell ((tr.C n).loc p).ann.ptr =
      ⟨((tr.C n).loc p).ann.time, .null⟩ ↔ ((tr.C n).loc p).pc = .l13)

theorem iterTimes_zero (p : P) : tr.IterTimes 0 p := by
  have h : ((tr.C 0).loc p).pc = .l2 := by rw [tr.zeroC]; rfl
  constructor <;> simp [h, PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn]

theorem iterTimes_succ {n : ℕ} (hn : n < tr.N) (p : P) (h : tr.IterTimes n p) :
    tr.IterTimes (n + 1) p := by
  obtain ⟨ha, hb, hc, hd, he, hf⟩ := h
  by_cases hp : (tr.lbl n).proc = p
  swap
  · obtain ⟨e1, -, e3, e4, -, e6⟩ := tr.step_other hn hp
    refine ⟨fun h1 h2 => ?_, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_, fun h1 => ?_⟩
    · rw [e1] at h1 h2; obtain ⟨x1, x2, x3, x4, x5, x6⟩ := ha h1 h2
      rw [e3, e4, e6, e1]; exact ⟨by omega, x2, x3, x4, x5, x6⟩
    · rw [e1] at h1; obtain ⟨x1, x2, x3, x4, x5⟩ := hb h1
      rw [e3, e1]; exact ⟨x1, by omega, x3, x4, x5⟩
    · rw [e1] at h1; obtain ⟨x1, x2, x3, x4, x5⟩ := hc h1
      rw [e3, e1]; exact ⟨x1, by omega, x3, x4, x5⟩
    · rw [e1] at h1; obtain ⟨x1, x2, x3, x4, x5⟩ := hd h1
      rw [e3, e1]; exact ⟨x1, by omega, x3, x4, x5⟩
    · rw [e1] at h1; obtain ⟨x1, x2, x3, x4, x5⟩ := he h1
      rw [e3, e1]; exact ⟨x1, by omega, x3, x4, x5⟩
    · rw [e1] at h1; obtain ⟨x1, x2, x3, x4, x5, x6⟩ := hf h1
      rw [e3, e1]; exact ⟨x1, by omega, x3, x4, x5, x6⟩
  have hs := tr.stepC n hn
  cases hl : tr.lbl n with
  | inv q o =>
    rw [hl] at hs hp; simp only [Label.proc] at hp; subst hp
    obtain ⟨-, -, -, hloc⟩ := step_inv_eff cellInit hs
    have : ((tr.C (n + 1)).loc q).pc = .l2 ∨ ((tr.C (n + 1)).loc q).pc = .l3 := by
      rw [hloc]; simp only [Function.update_self, Loc.invoke]; split_ifs <;> simp
    constructor <;> rcases this with h' | h' <;>
      simp [h', PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn]
  | ret q r =>
    rw [hl] at hs hp; simp only [Label.proc] at hp; subst hp
    obtain ⟨-, -, -, -, hloc⟩ := step_ret_eff cellInit hs
    have : ((tr.C (n + 1)).loc q).pc = .l2 := by rw [hloc]; simp
    constructor <;> simp [this, PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn]
  | tau q =>
    rw [hl] at hp; simp only [Label.proc] at hp; subst hp
    obtain ⟨-, hmem, -, hM, hloc⟩ := tr.step_tau hn hl
    obtain ⟨hlt, hk, hit⟩ := tr.step_tau_ghost hn hl
    have hloc' : (tr.C (n + 1)).loc q = (effect ((tr.C n).loc q) (tr.C n).M).2 := by
      rw [hloc, Function.update_self]
    clear hloc hs hM
    have hit' : ¬ (((tr.C n).loc q).pc = .l13 ∨ ((tr.C n).loc q).pc = .l15) →
        (tr.G (n + 1)).it q = (tr.G n).it q := fun h => by rw [hit, if_neg h]
    cases hpc : ((tr.C n).loc q).pc
    case l16 r => exact absurd hpc (hmem r)
    case l7 =>
      have hX : (effect ((tr.C n).loc q) (tr.C n).M).2 = { (tr.C n).loc q with pc := .l8 } := by
        simp [effect, hpc]
      have hit'' := hit' (by simp [hpc])
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha (by simp [hpc, PC.Loop]) (by simp [hpc])
      obtain ⟨b1, b2, b3, b4, b5⟩ := hb (by simp [hpc, PC.HasSnap])
      constructor <;> simp only [hloc', hX, hlt, hk, hit'', hpc] <;> intros <;>
        simp_all [PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn, Function.update_apply, Loc.mine, Loc.me] <;> omega
    case l2 | l3 | l4 | l13 | l15 =>
      constructor <;> simp [hloc', effect, hpc, PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn]
    case l5 =>
      have hit'' := hit' (by simp [hpc])
      rcases pc5_cases ((tr.C n).loc q) (tr.C n).M with h5 | h5 | ⟨r, h5⟩
      · have hX : (effect ((tr.C n).loc q) (tr.C n).M).2 = { (tr.C n).loc q with pc := .l6 } := by
          simp [effect, hpc, h5]
        have hcell : (tr.C n).M.cell ((tr.C n).loc q).me = ⟨((tr.C n).loc q).t, .null⟩ := by
          unfold pc5 at h5; split_ifs at h5 with hc
          · exact hc
          · split at h5 <;> cases h5
        constructor <;> simp only [hloc', hX, hlt, hk, hit'', hpc] <;> intros <;>
          simp_all [PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn, Function.update_apply, Loc.me]
      · have hX : (effect ((tr.C n).loc q) (tr.C n).M).2 = { (tr.C n).loc q with pc := .l5 } := by
          simp [effect, hpc, h5]
        constructor <;> simp [hloc', hX, PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn]
      · have hX : (effect ((tr.C n).loc q) (tr.C n).M).2 = { (tr.C n).loc q with pc := .l16 r } := by
          simp [effect, hpc, h5]
        constructor <;> simp [hloc', hX, PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn]
    case l6 =>
      have hX : (effect ((tr.C n).loc q) (tr.C n).M).2 =
          { (tr.C n).loc q with snap := (tr.C n).M.S, pc := .l7 } := by simp [effect, hpc]
      have hit'' := hit' (by simp [hpc])
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha (by simp [hpc, PC.Loop]) (by simp [hpc])
      constructor <;> simp only [hloc', hX, hlt, hk, hit'', hpc] <;> intros <;>
        simp_all [PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn, Function.update_apply, Loc.mine, Loc.me] <;> omega
    case l8 =>
      have hX : (effect ((tr.C n).loc q) (tr.C n).M).2 = { (tr.C n).loc q with pc := .l9 } := by
        simp [effect, hpc]
      have hit'' := hit' (by simp [hpc])
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha (by simp [hpc, PC.Loop]) (by simp [hpc])
      obtain ⟨b1, b2, b3, b4, b5⟩ := hb (by simp [hpc, PC.HasSnap])
      obtain ⟨c1, c2, c3, c4, c5⟩ := hc (by simp [hpc, PC.Copied])
      constructor <;> simp only [hloc', hX, hlt, hk, hit'', hpc] <;> intros <;>
        simp_all [PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn, Function.update_apply, Loc.mine, Loc.me] <;> omega
    case l9 =>
      have hX : (effect ((tr.C n).loc q) (tr.C n).M).2 =
          { (tr.C n).loc q with ann := (tr.C n).M.A, pc := .l10 } := by simp [effect, hpc]
      have hit'' := hit' (by simp [hpc])
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha (by simp [hpc, PC.Loop]) (by simp [hpc])
      obtain ⟨b1, b2, b3, b4, b5⟩ := hb (by simp [hpc, PC.HasSnap])
      obtain ⟨c1, c2, c3, c4, c5⟩ := hc (by simp [hpc, PC.Copied])
      obtain ⟨d1, d2, d3, d4, d5⟩ := hd (by simp [hpc])
      constructor <;> simp only [hloc', hX, hlt, hk, hit'', hpc] <;> intros <;>
        simp_all [PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn, Function.update_apply, Loc.mine, Loc.me] <;>
        omega
    case l10 =>
      have hit'' := hit' (by simp [hpc])
      obtain ⟨a1, a2, a3, a4, a5, a6⟩ := ha (by simp [hpc, PC.Loop]) (by simp [hpc])
      obtain ⟨b1, b2, b3, b4, b5⟩ := hb (by simp [hpc, PC.HasSnap])
      obtain ⟨c1, c2, c3, c4, c5⟩ := hc (by simp [hpc, PC.Copied])
      obtain ⟨d1, d2, d3, d4, d5⟩ := hd (Or.inr (by simp [hpc, PC.HasAnn]))
      obtain ⟨e1, e2, e3, e4, e5⟩ := he (by simp [hpc, PC.HasAnn])
      by_cases hcond : (tr.C n).M.cell ((tr.C n).loc q).ann.ptr = ⟨((tr.C n).loc q).ann.time, .null⟩
      · have hX : (effect ((tr.C n).loc q) (tr.C n).M).2 = { (tr.C n).loc q with pc := .l13 } := by
          simp [effect, hpc, hcond]
        constructor <;> simp only [hloc', hX, hlt, hk, hit'', hpc] <;> intros <;>
          simp_all [PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn, Function.update_apply, Loc.mine,
            Loc.me] <;> omega
      · have hX : (effect ((tr.C n).loc q) (tr.C n).M).2 = { (tr.C n).loc q with pc := .l15 } := by
          simp [effect, hpc, hcond]
        constructor <;> simp only [hloc', hX, hlt, hk, hit'', hpc] <;> intros <;>
          simp_all [PC.Loop, PC.HasSnap, PC.Copied, PC.HasAnn, Function.update_apply, Loc.mine,
            Loc.me] <;> omega


theorem iterTimes {n : ℕ} (hn : n ≤ tr.N) (p : P) : tr.IterTimes n p := by
  induction n with
  | zero => exact tr.iterTimes_zero p
  | succ n ih => exact tr.iterTimes_succ (by omega) p (ih (by omega))


/-- The recorded time of line 3 of the current operation. -/
def L3Time (n : ℕ) (p : P) : Prop :=
  (tr.C n).pend p ≠ none → ((tr.C n).loc p).pc.Past3 →
    (tr.G n).lt p .l3 < n ∧ tr.lbl ((tr.G n).lt p .l3) = .tau p ∧
    ((tr.C ((tr.G n).lt p .l3)).loc p).pc = .l3 ∧ (tr.G ((tr.G n).lt p .l3)).k p = (tr.G n).k p

theorem l3Time {n : ℕ} (hn : n ≤ tr.N) (p : P) : tr.L3Time n p := by
  induction n with
  | zero =>
    intro _ h; have : ((tr.C 0).loc p).pc = .l2 := by rw [tr.zeroC]; rfl
    rw [this] at h; exact absurd h id
  | succ n ih =>
    have ih := ih (by omega)
    intro hp h3
    by_cases hq : (tr.lbl n).proc = p
    swap
    · obtain ⟨e1, e2, e3, -, -, e6⟩ := tr.step_other (by omega) hq
      rw [e2] at hp; rw [e1] at h3; rw [e3, e6]
      obtain ⟨a1, a2, a3, a4⟩ := ih hp h3
      exact ⟨by omega, a2, a3, a4⟩
    have hs := tr.stepC n (by omega)
    cases hl : tr.lbl n with
    | inv q o =>
      rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, -, hloc⟩ := step_inv_eff cellInit hs
      rw [hloc] at h3; simp only [Function.update_self, Loc.invoke] at h3
      split_ifs at h3 <;> exact absurd h3 id
    | ret q r =>
      rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
      obtain ⟨-, -, hpend, -, -⟩ := step_ret_eff cellInit hs
      simp [hpend] at hp
    | tau q =>
      rw [hl] at hq; simp only [Label.proc] at hq; subst hq
      obtain ⟨hp0, hmem, hpend, -, hloc⟩ := tr.step_tau (by omega) hl
      obtain ⟨hlt, hk, -⟩ := tr.step_tau_ghost (by omega) hl
      rw [hlt, hk]
      by_cases hpc : ((tr.C n).loc q).pc = .l3
      · simp only [Function.update_apply, hpc, if_true]
        exact ⟨by omega, hl, by simp [hpc], trivial⟩
      · have h3' : ((tr.C n).loc q).pc.Past3 := by
          cases hc : ((tr.C n).loc q).pc <;> simp_all [PC.Past3, effect]
        obtain ⟨a1, a2, a3, a4⟩ := ih hp0 h3'
        simp only [Function.update_apply, Ne.symm hpc, if_false]
        exact ⟨by omega, a2, a3, a4⟩

end Trace

end Podc.GeneralizedCAS
