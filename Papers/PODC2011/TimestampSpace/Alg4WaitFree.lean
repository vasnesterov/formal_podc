import Papers.PODC2011.TimestampSpace.Alg4Space

/-!
# Algorithms 3 and 4 are wait-free for boundedly many `getTS` calls (Lemma 6.14)

With at most `M` `getTS` invocations every access has index `≤ B = ⌈2√M⌉` (Lemma 6.5), so the
while loop reads at most `B` registers and the for loop has at most `B` iterations; the
potential `pot B` of the local state strictly decreases with every step of the process.

* `alg4_waitFreeUpTo`: in every infinite execution with at most `M` `getTS` invocations, a
  process whose operation stays pending takes only finitely many steps. (CSLib's `WaitFree`
  quantifies over all infinite executions; with unboundedly many `getTS` calls the algorithm is
  not wait-free — the while loop can chase an ever-growing prefix of written registers — which is
  why the paper fixes `M` in advance.)
* `alg4_soloTerm`: from every reachable configuration a process running solo returns
  (obstruction-freedom, for any number of `getTS` calls).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.Alg4

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- Wait-freedom restricted to infinite executions with at most `M` `getTS` invocations. -/
def WaitFreeUpTo {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
    (I : Impl TS B P L) (M : ℕ) : Prop :=
  ∀ e : I.InfExec, (∀ T, totalGetTS ((List.range T).map e.lbl) ≤ M) →
    ∀ (p : P) (n : ℕ), (∀ t ≥ n, (e.cfg t).pend p ≠ none) → ∃ N, ∀ t ≥ N, e.lbl t ≠ .tau p

/-- Potential of a stage of the for loop. -/
def stgOff : Stg → ℕ
  | .s6 => 4
  | .s7 => 3
  | .s8 => 2
  | .s10 => 2
  | .s11 => 1

/-- Potential of a local state (an upper bound on its remaining accesses + 1), given the bound
`B` on all accessed indices. -/
def pot (B : ℕ) (pc : PC P) : ℕ :=
  match pc with
  | .idle => 0
  | .done _ => 1
  | .fin _ _ => 2
  | .scan _ => 3
  | .loop k i _ .s8 => 2 + 0 * k * i
  | .loop k i _ s => 3 + 4 * (k - 1 - i) + stgOff s
  | .wh j _ => 4 * B + 5 + (B + 1 - j)

/-- One access strictly decreases the potential (for `wh j`, given `j ≤ B`). -/
lemma pot_lt {B : ℕ} {q : P} {c : ℕ} {R R' : Mem P} {pc pc' : PC P}
    (hT : TauEff q c R pc pc' R') (hB : ∀ j v, pc = .wh j v → j ≤ B)
    (hpi : PI1 R q ⟨c, pc⟩) : pot B pc' < pot B pc := by
  cases hT with
  | @whS j v x _ => have := hB j v rfl; simp only [pot]; omega
  | @whN j v _ =>
    have := hB j v rfl
    simp only [PI1] at hpi
    unfold endWh; split_ifs <;> simp only [pot, stgOff] <;> omega
  | s6N _ => simp [pot, stgOff]
  | s6S _ => simp only [pot, stgOff]; omega
  | s7T _ => simp only [pot, stgOff]; omega
  | s7F _ => simp [pot, stgOff]
  | s8 => simp [pot]
  | s10T _ => simp [pot, stgOff]
  | s10F _ | s11 =>
    unfold nextIt; split_ifs <;> simp only [pot, stgOff] <;> omega
  | scN _ => simp [pot]
  | scS _ => simp [pot]
  | fin => simp [pot]

/-- In a configuration reached with `≤ M` `getTS` calls, an access of `p` decreases its
potential (with `B = ⌈2√M⌉`). -/
lemma pot_step {M : ℕ} {α : List (Label P TS)} {C C' : ACfg P} {p : P}
    (h : (alg4 (P := P)).run α = some C) (hM : totalGetTS α ≤ M)
    (hs : (alg4 (P := P)).step C (.tau p) = some C') :
    pot ⌈2 * Real.sqrt M⌉₊ (C'.loc p).pc < pot ⌈2 * Real.sqrt M⌉₊ (C.loc p).pc := by
  have h1 := inv1_of_run h
  obtain ⟨pc', h0, -, hloc, hT⟩ := tau_step hs
  rw [hloc, Function.update_self]
  have hpi := h1.pi p
  have hB : ∀ j v, (C.loc p).pc = .wh j v → j ≤ ⌈2 * Real.sqrt M⌉₊ := by
    intro j v hj
    have hact : (alg4 (P := P)).act p (C.loc p) = .access () (MOp.read j) (fun r =>
        match r j with
        | some x => ⟨(C.loc p).cnt, .wh (j + 1) (some x)⟩
        | none => ⟨(C.loc p).cnt, endWh j v⟩) := by
      change act p (C.loc p) = _
      unfold act; rw [hj]; rfl
    exact (alg4_space h hM h0 hact).2
  generalize C.loc p = l at hpi hT hB
  obtain ⟨c, pc⟩ := l
  exact pot_lt hT hB hpi

/-- The configurations of an infinite execution are reachable. -/
lemma run_range (e : (alg4 (P := P)).InfExec) (t : ℕ) :
    (alg4 (P := P)).run ((List.range t).map e.lbl) = some (e.cfg t) := by
  induction t with
  | zero => simp [e.cfg_zero, Impl.run]
  | succ t ih =>
    rw [List.range_succ, List.map_append, List.map_singleton, Impl.run_append_of_eq _ ih,
      Impl.runFrom_singleton]
    exact e.step_eq t

/-- A natural-number sequence that never increases after `t0` cannot decrease infinitely
often. -/
lemma no_descent (f : ℕ → ℕ) (t0 : ℕ) (hmono : ∀ t, t0 ≤ t → f (t + 1) ≤ f t)
    (hstrict : ∀ N, ∃ m, N ≤ m ∧ f (m + 1) < f m) : False := by
  have anti : ∀ a b, t0 ≤ a → a ≤ b → f b ≤ f a := by
    intro a b ha hab
    induction b, hab using Nat.le_induction with
    | base => exact le_rfl
    | succ b hb ih => exact (hmono b (ha.trans hb)).trans ih
  have key : ∀ c, ∃ t, t0 ≤ t ∧ f t + c ≤ f t0 := by
    intro c
    induction c with
    | zero => exact ⟨t0, le_rfl, le_rfl⟩
    | succ c ih =>
      obtain ⟨t, ht, hc⟩ := ih
      obtain ⟨m, hm, hlt⟩ := hstrict t
      exact ⟨m + 1, by omega, by have := anti t m ht hm; omega⟩
  obtain ⟨t, -, ht⟩ := key (f t0 + 1)
  omega

/-- **Lemma 6.14** (wait-freedom for at most `M` `getTS` calls). -/
theorem alg4_waitFreeUpTo (M : ℕ) : WaitFreeUpTo (alg4 (P := P)) M := by
  intro e hM p n hpend
  set B := ⌈2 * Real.sqrt M⌉₊
  let f : ℕ → ℕ := fun t => pot B ((e.cfg t).loc p).pc
  have hstep : ∀ t, n ≤ t → f (t + 1) ≤ f t ∧ (e.lbl t = .tau p → f (t + 1) < f t) := by
    intro t ht
    have hs := e.step_eq t
    by_cases hq : (e.lbl t).proc = p
    · cases hl : e.lbl t with
      | inv q o =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (step_inv' hs).1 (hpend t ht)
      | ret q r =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        exact absurd (by simp [(step_ret' hs).2.1]) (hpend (t + 1) (by omega))
      | tau q =>
        rw [hl] at hs hq; simp only [Label.proc] at hq; subst hq
        have := pot_step (run_range e t) (hM t) hs
        exact ⟨this.le, fun _ => this⟩
    · have := (Impl.step_other hs hq).1
      refine ⟨by simp only [f, this]; exact le_rfl, fun h => absurd (by rw [h]; rfl) hq⟩
  by_contra hcon
  push Not at hcon
  apply no_descent f n (fun t ht => (hstep t ht).1)
  intro N
  obtain ⟨t, ht, hl⟩ := hcon (max N n)
  exact ⟨t, le_of_max_le_left ht, (hstep t (le_of_max_le_right ht)).2 hl⟩

lemma totalGetTS_tau (α : List (Label P TS)) (q : P) :
    totalGetTS (α ++ [.tau q]) = totalGetTS α := by
  simp [totalGetTS, List.countP_append]

lemma totalGetTS_ret (α : List (Label P TS)) (q : P) (r : (ℕ × ℕ) ⊕ Bool) :
    totalGetTS (α ++ [.ret q r]) = totalGetTS α := by
  simp [totalGetTS, List.countP_append]

/-- Solo runs terminate (obstruction-freedom), for any number of `getTS` calls. -/
theorem alg4_solo {α : List (Label P TS)} {C : ACfg P} (h : (alg4 (P := P)).run α = some C)
    (p : P) : ∃ k, (((alg4 (P := P)).soloStep p)^[k] C).pend p = none := by
  set M := totalGetTS α
  set B := ⌈2 * Real.sqrt M⌉₊
  suffices key : ∀ m, ∀ (β : List (Label P TS)) (D : ACfg P), (alg4 (P := P)).run β = some D →
      totalGetTS β = M → pot B (D.loc p).pc ≤ m →
      ∃ k, (((alg4 (P := P)).soloStep p)^[k] D).pend p = none from
    key _ α C h rfl le_rfl
  intro m
  induction m with
  | zero =>
    intro β D hD hβ hm
    refine ⟨0, ?_⟩
    have h1 := inv1_of_run hD
    simp only [Function.iterate_zero, id]
    by_contra hp
    cases hpc : (D.loc p).pc with
    | idle => exact hp ((h1.idle p).2 hpc)
    | _ =>
      rw [hpc] at hm
      simp only [pot, nonpos_iff_eq_zero] at hm
      revert hm; rename_i a; cases a <;> simp
  | succ m ih =>
    intro β D hD hβ hm
    by_cases hp : D.pend p = none
    · exact ⟨0, hp⟩
    have hsome := (alg4 (P := P)).step_nextLabel_isSome D p hp
    obtain ⟨D', hD'⟩ := Option.isSome_iff_exists.1 hsome
    have hsolo : (alg4 (P := P)).soloStep p D = D' := by
      simp [Impl.soloStep, hp, hD']
    unfold Impl.nextLabel at hD'
    split at hD'
    · -- an access
      have hlt : pot B (D'.loc p).pc < pot B (D.loc p).pc := pot_step (M := M) hD (le_of_eq hβ) hD'
      have hrun : (alg4 (P := P)).run (β ++ [.tau p]) = some D' := by
        rw [Impl.run_append_of_eq _ hD, Impl.runFrom_singleton]; exact hD'
      obtain ⟨k, hk⟩ := ih (β ++ [.tau p]) D' hrun (by rw [totalGetTS_tau, hβ]) (by omega)
      exact ⟨k + 1, by rw [Function.iterate_succ_apply, hsolo]; exact hk⟩
    · -- a response
      refine ⟨1, ?_⟩
      simp only [Function.iterate_one, hsolo]
      rw [(step_ret' hD').2.1, Function.update_self]

end Cslib.SharedMemory.Timestamp.Alg4
