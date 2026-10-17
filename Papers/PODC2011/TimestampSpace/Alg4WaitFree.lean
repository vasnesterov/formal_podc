import Papers.PODC2011.TimestampSpace.Alg4Space
import Cslib.Computability.Distributed.SharedMemory.Mutex
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Task

/-!
# Algorithms 3 and 4 are wait-free for boundedly many `getTS` calls (Lemma 6.14)

With at most `M` `getTS` invocations every access has index `≤ B = ⌈2√M⌉` (Lemma 6.5), so the
while loop reads at most `B` registers and the for loop has at most `B` iterations; the
potential `pot B` of the local state strictly decreases with every step of the process.

* `alg4_waitFreeUpTo`: in every infinite execution with at most `M` `getTS` invocations, a
  process whose operation stays pending takes only finitely many steps (by the library's
  `Impl.waitFreeOn_of_cfgPotential` with the potential `pot`). (CSLib's `WaitFree`
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

/-- Wait-freedom restricted to infinite executions with at most `M` `getTS` invocations (the
library's `Impl.WaitFreeOn` for the executions with `totalGetTS ≤ M`). -/
abbrev WaitFreeUpTo {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
    (I : Impl TS B P L) (M : ℕ) : Prop :=
  I.WaitFreeOn fun α => totalGetTS α ≤ M

/-- `WaitFreeUpTo`, unfolded: in every infinite execution with at most `M` `getTS` invocations, a
process whose operation stays pending takes only finitely many steps. -/
lemma waitFreeUpTo_iff {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
    (I : Impl TS B P L) (M : ℕ) :
    WaitFreeUpTo I M ↔ ∀ e : I.InfExec, (∀ T, totalGetTS ((List.range T).map e.lbl) ≤ M) →
      ∀ (p : P) (n : ℕ), (∀ t ≥ n, (e.cfg t).pend p ≠ none) → ∃ N, ∀ t ≥ N, e.lbl t ≠ .tau p :=
  Iff.rfl

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

/-- **Lemma 6.14** (wait-freedom for at most `M` `getTS` calls). -/
theorem alg4_waitFreeUpTo (M : ℕ) : WaitFreeUpTo (alg4 (P := P)) M := by
  refine Impl.waitFreeOn_of_cfgPotential _ (fun p C => pot ⌈2 * Real.sqrt M⌉₊ (C.loc p).pc)
    fun p α C ℓ C' hα hM hs hp hp' => ?_
  have hM' : totalGetTS α ≤ M :=
    le_trans (by simp [totalGetTS, List.countP_append]) hM
  rcases Impl.step_tau_or_other _ hs hp hp' with rfl | ⟨hq, hloc⟩
  · have := pot_step hα hM' hs
    exact ⟨this.le, fun _ => this⟩
  · simp only [hloc]
    exact ⟨le_rfl, fun h => absurd (by rw [h]; rfl) hq⟩

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
