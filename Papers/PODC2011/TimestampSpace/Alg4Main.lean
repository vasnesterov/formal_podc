import Papers.PODC2011.TimestampSpace.Alg4WaitFree

/-!
# Theorem 1.3 (upper bound): one-shot timestamps from `⌈2√n⌉ ≤ 2⌈√n⌉` registers

Summary of Section 6 for Algorithms 3 and 4 (`alg4`):
* `alg4_correct` (Lemma 6.4): every execution satisfies `TSCorrect` (no bound on the number of
  `getTS` calls needed);
* `alg4_space` (Lemma 6.5): with at most `M` `getTS` calls every access touches only
  `R[1..⌈2√M⌉]`; `alg4_space_step` states it for the steps of an execution;
* `alg4_waitFreeUpTo` (Lemma 6.14): wait-free in infinite executions with at most `M` calls;
* `alg4_isTS`: `alg4` is a (long-lived and one-shot) timestamp implementation in the sense of
  `IsTS` (correct + non-deterministic solo termination);
* `theorem_1_3`: for `n` processes in the one-shot setting: correct, wait-free on one-shot
  executions, and every access is to a register among `R[1..⌈2√n⌉] ⊆ R[1..2⌈√n⌉]`.

Model deviation (also in the module docstring of `Alg4.lean`): the paper's `scan` is an
(obstruction-free, but here wait-free because there are finitely many writes) double collect
that the paper itself treats as atomic; we model it as an atomic snapshot primitive of a single
base object holding the register array. The space bound counts the register indices accessed.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.Alg4

open Cslib.SharedMemory

variable {P : Type} [DecidableEq P]

/-- `alg4` is a timestamp implementation (correct on all executions, solo-terminating), both
long-lived and one-shot. -/
theorem alg4_isTS (os : Bool) : IsTS (alg4 (P := P)) os where
  allowed _ _ := trivial
  correct α hα _ := alg4_correct α hα
  progress _ _ p hα _ _ := alg4_solo hα p

/-- `alg4` is obstruction-free (for any number of `getTS` calls). -/
theorem alg4_obstructionFree : (alg4 (P := P)).ObstructionFree :=
  (soloTerm_false_iff _).1 (alg4_isTS false).progress

/-- Lemma 6.5 for the steps of an execution: if `α = β ++ [tau p] ++ γ` has at most `M`
`getTS` invocations, the primitive applied by `p` at that step touches only `R[1..⌈2√M⌉]`. -/
theorem alg4_space_step {M : ℕ} {β γ : List (Label P TS)} {p : P}
    (hv : (alg4 (P := P)).Valid (β ++ [.tau p] ++ γ))
    (hM : totalGetTS (β ++ [.tau p] ++ γ) ≤ M) :
    ∃ C i o k, (alg4 (P := P)).run β = some C ∧
      (alg4 (P := P)).act p (C.loc p) = .access i o k ∧
      1 ≤ o.idx ∧ o.idx ≤ ⌈2 * Real.sqrt M⌉₊ := by
  have hv1 : (alg4 (P := P)).Valid (β ++ [.tau p]) := hv.of_append
  obtain ⟨C', hC'⟩ := hv1
  obtain ⟨C, hC, hs⟩ := run_append_singleton hC'
  obtain ⟨h0, -, i, o, k, hact, -⟩ := Impl.step_tau hs
  have hM' : totalGetTS β ≤ M := by
    refine le_trans ?_ hM
    simp only [totalGetTS, List.countP_append]; omega
  exact ⟨C, i, o, k, hC, hact, alg4_space hC hM' h0 hact⟩

/-- The total number of `getTS` invocations is the sum of the per-process counts. -/
lemma totalGetTS_eq_sum [Fintype P] (α : List (Label P TS)) :
    totalGetTS α = ∑ p, getTSCount α p := by
  induction α with
  | nil => simp [totalGetTS, getTSCount]
  | cons ℓ α ih =>
    have h : ∀ p, getTSCount (ℓ :: α) p = getTSCount [ℓ] p + getTSCount α p := fun p => by
      rw [show ℓ :: α = [ℓ] ++ α from rfl, getTSCount_append]
    simp only [h, Finset.sum_add_distrib, ← ih]
    simp only [totalGetTS, List.countP_cons]
    rw [add_comm]
    congr 1
    cases ℓ with
    | inv q o =>
      cases o with
      | getTS =>
        simp only [getTSCount, opsOf, List.filterMap_cons, List.filterMap_nil, Label.invOf_inv]
        rw [Finset.sum_eq_single q]
        · simp [TSOp.isGetTS]
        · intro x _ hx; simp [Ne.symm hx]
        · simp
      | compare a b =>
        simp only [getTSCount, opsOf, List.filterMap_cons, List.filterMap_nil, Label.invOf_inv]
        symm; apply Finset.sum_eq_zero; intro x _
        by_cases hx : q = x <;> simp [hx, TSOp.isGetTS]
    | ret q r => simp [getTSCount, opsOf, List.filterMap_cons]
    | tau q => simp [getTSCount, opsOf, List.filterMap_cons]

/-- In a one-shot execution there are at most `n = |P|` `getTS` invocations. -/
lemma totalGetTS_le_card [Fintype P] {α : List (Label P TS)} (h : Adm true α) :
    totalGetTS α ≤ Fintype.card P := by
  rw [totalGetTS_eq_sum]
  calc ∑ p, getTSCount α p ≤ ∑ _p : P, 1 := Finset.sum_le_sum fun p _ => h rfl p
    _ = Fintype.card P := by simp

lemma ceil_two_sqrt_le (n : ℕ) : ⌈2 * Real.sqrt n⌉₊ ≤ 2 * ⌈Real.sqrt n⌉₊ := by
  rw [Nat.ceil_le]
  push_cast
  have := Nat.le_ceil (Real.sqrt n)
  linarith

/-- **Theorem 1.3** (upper bound, Section 6): for `n` processes, Algorithms 3 and 4 form a
one-shot timestamp implementation that is
1. correct and solo-terminating (`IsTS … true`),
2. wait-free in every infinite one-shot execution, and
3. uses only the registers `R[1..⌈2√n⌉] ⊆ R[1..2⌈√n⌉]`: in every one-shot execution every
   access of every process has index between `1` and `⌈2√n⌉ ≤ 2⌈√n⌉`. -/
theorem theorem_1_3 [Fintype P] :
    IsTS (alg4 (P := P)) true ∧
    (∀ e : (alg4 (P := P)).InfExec, (∀ T, Adm true ((List.range T).map e.lbl)) →
      ∀ (p : P) (n : ℕ), (∀ t ≥ n, (e.cfg t).pend p ≠ none) → ∃ N, ∀ t ≥ N, e.lbl t ≠ .tau p) ∧
    (∀ (α : List (Label P TS)) (C : ACfg P) (p : P) (i : Unit) (o : MOp P)
      (k : (memObj P).Resp → Loc P), (alg4 (P := P)).run α = some C → Adm true α →
      C.pend p ≠ none → (alg4 (P := P)).act p (C.loc p) = .access i o k →
      1 ≤ o.idx ∧ o.idx ≤ ⌈2 * Real.sqrt (Fintype.card P)⌉₊ ∧
        o.idx ≤ 2 * ⌈Real.sqrt (Fintype.card P)⌉₊) := by
  refine ⟨alg4_isTS true, fun e he => alg4_waitFreeUpTo (Fintype.card P) e
    (fun T => totalGetTS_le_card (he T)), ?_⟩
  intro α C p i o k h hadm hp hact
  have := alg4_space h (totalGetTS_le_card hadm) hp hact
  exact ⟨this.1, this.2, this.2.trans (ceil_two_sqrt_le _)⟩

end Cslib.SharedMemory.Timestamp.Alg4
