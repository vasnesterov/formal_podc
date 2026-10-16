import Papers.PODC2011.TimestampSpace.SimpleAlgCorrect

/-!
# Algorithms 1 and 2 are not a long-lived timestamp implementation

Lemma 5.1 needs the one-shot restriction: for `n = 2` (one register, shared by processes `0`
and `1`) there is an execution in which each process calls `getTS` twice and the history
violates `TSCorrect`. Process `1` reads `R = 0` and stalls before writing; process `0` performs
two complete `getTS` operations (writing `1`, then `2`, returning `1` and `2`); process `1`
then writes `1` (the register *decreases* from `2` to `1`), returns, and performs a second
`getTS` returning `2` again. The second `getTS` of `0` (timestamp `2`) precedes the second
`getTS` of `1` (timestamp `2`), yet a later `compare(2, 2)` returns `false`.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.Timestamp.SimpleTS

open Cslib.SharedMemory

/-! ### A computable copy of the step function (for evaluating concrete executions) -/

section Compute

variable {n : ℕ}

/-- `Impl.step` of `alg n reread` with decidable conditions. -/
def cstep (reread : Bool) (C : Cfg n) : Label (Fin n) (tsObj ℕ) → Option (Cfg n)
  | .inv p o =>
    if (C.pend p).isNone then
      some { C with pend := Function.update C.pend p (some o),
                    loc := Function.update C.loc p (invoke (C.loc p) o) }
    else none
  | .tau p =>
    if (C.pend p).isNone then none else
    match act reread p (C.loc p) with
    | .access i o k =>
      some { C with mem := Function.update C.mem i ((Regs n i).δ (C.mem i) o).1,
                    loc := Function.update C.loc p (k ((Regs n i).δ (C.mem i) o).2) }
    | .ret _ _ => none
  | .ret p r =>
    if (C.pend p).isNone then none else
    match act reread p (C.loc p) with
    | .access _ _ _ => none
    | .ret r' l =>
      if r = r' then
        some { C with pend := Function.update C.pend p none, loc := Function.update C.loc p l }
      else none

lemma step_eq_cstep (reread : Bool) (C : Cfg n) (ℓ : Label (Fin n) (tsObj ℕ)) :
    (alg n reread).step C ℓ = cstep reread C ℓ := by
  cases ℓ with
  | inv p o =>
    simp only [Impl.step, cstep, alg]; by_cases h : C.pend p = none <;> simp [h]
  | tau p =>
    simp only [Impl.step, cstep, alg]; by_cases h : C.pend p = none
    · simp [h]
    · simp only [h, Option.isNone_iff_eq_none, ite_false]
      generalize act reread p (C.loc p) = a
      cases a <;> rfl
  | ret p r =>
    simp only [Impl.step, cstep, alg]; by_cases h : C.pend p = none
    · simp [h]
    · simp only [h, Option.isNone_iff_eq_none, ite_false]
      generalize act reread p (C.loc p) = a
      cases a with
      | access i o k => rfl
      | ret r' l => by_cases hr : r = r' <;> simp [hr]

/-- `Impl.runFrom` with `cstep`. -/
def crun (reread : Bool) (C : Cfg n) : Exec n → Option (Cfg n)
  | [] => some C
  | ℓ :: α => (cstep reread C ℓ).bind (fun C' => crun reread C' α)

lemma runFrom_eq_crun (reread : Bool) (C : Cfg n) (α : Exec n) :
    (alg n reread).runFrom C α = crun reread C α := by
  induction α generalizing C with
  | nil => rfl
  | cons ℓ α ih => simp only [Impl.runFrom_cons, crun, step_eq_cstep, ih]

end Compute

/-- The optional re-read step of process `p`. -/
def rrStep (reread : Bool) (p : Fin 2) : Exec 2 := if reread then [.tau p] else []

/-- Part 1: `1` reads `R = 0`; `0` runs `getTS` twice (returns `1`, then `2`). -/
def cex₁ (reread : Bool) : Exec 2 :=
  [.inv 1 .getTS, .tau 1,
    .inv 0 .getTS, .tau 0, .tau 0] ++ rrStep reread 0 ++ [.ret 0 (.inl 1),
    .inv 0 .getTS, .tau 0, .tau 0] ++ rrStep reread 0 ++ [.ret 0 (.inl 2)]

/-- Part 2: `1` writes `1`, returns `1`, then runs a second `getTS` returning `2`. -/
def cex₂ (reread : Bool) : Exec 2 :=
  [.tau 1] ++ rrStep reread 1 ++ [.ret 1 (.inl 1),
    .inv 1 .getTS, .tau 1, .tau 1] ++ rrStep reread 1 ++ [.ret 1 (.inl 2)]

/-- Part 3: `0` compares the two timestamps. -/
def cex₃ : Exec 2 := [.inv 0 (.compare 2 2), .ret 0 (.inr false)]

/-- The counterexample execution. -/
def cex (reread : Bool) : Exec 2 := cex₁ reread ++ cex₂ reread ++ cex₃

lemma cex_valid (reread : Bool) : (alg 2 reread).Valid (cex reread) := by
  refine Option.isSome_iff_exists.1 ?_
  rw [Impl.run, runFrom_eq_crun]
  cases reread <;> decide +kernel

/-- In the counterexample the register decreases: it holds `2` after part 1 and `1` after the
next step of process `1` (compare `mem_mono` for one-shot executions). -/
lemma cex_decrease (reread : Bool) :
    ((alg 2 reread).run (cex₁ reread)).map (fun C => C.mem 0) = some 2 ∧
      ((alg 2 reread).run (cex₁ reread ++ [.tau 1])).map (fun C => C.mem 0) = some 1 := by
  rw [Impl.run, Impl.run, runFrom_eq_crun, runFrom_eq_crun]
  cases reread <;> decide +kernel

lemma cex_count (reread : Bool) (p : Fin 2) : getTSCount (cex reread) p = 2 := by
  cases reread <;> fin_cases p <;> rfl

/-- **Lemma 5.1 is false without the one-shot restriction**: an execution of Algorithms 1
and 2 (`n = 2`) in which every process calls `getTS` twice violates the timestamp
specification. -/
theorem cex_not_correct (reread : Bool) : ¬ TSCorrect (cex reread) := by
  intro h
  have key := (h.order (0, 1) (1, 1) (0, 2) 2 2 (.compare 2 2) (.inr false)
    (by cases reread <;> rfl) (by cases reread <;> rfl) (by cases reread <;> rfl)
    (by cases reread <;> rfl)
    ⟨cex₁ reread, cex₂ reread ++ cex₃, by simp [cex], by unfold Completed; cases reread <;> decide,
      by unfold Invoked; cases reread <;> decide⟩
    ⟨cex₁ reread ++ cex₂ reread, cex₃, rfl, by unfold Completed; cases reread <;> decide,
      by unfold Invoked; cases reread <;> decide⟩
    (by cases reread <;> rfl) (by cases reread <;> rfl)).1 rfl
  simp at key

/-- Hence Algorithms 1 and 2 are not a long-lived timestamp implementation. -/
theorem not_isTS_longLived (reread : Bool) : ¬ IsTS (alg 2 reread) false := fun h =>
  cex_not_correct reread (h.correct _ (cex_valid reread) (adm_false _))

end Cslib.SharedMemory.Timestamp.SimpleTS
