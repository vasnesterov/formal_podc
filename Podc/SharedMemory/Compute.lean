import Cslib.Computability.Distributed.SharedMemory.Model

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Model.lean

/-!
# Computable steps

`Impl.step` decides the invocation discipline `allowed` and the equality of responses
classically, so concrete executions cannot be evaluated with `decide`. Given decidability
instances, `Impl.cstep` is a computable copy of the step function (`Impl.step_eq_cstep`), and
`Impl.crunFrom` / `Impl.crun` the corresponding runs (`Impl.runFrom_eq_crunFrom`,
`Impl.run_eq_crun`, `Impl.valid_of_crun`): a concrete execution can then be checked by
evaluating `crun`.
-/

namespace Cslib.SharedMemory

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

namespace Impl

variable [DecidableEq P] [DecidableEq ι] [DecidableEq A.Resp] (I : Impl A B P L)
  [∀ p o, Decidable (I.allowed p o)]

/-- A computable copy of `Impl.step`. -/
def cstep (C : Config A B P L) : Label P A → Option (Config A B P L)
  | .inv p o =>
    if C.pend p = none ∧ I.allowed p o then
      some { C with pend := Function.update C.pend p (some o),
                    loc := Function.update C.loc p (I.invoke p (C.loc p) o) }
    else none
  | .tau p =>
    if C.pend p = none then none else
    match I.act p (C.loc p) with
    | .access i o k =>
      some { C with mem := Function.update C.mem i ((B i).δ (C.mem i) o).1,
                    loc := Function.update C.loc p (k ((B i).δ (C.mem i) o).2) }
    | .ret _ _ => none
  | .ret p r =>
    if C.pend p = none then none else
    match I.act p (C.loc p) with
    | .access _ _ _ => none
    | .ret r' l =>
      if r = r' then
        some { C with pend := Function.update C.pend p none, loc := Function.update C.loc p l }
      else none

lemma step_eq_cstep (C : Config A B P L) (ℓ : Label P A) : I.step C ℓ = I.cstep C ℓ := by
  cases ℓ with
  | inv p o => simp only [step, cstep]; congr 1
  | tau p => rfl
  | ret p r =>
    simp only [step, cstep]
    split_ifs
    · rfl
    · generalize I.act p (C.loc p) = a
      cases a with
      | access i o k => rfl
      | ret r' l => simp only; congr 1

/-- `Impl.runFrom` with `cstep`. -/
def crunFrom (C : Config A B P L) : List (Label P A) → Option (Config A B P L)
  | [] => some C
  | ℓ :: α => (I.cstep C ℓ).bind fun C' => crunFrom C' α

/-- `Impl.run` with `cstep`. -/
def crun (α : List (Label P A)) : Option (Config A B P L) := I.crunFrom I.initCfg α

lemma runFrom_eq_crunFrom (C : Config A B P L) (α : List (Label P A)) :
    I.runFrom C α = I.crunFrom C α := by
  induction α generalizing C with
  | nil => rfl
  | cons ℓ α ih => simp only [runFrom_cons, crunFrom, step_eq_cstep, ih]

lemma run_eq_crun (α : List (Label P A)) : I.run α = I.crun α :=
  I.runFrom_eq_crunFrom _ α

lemma valid_of_crun {α : List (Label P A)} (h : (I.crun α).isSome = true) : I.Valid α := by
  rw [Valid, run_eq_crun]
  exact Option.isSome_iff_exists.1 h

end Impl

end Cslib.SharedMemory
