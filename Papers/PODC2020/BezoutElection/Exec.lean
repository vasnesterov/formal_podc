import Papers.PODC2020.BezoutElection.Defs

/-!
# Generic lemmas on the outputs of executions

CSLib candidates (they hold for any implementation `Impl A B P L`). The lemmas on pending
operations along infinite executions are in `Podc.SharedMemory.Progress`
(`Impl.step_pend_none`, `Impl.InfExec.exists_ret_between`).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory

namespace BezoutElection

variable {A : ObjSpec} {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {P L : Type} [DecidableEq P]
  {I : Impl A B P L}

-- CSLib candidate
lemma outputs_append (α β : List (Label P A)) (p : P) :
    outputs (α ++ β) p = (outputs α p).or (outputs β p) := by
  simp [outputs, respsOf_append, List.head?_append]

-- CSLib candidate
lemma outputs_ne_none_of_mem {α : List (Label P A)} {p : P} {r : A.Resp}
    (h : Label.ret p r ∈ α) : outputs α p ≠ none := by
  unfold outputs respsOf
  intro hn
  rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at hn
  simpa using hn _ h

lemma outputs_eq_none_of_proc_ne {α : List (Label P A)} {p : P} (h : ∀ ℓ ∈ α, ℓ.proc ≠ p) :
    outputs α p = none := by
  simp [outputs, respsOf_eq_nil_of_proc_ne h]

end BezoutElection
