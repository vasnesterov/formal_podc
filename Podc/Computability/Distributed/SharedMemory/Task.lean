import Cslib.Computability.Distributed.SharedMemory.Task

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Task.lean (append to the
-- existing file)

/-!
# Tasks: inputs, outputs and one-shot executions under extensions

Additions to `Cslib/Computability/Distributed/SharedMemory/Task.lean`.

## Main statements

* `outputs_append`, `outputs_concat`, `outputs_concat_of_ne`, `outputs_append_of_ne_none`,
  `outputs_append_ne_none`, `outputs_append_inv`, `outputs_append_tau`: the output of a process
  (its first response) after extending the execution.
* `outputs_ne_none_of_mem`, `outputs_eq_none_of_proc_ne`.
* `inputs_append_of_ne_none`: an input, once given, does not change.
* `OneShot.append_inv`, `OneShot.append_of_opsOf_nil`: extending one-shot executions.
-/

namespace Cslib.SharedMemory

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-! ### Outputs -/

lemma outputs_append (α β : List (Label P A)) (p : P) :
    outputs (α ++ β) p = (outputs α p).or (outputs β p) := by
  simp [outputs, respsOf_append, List.head?_append]

lemma outputs_concat (α : List (Label P A)) (ℓ : Label P A) (p : P) :
    outputs (α ++ [ℓ]) p = (outputs α p).or (ℓ.retOf p) := by
  rw [outputs_append]; congr 1; cases h : ℓ.retOf p <;> simp [outputs, h]

/-- Appending a label that is not a response of `p` does not change the output of `p`. -/
lemma outputs_concat_of_ne {α : List (Label P A)} {ℓ : Label P A} {p : P}
    (h : ∀ r, ℓ ≠ .ret p r) : outputs (α ++ [ℓ]) p = outputs α p := by
  simp only [outputs, respsOf_concat_of_ne h]

/-- An output, once given, does not change. -/
lemma outputs_append_of_ne_none {α : List (Label P A)} (β : List (Label P A)) {p : P}
    (h : outputs α p ≠ none) : outputs (α ++ β) p = outputs α p := by
  rw [outputs_append]
  obtain ⟨r, hr⟩ := Option.ne_none_iff_exists'.1 h
  simp [hr]

/-- A process that has output keeps its output. -/
lemma outputs_append_ne_none {α : List (Label P A)} (β : List (Label P A)) {p : P}
    (h : outputs α p ≠ none) : outputs (α ++ β) p ≠ none := by
  rwa [outputs_append_of_ne_none β h]

@[simp] lemma outputs_append_inv (α : List (Label P A)) (p q : P) (o : A.Op) :
    outputs (α ++ [.inv p o]) q = outputs α q := outputs_concat_of_ne (by simp)

@[simp] lemma outputs_append_tau (α : List (Label P A)) (p q : P) :
    outputs (α ++ [.tau p]) q = outputs α q := outputs_concat_of_ne (by simp)

lemma outputs_ne_none_of_mem {α : List (Label P A)} {p : P} {r : A.Resp}
    (h : Label.ret p r ∈ α) : outputs α p ≠ none := by
  unfold outputs respsOf
  intro hn
  rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at hn
  simpa using hn _ h

lemma outputs_eq_none_of_proc_ne {α : List (Label P A)} {p : P} (h : ∀ ℓ ∈ α, ℓ.proc ≠ p) :
    outputs α p = none := by
  simp [outputs, respsOf_eq_nil_of_proc_ne h]

/-! ### Inputs -/

/-- An input, once given, does not change. -/
lemma inputs_append_of_ne_none {α : List (Label P A)} (β : List (Label P A)) {p : P}
    (h : inputs α p ≠ none) : inputs (α ++ β) p = inputs α p := by
  simp only [inputs, opsOf_append] at h ⊢
  rw [List.head?_append]
  cases hh : (opsOf α p).head? with
  | none => exact absurd hh h
  | some x => rfl

/-! ### One-shot executions -/

/-- A process that has not invoked anything may invoke an operation in a one-shot execution. -/
lemma OneShot.append_inv {α : List (Label P A)} (h : OneShot α) {p : P} (hp : opsOf α p = [])
    (o : A.Op) : OneShot (α ++ [.inv p o]) := by
  intro q
  by_cases hq : q = p
  · subst hq; simp [opsOf_append, hp]
  · have := h q
    simp only [opsOf_append, opsOf_cons, opsOf_nil, List.length_append]
    rw [Label.invOf_eq_none_of_proc_ne (by simpa [Label.proc] using Ne.symm hq)]
    simpa using this

/-- Appending labels without invocations keeps an execution one-shot. -/
lemma OneShot.append_of_opsOf_nil {α β : List (Label P A)} (h : OneShot α)
    (hβ : ∀ p, opsOf β p = []) : OneShot (α ++ β) := by
  intro p; simpa [opsOf_append, hβ p] using h p

end Cslib.SharedMemory
