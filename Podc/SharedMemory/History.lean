import Cslib.Computability.Distributed.SharedMemory.History

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/History.lean

/-!
# More history API

Small additions to CSLib's `History.lean`, used by many invariant-based proofs:

* `PrefixClosed E` — a set of executions closed under prefixes (usage disciplines such as
  one-shot executions);
* `Label.isTauOf p` — `ℓ` is an internal step of `p` (as a `Bool`, for counting steps);
* `curOp α p` — the *current* operation instance of `p`: the instance of its pending operation
  (if any), otherwise of its next one; it has not completed (`not_completed_curOp`); with
  `@[simp]` lemmas for appending labels;
* `opOf_append_of_eq_some`, `respOf_append_of_eq_some` — the operation/response of an instance
  does not change when the execution is extended; `respOf_append_of_not_ret` — nor when a label
  other than a response is appended;
* `linState_append`, `linState_concat` — the abstract state after a concatenation of
  sequential histories.
-/

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec}

/-- A set of finite executions that is closed under taking prefixes. -/
def PrefixClosed (E : List (Label P A) → Prop) : Prop :=
  ∀ α β, E (α ++ β) → E α

lemma PrefixClosed.of_prefix {E : List (Label P A) → Prop} (hE : PrefixClosed E)
    {α β : List (Label P A)} (h : α <+: β) (hβ : E β) : E α := by
  obtain ⟨γ, rfl⟩ := h; exact hE α γ hβ

lemma prefixClosed_true : PrefixClosed (fun _ : List (Label P A) => True) :=
  fun _ _ _ => trivial

variable [DecidableEq P]

namespace Label

/-- `ℓ` is an internal step (base-object access) of `p`. -/
def isTauOf (p : P) : Label P A → Bool
  | .tau q => decide (q = p)
  | _ => false

@[simp] lemma isTauOf_tau (p q : P) : (tau q : Label P A).isTauOf p = decide (q = p) := rfl
@[simp] lemma isTauOf_inv (p q : P) (o : A.Op) : (inv q o : Label P A).isTauOf p = false := rfl
@[simp] lemma isTauOf_ret (p q : P) (r : A.Resp) : (ret q r : Label P A).isTauOf p = false := rfl

lemma isTauOf_eq_true_iff {p : P} {ℓ : Label P A} : ℓ.isTauOf p = true ↔ ℓ = .tau p := by
  cases ℓ <;> simp [eq_comm]

end Label

/-! ### The current operation instance of a process -/

/-- The current operation instance of `p` after `α`: the instance of its pending operation if
there is one, otherwise the instance of its next operation. -/
abbrev curOp (α : List (Label P A)) (p : P) : OpId P := (p, (respsOf α p).length)

@[simp] lemma curOp_nil (p : P) : curOp ([] : List (Label P A)) p = (p, 0) := rfl

@[simp] lemma curOp_append_inv (α : List (Label P A)) (p q : P) (o : A.Op) :
    curOp (α ++ [.inv p o]) q = curOp α q := by
  simp [curOp]

@[simp] lemma curOp_append_tau (α : List (Label P A)) (p q : P) :
    curOp (α ++ [.tau p]) q = curOp α q := by
  simp [curOp]

@[simp] lemma curOp_append_ret_self (α : List (Label P A)) (p : P) (r : A.Resp) :
    curOp (α ++ [.ret p r]) p = (p, (respsOf α p).length + 1) := by
  simp [curOp]

lemma curOp_append_ret_of_ne (α : List (Label P A)) {p q : P} (r : A.Resp) (h : p ≠ q) :
    curOp (α ++ [.ret p r]) q = curOp α q := by
  simp [curOp, h]

lemma curOp_append_of_proc_ne (α : List (Label P A)) {ℓ : Label P A} {q : P}
    (h : ℓ.proc ≠ q) : curOp (α ++ [ℓ]) q = curOp α q := by
  simp [curOp, Label.retOf_eq_none_of_proc_ne h]

/-- The current operation instance of a process has not completed. -/
@[simp] lemma not_completed_curOp (α : List (Label P A)) (p : P) :
    ¬ Completed α (curOp α p) := by
  simp [Completed]

/-! ### Operations and responses of instances in extensions -/

lemma Invoked.of_opOf_eq_some {α : List (Label P A)} {x : OpId P} {o : A.Op}
    (h : opOf α x = some o) : Invoked α x := by
  simp only [opOf] at h; exact (List.getElem?_eq_some_iff.1 h).1

lemma Completed.of_respOf_eq_some {α : List (Label P A)} {x : OpId P} {r : A.Resp}
    (h : respOf α x = some r) : Completed α x := by
  simp only [respOf] at h; exact (List.getElem?_eq_some_iff.1 h).1

lemma opOf_append_of_eq_some {α : List (Label P A)} {x : OpId P} {o : A.Op}
    (h : opOf α x = some o) (β : List (Label P A)) : opOf (α ++ β) x = some o := by
  rw [opOf_append_of_invoked (Invoked.of_opOf_eq_some h), h]

lemma respOf_append_of_eq_some {α : List (Label P A)} {x : OpId P} {r : A.Resp}
    (h : respOf α x = some r) (β : List (Label P A)) : respOf (α ++ β) x = some r := by
  rw [respOf_append_of_completed (Completed.of_respOf_eq_some h), h]

/-- Appending a label that is not a response does not change the responses of instances. -/
lemma respOf_append_of_not_ret {α : List (Label P A)} {ℓ : Label P A}
    (hℓ : ∀ p r, ℓ ≠ .ret p r) (x : OpId P) : respOf (α ++ [ℓ]) x = respOf α x := by
  cases ℓ with
  | ret p r => exact absurd rfl (hℓ p r)
  | inv p o => simp [respOf]
  | tau p => simp [respOf]

end Cslib.SharedMemory

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec}

/-! ### The state after a sequential history -/

@[simp] lemma linState_nil : linState ([] : List (OpId P × A.Op)) = A.init := rfl

lemma linState_append (L M : List (OpId P × A.Op)) :
    linState (L ++ M) = A.runOps (linState L) (M.map Prod.snd) := by
  simp [linState, ObjSpec.runOps_append]

@[simp] lemma linState_concat (L : List (OpId P × A.Op)) (x : OpId P) (o : A.Op) :
    linState (L ++ [(x, o)]) = (A.δ (linState L) o).1 := by
  simp [linState_append]

end Cslib.SharedMemory
