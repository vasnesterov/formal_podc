import Cslib.Computability.Distributed.SharedMemory.History
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/History.lean (append to the
-- existing file)

/-!
# Histories: appending one label, real-time order, counting invocations

Additions to `Cslib/Computability/Distributed/SharedMemory/History.lean`: bookkeeping lemmas for
invariant proofs over executions extended one label at a time.

## Main statements

* `Label.eq_inv_of_invOf_eq_some`, `Label.eq_ret_of_retOf_eq_some`: recovering a label.
* `opsOf_append_tau`, `opsOf_append_ret`, `respsOf_append_inv`, `respsOf_append_tau`,
  `respsOf_append_ret_of_ne`, `opOf_append_tau`, `opOf_append_ret`: operations/responses after
  appending a label of a given shape.
* `opOf_concat_cases`, `respOf_concat_cases`: an operation (response) known after appending one
  label was known before, or it is the appended label.
* `completed_append_ret`, `completed_append_ret_of_ne`, `completed_append_of_not_ret`,
  `respOf_append_ret_of_ne`: completed instances after appending one label.
* `precedes_concat`, `Precedes.of_concat_of_not_ret`, `not_precedes_append`: real-time order
  after appending labels.
* `opsOf_filter_proc`, `respsOf_filter_proc`: restricting an execution to the labels of `p`.
* `Label.isInv`, `numInv`, `numInv_eq_sum`: the number of invocations of an execution.
-/

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} [DecidableEq P]

namespace Label

/-- A label at which `p` invokes `o` is the invocation `inv p o`. -/
lemma eq_inv_of_invOf_eq_some {ℓ : Label P A} {p : P} {o : A.Op} (h : ℓ.invOf p = some o) :
    ℓ = .inv p o := by
  cases ℓ with
  | inv q o' => simp only [invOf_inv] at h; split_ifs at h with hq; cases h; rw [hq]
  | ret q r => simp at h
  | tau q => simp at h

/-- A label at which `p` returns `r` is the response `ret p r`. -/
lemma eq_ret_of_retOf_eq_some {ℓ : Label P A} {p : P} {r : A.Resp} (h : ℓ.retOf p = some r) :
    ℓ = .ret p r := by
  cases ℓ with
  | ret q r' => simp only [retOf_ret] at h; split_ifs at h with hq; cases h; rw [hq]
  | inv q o => simp at h
  | tau q => simp at h

end Label

/-! ### Operations and responses after appending one label -/

@[simp] lemma opsOf_append_tau (α : List (Label P A)) (p q : P) :
    opsOf (α ++ [.tau p]) q = opsOf α q := by simp [opsOf_append]

@[simp] lemma opsOf_append_ret (α : List (Label P A)) (p q : P) (r : A.Resp) :
    opsOf (α ++ [.ret p r]) q = opsOf α q := by simp [opsOf_append]

@[simp] lemma respsOf_append_inv (α : List (Label P A)) (p q : P) (o : A.Op) :
    respsOf (α ++ [.inv p o]) q = respsOf α q := by simp [respsOf_append]

@[simp] lemma respsOf_append_tau (α : List (Label P A)) (p q : P) :
    respsOf (α ++ [.tau p]) q = respsOf α q := by simp [respsOf_append]

lemma respsOf_append_ret_of_ne (α : List (Label P A)) {p q : P} (r : A.Resp) (h : q ≠ p) :
    respsOf (α ++ [.ret p r]) q = respsOf α q := by simp [respsOf_append, Ne.symm h]

@[simp] lemma opOf_append_tau (α : List (Label P A)) (p : P) (x : OpId P) :
    opOf (α ++ [.tau p]) x = opOf α x := by simp [opOf]

@[simp] lemma opOf_append_ret (α : List (Label P A)) (p : P) (r : A.Resp) (x : OpId P) :
    opOf (α ++ [.ret p r]) x = opOf α x := by simp [opOf]

/-- An operation known after appending `ℓ` was known before, or `ℓ` is its invocation. -/
lemma opOf_concat_cases {α : List (Label P A)} {ℓ : Label P A} {x : OpId P} {o : A.Op}
    (h : opOf (α ++ [ℓ]) x = some o) :
    opOf α x = some o ∨ (ℓ = .inv x.1 o ∧ x.2 = (opsOf α x.1).length) := by
  simp only [opOf, opsOf_concat] at h ⊢
  rcases lt_or_ge x.2 (opsOf α x.1).length with hlt | hge
  · left; rwa [List.getElem?_append_left hlt] at h
  · right
    rw [List.getElem?_append_right hge] at h
    cases hl : ℓ.invOf x.1 with
    | none => simp [hl] at h
    | some o' =>
      rw [hl] at h
      rcases List.getElem?_eq_some_iff.1 h with ⟨h1, h2⟩
      simp only [Option.toList_some, List.length_singleton, List.getElem_singleton] at h1 h2
      subst h2; exact ⟨Label.eq_inv_of_invOf_eq_some hl, by omega⟩

/-- A response known after appending `ℓ` was known before, or `ℓ` is this response. -/
lemma respOf_concat_cases {α : List (Label P A)} {ℓ : Label P A} {x : OpId P} {r : A.Resp}
    (h : respOf (α ++ [ℓ]) x = some r) :
    respOf α x = some r ∨ (ℓ = .ret x.1 r ∧ x.2 = (respsOf α x.1).length) := by
  simp only [respOf, respsOf_concat] at h ⊢
  rcases lt_or_ge x.2 (respsOf α x.1).length with hlt | hge
  · left; rwa [List.getElem?_append_left hlt] at h
  · right
    rw [List.getElem?_append_right hge] at h
    cases hl : ℓ.retOf x.1 with
    | none => simp [hl] at h
    | some r' =>
      rw [hl] at h
      rcases List.getElem?_eq_some_iff.1 h with ⟨h1, h2⟩
      simp only [Option.toList_some, List.length_singleton, List.getElem_singleton] at h1 h2
      subst h2; exact ⟨Label.eq_ret_of_retOf_eq_some hl, by omega⟩

/-- The response of an instance of another process does not change when `p` returns. -/
lemma respOf_append_ret_of_ne {α : List (Label P A)} {p : P} {r : A.Resp} {x : OpId P}
    (hx : x.1 ≠ p) : respOf (α ++ [.ret p r]) x = respOf α x :=
  respOf_concat_of_ne fun _ h => hx (Label.ret.inj h).1.symm

/-! ### Completed instances after appending one label -/

/-- After `p` returns, the completed instances are the old ones and the current one of `p`. -/
lemma completed_append_ret {α : List (Label P A)} {p : P} {r : A.Resp} (x : OpId P) :
    Completed (α ++ [.ret p r]) x ↔ Completed α x ∨ x = (p, (respsOf α p).length) := by
  obtain ⟨q, k⟩ := x
  simp only [Completed, respsOf_append, respsOf_cons, Label.retOf_ret, respsOf_nil,
    List.append_nil, List.length_append, Prod.mk.injEq]
  by_cases hq : p = q
  · subst hq; simp; omega
  · simp [hq, Ne.symm hq]

lemma completed_append_ret_of_ne {α : List (Label P A)} {p : P} {r : A.Resp} {x : OpId P}
    (hx : x.1 ≠ p) : Completed (α ++ [.ret p r]) x ↔ Completed α x := by
  rw [completed_append_ret]
  exact ⟨fun h => h.resolve_right fun h => hx (by rw [h]), Or.inl⟩

/-- Appending a label that is not a response does not complete any instance. -/
lemma completed_append_of_not_ret {α : List (Label P A)} {ℓ : Label P A}
    (hℓ : ∀ p r, ℓ ≠ .ret p r) (x : OpId P) : Completed (α ++ [ℓ]) x ↔ Completed α x := by
  simp only [Completed, respsOf_concat_of_ne (hℓ x.1)]

/-! ### Real-time order after appending labels -/

/-- Real-time order after appending one label: it held before, or `a` has completed and `b` has
not been invoked after the label. -/
lemma precedes_concat {α : List (Label P A)} {ℓ : Label P A} {a b : OpId P}
    (h : Precedes (α ++ [ℓ]) a b) :
    Precedes α a b ∨ (Completed (α ++ [ℓ]) a ∧ ¬ Invoked (α ++ [ℓ]) b) := by
  obtain ⟨β, γ, hsplit, h1, h2⟩ := h
  induction γ using List.reverseRecOn with
  | nil => right; simp only [List.append_nil] at hsplit; subst hsplit; exact ⟨h1, h2⟩
  | append_singleton γ x _ =>
    left
    rw [← List.append_assoc] at hsplit
    exact ⟨β, γ, (List.append_inj' hsplit rfl).1, h1, h2⟩

/-- Appending a label that is not a response creates no real-time precedence. -/
lemma Precedes.of_concat_of_not_ret {α : List (Label P A)} {ℓ : Label P A} {a b : OpId P}
    (hℓ : ∀ q r, ℓ ≠ .ret q r) (h : Precedes (α ++ [ℓ]) a b) : Precedes α a b := by
  rcases precedes_concat h with h | ⟨h1, h2⟩
  · exact h
  · exact ⟨α, [], by simp, (completed_append_of_not_ret hℓ a).1 h1, fun h3 => h2 h3.mono⟩

/-- Real-time precedence towards an already invoked instance is not created by new labels. -/
lemma not_precedes_append {α β : List (Label P A)} {a b : OpId P} (hb : Invoked α b)
    (h : ¬ Precedes α a b) : ¬ Precedes (α ++ β) a b :=
  fun h' => h (h'.of_append_of_invoked hb)

/-! ### Restricting to one process -/

lemma opsOf_filter_proc (α : List (Label P A)) (p : P) :
    opsOf (α.filter (fun ℓ => decide (ℓ.proc = p))) p = opsOf α p := by
  induction α with
  | nil => rfl
  | cons ℓ α ih =>
    by_cases h : ℓ.proc = p
    · simp [h, ih]
    · simp [h, ih, Label.invOf_eq_none_of_proc_ne h]

lemma respsOf_filter_proc (α : List (Label P A)) (p : P) :
    respsOf (α.filter (fun ℓ => decide (ℓ.proc = p))) p = respsOf α p := by
  induction α with
  | nil => rfl
  | cons ℓ α ih =>
    by_cases h : ℓ.proc = p
    · simp [h, ih]
    · simp [h, ih, Label.retOf_eq_none_of_proc_ne h]

end Cslib.SharedMemory

/-! ### Counting invocations -/

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec}

namespace Label

/-- The label is an invocation. -/
def isInv : Label P A → Bool
  | .inv _ _ => true
  | _ => false

@[simp] lemma isInv_inv (p : P) (o : A.Op) : (inv p o : Label P A).isInv = true := rfl
@[simp] lemma isInv_ret (p : P) (r : A.Resp) : (ret p r : Label P A).isInv = false := rfl
@[simp] lemma isInv_tau (p : P) : (tau p : Label P A).isInv = false := rfl

end Label

/-- The number of invocations in an execution. -/
def numInv (α : List (Label P A)) : ℕ := α.countP Label.isInv

@[simp] lemma numInv_nil : numInv ([] : List (Label P A)) = 0 := rfl

@[simp] lemma numInv_append (α β : List (Label P A)) :
    numInv (α ++ β) = numInv α + numInv β := List.countP_append ..

@[simp] lemma numInv_cons (ℓ : Label P A) (α : List (Label P A)) :
    numInv (ℓ :: α) = numInv α + if ℓ.isInv then 1 else 0 := by
  simp [numInv, List.countP_cons]

/-- The number of invocations is the sum over the processes of their numbers of invocations. -/
lemma numInv_eq_sum [Fintype P] [DecidableEq P] (α : List (Label P A)) :
    numInv α = ∑ p, (opsOf α p).length := by
  induction α with
  | nil => simp
  | cons ℓ α ih =>
    simp only [numInv_cons, ih, opsOf_cons, List.length_append, Finset.sum_add_distrib]
    cases ℓ with
    | inv q o =>
      have h1 : ∀ p, ((Label.inv q o : Label P A).invOf p).toList.length =
          if q = p then 1 else 0 := by
        intro p; simp only [Label.invOf_inv]; split_ifs <;> rfl
      simp only [h1, Finset.sum_ite_eq, Finset.mem_univ, ite_true, Label.isInv_inv]; omega
    | ret q r => simp
    | tau q => simp

end Cslib.SharedMemory
