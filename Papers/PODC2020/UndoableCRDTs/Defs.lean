import Mathlib

/-!
# Undoable CRDTs: definitions (Dolan, PODC 2020, Section 2)

S. Dolan, *Brief Announcement: The Only Undoable CRDTs are Counters*, PODC 2020
(arXiv:2006.10494).

* `OpSystem`: a set of states `S` with an initial state `s0` and a family of *partial*
  primitive operations `P`. Actions `P*` are lists of operations, applied left to right
  (`s · p · q = q (p s)`; `act s [p, q]`).
* `OpSystem.Commutative` (Axiom 1), `OpSystem.Undoable` (Axiom 2), `OpSystem.Reachable`.
* `CRDT`: an operation system with finitely many primitive operations, all states reachable,
  satisfying Axiom 1. `UndoableCRDT`: a CRDT also satisfying Axiom 2.
* `CRDTEquiv`: equivalence of CRDTs (Section 2.2).
* `CRDT.tuple`: the tuple construction (Section 2.3).
* `modCounter n`: the counter modulo `n` (Section 1.1); `modCounter 0` is the unbounded
  counter (its state type is `ZMod 0 = ℤ`, definitionally).
-/

universe u v u₁ v₁ u₂ v₂ w

namespace UndoableCRDTs

/-- States, an initial state and partial primitive operations (Section 2). An operation
`p : P` is a partial function `app p : S → Option S`. -/
structure OpSystem where
  /-- Abstract states. -/
  S : Type u
  /-- Primitive operations. -/
  P : Type v
  /-- The initial state `s₀`. -/
  s0 : S
  /-- `app p s = some t` iff `s · p` is well defined and equals `t`. -/
  app : P → S → Option S

namespace OpSystem

variable (C : OpSystem.{u, v})

/-- `s · a` for an action `a ∈ P*` (Section 2.1): the operations of the list are applied
from left to right; `none` when some operation does not apply. -/
def act : C.S → List C.P → Option C.S
  | s, [] => some s
  | s, p :: a => (C.app p s).bind fun t => act t a

/-- `s · a ok`: the action `a` is well defined in state `s`. -/
def Ok (s : C.S) (a : List C.P) : Prop := ∃ t, C.act s a = some t

/-- **Axiom 1 (Commutativity)**: if `s · p ok` and `s · q ok`, then `s · p · q ok`,
`s · q · p ok` and `s · p · q = s · q · p`. As in the paper, `p = q` is allowed. -/
def Commutative : Prop :=
  ∀ s p q, C.Ok s [p] → C.Ok s [q] →
    C.Ok s [p, q] ∧ C.Ok s [q, p] ∧ C.act s [p, q] = C.act s [q, p]

/-- **Axiom 2 (Undoability)**: if `s · p ok`, then there are primitive operations
`q₁, …, qₙ` with `s · p · q₁ ⋯ qₙ = s`. -/
def Undoable : Prop :=
  ∀ s p, C.Ok s [p] → ∃ qs : List C.P, C.act s (p :: qs) = some s

/-- All states are reachable from `s₀` by some action (Section 2). -/
def Reachable : Prop := ∀ s, ∃ a, C.act C.s0 a = some s

@[simp] lemma act_nil (s : C.S) : C.act s [] = some s := rfl

lemma act_cons (s : C.S) (p : C.P) (a : List C.P) :
    C.act s (p :: a) = (C.app p s).bind fun t => C.act t a := rfl

@[simp] lemma act_singleton (s : C.S) (p : C.P) : C.act s [p] = C.app p s := by
  simp [act_cons]

lemma act_append (s : C.S) (a b : List C.P) :
    C.act s (a ++ b) = (C.act s a).bind fun t => C.act t b := by
  induction a generalizing s with
  | nil => simp
  | cons p a ih =>
    simp only [List.cons_append, act_cons]
    cases C.app p s with
    | none => rfl
    | some t => exact ih t

lemma act_cons_of {s t : C.S} {p : C.P} (h : C.app p s = some t) (a : List C.P) :
    C.act s (p :: a) = C.act t a := by
  simp [act_cons, h]

lemma act_append_of {s t : C.S} {a : List C.P} (h : C.act s a = some t) (b : List C.P) :
    C.act s (a ++ b) = C.act t b := by
  simp [act_append, h]

end OpSystem

/-- An operation-based CRDT (Section 2): finitely many primitive operations, every state
reachable from `s₀`, and Axiom 1. -/
structure CRDT where
  /-- The underlying states and operations. -/
  toOpSystem : OpSystem.{u, v}
  /-- `P` is finite. -/
  finite : Finite toOpSystem.P
  /-- Every state is reachable from `s₀`. -/
  reachable : toOpSystem.Reachable
  /-- Axiom 1. -/
  comm : toOpSystem.Commutative

/-- An undoable CRDT: a CRDT satisfying Axiom 2. -/
structure UndoableCRDT extends CRDT.{u, v} where
  /-- Axiom 2. -/
  undo : toOpSystem.Undoable

/-- Equivalence of CRDTs (Section 2.2): a bijection `φ` of states and translations
`ψ : P₁ → P₂*`, `ψ' : P₂ → P₁*` of operations such that `φ(s₀) = s₀'`, and
`φ(s) · ψ(p) = φ(s · p)` whenever `s · p ok` (both sides well defined), and symmetrically
`φ⁻¹(s') · ψ'(p') = φ⁻¹(s' · p')` whenever `s' · p' ok`. -/
structure CRDTEquiv (C₁ : OpSystem.{u₁, v₁}) (C₂ : OpSystem.{u₂, v₂}) where
  /-- The bijection of states. -/
  φ : C₁.S ≃ C₂.S
  /-- Implementation of the operations of `C₁` by actions of `C₂`. -/
  ψ : C₁.P → List C₂.P
  /-- Implementation of the operations of `C₂` by actions of `C₁`. -/
  ψ' : C₂.P → List C₁.P
  map_s0 : φ C₁.s0 = C₂.s0
  map_app : ∀ s p t, C₁.app p s = some t → C₂.act (φ s) (ψ p) = some (φ t)
  map_app' : ∀ s' p' t', C₂.app p' s' = some t' → C₁.act (φ.symm s') (ψ' p') = some (φ.symm t')

namespace OpSystem

/-- The tuple construction (Section 2.3) for a family of operation systems: states are
tuples, and an operation of the `i`-th component acts on the `i`-th coordinate. -/
abbrev tuple {ι : Type w} [DecidableEq ι] (C : ι → OpSystem.{u, v}) : OpSystem where
  S := ∀ i, (C i).S
  P := Σ i, (C i).P
  s0 := fun i => (C i).s0
  app := fun x s => ((C x.1).app x.2 (s x.1)).map (Function.update s x.1)

end OpSystem

/-- The primitive operations of a counter. -/
inductive CounterOp
  | inc
  | dec
  deriving DecidableEq

instance : Fintype CounterOp where
  elems := {.inc, .dec}
  complete x := by cases x <;> simp

/-- The effect of a counter operation: `+1` or `-1`. -/
def CounterOp.val {A : Type*} [AddGroupWithOne A] : CounterOp → A
  | .inc => 1
  | .dec => -1

/-- The counter modulo `n` as an operation system (Section 1.1): states `ZMod n`, initial
state `0`, increment and decrement (always applicable). For `n = 0` this is the unbounded
counter, since `ZMod 0 = ℤ`. -/
abbrev OpSystem.modCounter (n : ℕ) : OpSystem.{0, 0} where
  S := ZMod n
  P := CounterOp
  s0 := 0
  app := fun p s => some (s + p.val)

end UndoableCRDTs
