import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Potential

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/ (IVL / skeleton linearizations)

/-!
# Intermediate value linearizability (Definition 1 of Rinberg–Keidar)

Rinberg, Keidar, *Intermediate Value Linearizability: A Quantitative Correctness Criterion*,
PODC 2020 (brief announcement), full version arXiv:2006.12889, Section 3.

We work in CSLib's asynchronous shared-memory model (`Cslib.SharedMemory`): a history is a list of
labels `List (Label P A)` (invocations `inv p o`, responses `ret p r`, internal steps `tau p`),
operation instances are `OpId P = P × ℕ` (`(p, k)` = the `k`-th operation of `p`), and a
linearization of `α` is a list `L : List (OpId P × A.Op)` (`IsLinearization α L`, the amended
Herlihy–Wing definition of Sela–Herlihy–Petrank).

* `skelSpec A` (`= skelOf A.Op`): the object with the operations of `A`, a single state and the
  single response `()` — the paper's "`?`" response. `skel α` (the paper's `H?`) replaces every
  response of `α` by `()`.
* `IsSkelLin α L`: `L` is a linearization of the skeleton history `skel α` (no constraint on
  responses).
* `QSpec Op Resp`: a deterministic sequential specification (states, initial state, transition
  function) over given operations and responses. It is decoupled from the `ObjSpec` that fixes the
  interface of an implementation, so that one implementation (or a family of implementations
  indexed by coin flips) can be compared with several specifications; `ObjSpec.toQSpec A` is the
  specification of `A` itself.
* `tau S L a` (the paper's `ret(a, τ_S(L))`): the response that the deterministic sequential
  specification `S` gives to the instance `a` in the sequential skeleton `L`.
* `IsIVLFor S α` / `IsIVL A α` (**Definition 1**): there are two skeleton linearizations `L₁`, `L₂`
  such that every completed instance returns a value between the values `τ_S(L₁)` and `τ_S(L₂)`
  assign to it.
* `Impl.IVLFor S` / `Impl.IVL` (**Definition 1**, second part): every execution of the
  implementation is IVL.
* `isIVL_of_isLinearization`: a linearizable history is IVL (remark after Definition 1).

The paper compares only the return values of *queries*; the updates of a quantitative object
return no value. In CSLib every operation has a response, so we compare all completed instances:
for the objects of the paper the updates return a fixed dummy value, both in the implementations
and in the specifications, so the comparison is trivial for them.
-/

open Cslib.SharedMemory

set_option linter.unusedSectionVars false

namespace Podc.IntermediateValueLin

variable {P : Type} [DecidableEq P] {A : ObjSpec}

/-- The skeleton object over the operations `Op`: one state and the single response `()` (the
paper's "`?`"). Every sequential history of it is legal. -/
abbrev skelOf (Op : Type) : ObjSpec where
  State := Unit
  Op := Op
  Resp := Unit
  init := ()
  δ _ _ := ((), ())

/-- The skeleton object of `A`. -/
abbrev skelSpec (A : ObjSpec) : ObjSpec := skelOf A.Op

/-- A label with its response value erased. -/
def _root_.Cslib.SharedMemory.Label.skel : Label P A → Label P (skelSpec A)
  | .inv p o => .inv p o
  | .ret p _ => .ret p ()
  | .tau p => .tau p

/-- The skeleton history `H?` of `α`: all response values replaced by `?`. -/
def skel (α : List (Label P A)) : List (Label P (skelSpec A)) := α.map Label.skel

/-- `L` is a linearization of the skeleton history `α?`. -/
abbrev IsSkelLin (α : List (Label P A)) (L : List (OpId P × A.Op)) : Prop :=
  IsLinearization (skel α) L

/-- A deterministic sequential specification over operations `Op` and responses `Resp`: the
paper's sequential specification `H` of a deterministic (quantitative) object. -/
structure QSpec (Op Resp : Type) where
  /-- States. -/
  State : Type
  /-- Initial state. -/
  init : State
  /-- Transition function: new state and response. -/
  δ : State → Op → State × Resp

/-- The `ObjSpec` with the states and transitions of `S`. -/
abbrev QSpec.obj {Op Resp : Type} (S : QSpec Op Resp) : ObjSpec := ⟨S.State, Op, Resp, S.init, S.δ⟩

/-- The sequential specification of the object `A`. -/
abbrev _root_.Cslib.SharedMemory.ObjSpec.toQSpec (A : ObjSpec) : QSpec A.Op A.Resp :=
  ⟨A.State, A.init, A.δ⟩

/-- `tau S L a` is the paper's `ret(a, τ_S(L))`: the response of the instance `a` in the unique
legal sequential history of the deterministic object `S` with skeleton `L`. -/
def tau {Op Resp : Type} (S : QSpec Op Resp) (L : List (OpId P × Op)) (a : OpId P) :
    Option Resp :=
  S.obj.respIn S.init L a

/-- **Definition 1** (intermediate value linearizability). The history `α` is IVL with respect to
the deterministic sequential specification `S` if there are two linearizations `L₁`, `L₂` of the
skeleton history `α?` such that for every instance `a` that returns `r` in `α`,
`ret(a, τ_S(L₁)) ≤ r ≤ ret(a, τ_S(L₂))`. -/
def IsIVLFor [LE A.Resp] (S : QSpec A.Op A.Resp) (α : List (Label P A)) : Prop :=
  ∃ L₁ L₂, IsSkelLin α L₁ ∧ IsSkelLin α L₂ ∧
    ∀ a r, respOf α a = some r → ∃ r₁ r₂, tau S L₁ a = some r₁ ∧ tau S L₂ a = some r₂ ∧
      r₁ ≤ r ∧ r ≤ r₂

/-- **Definition 1** for the specification of the interface object `A` itself. -/
abbrev IsIVL (A : ObjSpec) [LE A.Resp] (α : List (Label P A)) : Prop := IsIVLFor A.toQSpec α

/-- **Definition 1**, second part: an implementation is an *IVL implementation* of `S` if every
history of one of its (finite) executions is IVL. (Executions of CSLib implementations are
well-formed by construction, `Impl.Valid.wellFormed`.) -/
def _root_.Cslib.SharedMemory.Impl.IVLFor {ι : Type} [DecidableEq ι] {B : ι → ObjSpec}
    {L : Type} [LE A.Resp] (I : Impl A B P L) (S : QSpec A.Op A.Resp) : Prop :=
  ∀ α, I.Valid α → IsIVLFor S α

/-- An IVL implementation of its interface object `A`. -/
abbrev _root_.Cslib.SharedMemory.Impl.IVL {ι : Type} [DecidableEq ι] {B : ι → ObjSpec} {L : Type}
    [LE A.Resp] (I : Impl A B P L) : Prop :=
  I.IVLFor A.toQSpec

/-! ### The skeleton history -/

@[simp] lemma skel_nil : skel ([] : List (Label P A)) = [] := rfl

@[simp] lemma skel_append (α β : List (Label P A)) : skel (α ++ β) = skel α ++ skel β := by
  simp [skel]

@[simp] lemma skel_cons (ℓ : Label P A) (α : List (Label P A)) :
    skel (ℓ :: α) = ℓ.skel :: skel α := rfl

@[simp] lemma skel_singleton (ℓ : Label P A) : skel [ℓ] = [ℓ.skel] := rfl

@[simp] lemma _root_.Cslib.SharedMemory.Label.skel_inv (p : P) (o : A.Op) : (Label.inv p o).skel = .inv p o := rfl
@[simp] lemma _root_.Cslib.SharedMemory.Label.skel_ret (p : P) (r : A.Resp) : (Label.ret p r).skel = .ret p () := rfl
@[simp] lemma _root_.Cslib.SharedMemory.Label.skel_tau (p : P) : (Label.tau p : Label P A).skel = .tau p := rfl

lemma _root_.Cslib.SharedMemory.Label.invOf_skel (p : P) (ℓ : Label P A) : ℓ.skel.invOf p = ℓ.invOf p := by
  cases ℓ <;> rfl

lemma _root_.Cslib.SharedMemory.Label.retOf_skel (p : P) (ℓ : Label P A) :
    ℓ.skel.retOf p = (ℓ.retOf p).map (fun _ => ()) := by
  cases ℓ with
  | inv q o => rfl
  | ret q r => by_cases h : q = p <;> simp [Label.skel, h]
  | tau q => rfl

@[simp] lemma opsOf_skel (α : List (Label P A)) (p : P) : opsOf (skel α) p = opsOf α p := by
  induction α with
  | nil => rfl
  | cons ℓ α ih => simp [ih, Label.invOf_skel]

@[simp] lemma respsOf_skel (α : List (Label P A)) (p : P) :
    respsOf (skel α) p = (respsOf α p).map (fun _ => ()) := by
  induction α with
  | nil => rfl
  | cons ℓ α ih =>
    simp only [skel_cons, respsOf_cons, ih, Label.retOf_skel, List.map_append]
    cases ℓ.retOf p <;> rfl

@[simp] lemma opOf_skel (α : List (Label P A)) (x : OpId P) : opOf (skel α) x = opOf α x := by
  simp [opOf]

@[simp] lemma invoked_skel {α : List (Label P A)} {x : OpId P} :
    Invoked (skel α) x ↔ Invoked α x := by
  simp [Invoked]

@[simp] lemma completed_skel {α : List (Label P A)} {x : OpId P} :
    Completed (skel α) x ↔ Completed α x := by
  simp [Completed]

lemma respOf_skel (α : List (Label P A)) (x : OpId P) :
    respOf (skel α) x = (respOf α x).map (fun _ => ()) := by
  simp only [respOf, respsOf_skel, List.getElem?_map]

@[simp] lemma precedes_skel {α : List (Label P A)} {a b : OpId P} :
    Precedes (skel α) a b ↔ Precedes α a b := by
  constructor
  · rintro ⟨β', γ', h, h1, h2⟩
    obtain ⟨β, γ, rfl, rfl, rfl⟩ := List.map_eq_append_iff.1 h
    exact ⟨β, γ, rfl, completed_skel.1 h1, fun h => h2 (invoked_skel.2 h)⟩
  · rintro ⟨β, γ, rfl, h1, h2⟩
    exact ⟨skel β, skel γ, skel_append β γ, completed_skel.2 h1,
      fun h => h2 (invoked_skel.1 h)⟩

/-- Every sequential history of the skeleton object is legal. -/
lemma seqOK_skel (β : List (Label P (skelSpec A))) (q : Unit) (L : List (OpId P × A.Op)) :
    SeqOK β q L := by
  induction L generalizing q with
  | nil => trivial
  | cons y L ih => exact ⟨fun _ _ => rfl, ih _⟩

/-- A skeleton linearization is the same as a list satisfying all conditions of a linearization of
`α` except legality. -/
lemma isSkelLin_iff {α : List (Label P A)} {L : List (OpId P × A.Op)} :
    IsSkelLin α L ↔ (L.map Prod.fst).Nodup ∧ (∀ y ∈ L, opOf α y.1 = some y.2) ∧
      (∀ a, Completed α a → a ∈ L.map Prod.fst) ∧
      (∀ a b, Precedes α a b → b ∈ L.map Prod.fst → [a, b].Sublist (L.map Prod.fst)) := by
  constructor
  · intro h
    exact ⟨h.nodup, fun y hy => by simpa using h.op_eq y hy,
      fun a ha => h.complete a (completed_skel.2 ha),
      fun a b hab hb => h.realtime a b (precedes_skel.2 hab) hb⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨h1, fun y hy => by simpa using h2 y hy, fun a ha => h3 a (completed_skel.1 ha),
      fun a b hab hb => h4 a b (precedes_skel.1 hab) hb, seqOK_skel _ _ _⟩

/-- A linearization of `α` is a linearization of its skeleton. -/
lemma _root_.Cslib.SharedMemory.IsLinearization.isSkelLin {α : List (Label P A)} {L : List (OpId P × A.Op)}
    (h : IsLinearization α L) : IsSkelLin α L :=
  isSkelLin_iff.2 ⟨h.nodup, h.op_eq, h.complete, h.realtime⟩

/-- Remark after Definition 1: a linearizable history is IVL (take `L₁ = L₂` = a linearization).
-/
theorem isIVL_of_isLinearization [Preorder A.Resp] {α : List (Label P A)}
    {L : List (OpId P × A.Op)} (h : IsLinearization α L) : IsIVL A α :=
  ⟨L, L, h.isSkelLin, h.isSkelLin, fun _ r hr =>
    ⟨r, r, h.respIn_eq hr, h.respIn_eq hr, le_rfl, le_rfl⟩⟩

/-- A linearizable implementation is an IVL implementation. -/
theorem _root_.Cslib.SharedMemory.Impl.IVL.of_linearizable {ι : Type} [DecidableEq ι]
    {B : ι → ObjSpec} {L : Type} [Preorder A.Resp] {I : Impl A B P L} (h : I.Linearizable) :
    I.IVL := by
  obtain ⟨f, hf⟩ := h
  intro α hα
  exact isIVL_of_isLinearization (hf α hα)

/-- Linearizability of a history `α` with respect to a sequential specification `S` over the same
operations and responses (needed when the interface object of an implementation is not the
specification itself): a skeleton linearization in which `τ_S` assigns to every completed
instance its actual response. -/
def IsLinFor (S : QSpec A.Op A.Resp) (α : List (Label P A)) : Prop :=
  ∃ L, IsSkelLin α L ∧ ∀ a r, respOf α a = some r → tau S L a = some r

/-- For the specification of `A` itself, `IsLinFor` is CSLib's linearizability. -/
theorem isLinFor_toQSpec_iff {α : List (Label P A)} :
    IsLinFor A.toQSpec α ↔ ∃ L, IsLinearization α L := by
  constructor
  · rintro ⟨L, hL, hr⟩
    refine ⟨L, hL.nodup, fun y hy => by simpa using hL.op_eq y hy,
      fun a ha => hL.complete a (completed_skel.2 ha),
      fun a b hab hb => hL.realtime a b (precedes_skel.2 hab) hb, ?_⟩
    exact seqOK_of_respIn hL.nodup fun x r _ hxr => hr x r hxr
  · rintro ⟨L, hL⟩
    exact ⟨L, hL.isSkelLin, fun a r hr => hL.respIn_eq hr⟩

/-- A history that is linearizable with respect to `S` is IVL with respect to `S`. -/
theorem IsLinFor.isIVLFor [Preorder A.Resp] {S : QSpec A.Op A.Resp} {α : List (Label P A)}
    (h : IsLinFor S α) : IsIVLFor S α := by
  obtain ⟨L, hL, hr⟩ := h
  exact ⟨L, L, hL, hL, fun a r har => ⟨r, r, hr a r har, hr a r har, le_rfl, le_rfl⟩⟩

/-- In a skeleton linearization, every completed instance gets a response from `τ_A`. -/
lemma IsSkelLin.tau_isSome {α : List (Label P A)} {L : List (OpId P × A.Op)}
    (h : IsSkelLin α L) (S : QSpec A.Op A.Resp) {a : OpId P} (ha : Completed α a) :
    (tau S L a).isSome :=
  ObjSpec.respIn_isSome_iff.2 (h.complete a (completed_skel.2 ha))

end Podc.IntermediateValueLin
