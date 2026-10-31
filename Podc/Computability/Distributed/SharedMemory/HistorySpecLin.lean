import Cslib.Computability.Distributed.SharedMemory.StrongLin

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/HistorySpecLin.lean

/-!
# Linearizability with respect to a set of sequential histories

CSLib's linearizability notions fix the sequential specification as a (deterministic or
nondeterministic) state machine (`ObjSpec`, `NSpec`). Some correctness conditions are instead
given as an arbitrary *set of sequential histories*, e.g. relaxed specifications defined by a
relation between histories ("`H'` is allowed iff some legal `H` is a relaxation of `H'`").

* `IsHLinearization Spec α L`: `L` (a list of operation instances with their operations and
  responses) is a linearization of the execution `α` whose sequential history lies in `Spec`.
  The fields are those of `IsNLinearization`, with legality replaced by `Spec L`
  (`isHLinearization_legal_iff`).
* `Impl.HStronglyLinearizable Spec`: strong linearizability (a prefix-preserving linearization
  function, Golab–Higham–Woelfel) with respect to `Spec`.
* `Impl.hStronglyLinearizable_of_prefix`: a function from executions to sequential histories
  that only grows along executions, lists distinct invoked instances with their operations and
  actual responses, contains every completed instance and lies in `Spec`, is a strong
  linearization function (real-time order is automatic).
-/

namespace Cslib.SharedMemory

variable {P : Type} {A : ObjSpec} [DecidableEq P]

/-- `L` is a linearization of (the history of) `α` whose sequential history (with responses)
belongs to the set `Spec`. Pending operations may be included with any response. -/
structure IsHLinearization (Spec : List (OpId P × A.Op × A.Resp) → Prop)
    (α : List (Label P A)) (L : List (OpId P × A.Op × A.Resp)) : Prop where
  nodup : (L.map Prod.fst).Nodup
  op_eq : ∀ y ∈ L, opOf α y.1 = some y.2.1
  resp_eq : ∀ y ∈ L, ∀ r, respOf α y.1 = some r → y.2.2 = r
  complete : ∀ a, Completed α a → a ∈ L.map Prod.fst
  realtime : ∀ a b, Precedes α a b → b ∈ L.map Prod.fst → [a, b].Sublist (L.map Prod.fst)
  mem : Spec L

/-- For a nondeterministic specification `S`, linearizability with respect to the set of legal
histories of `S` is `IsNLinearization S`. -/
theorem isHLinearization_legal_iff (S : NSpec A.Op A.Resp) (α : List (Label P A))
    (L : List (OpId P × A.Op × A.Resp)) :
    IsHLinearization (fun L => S.Legal S.init (L.map Prod.snd)) α L ↔ IsNLinearization S α L :=
  ⟨fun h => ⟨h.nodup, h.op_eq, h.resp_eq, h.complete, h.realtime, h.mem⟩,
    fun h => ⟨h.nodup, h.op_eq, h.resp_eq, h.complete, h.realtime, h.legal⟩⟩

lemma IsHLinearization.mono {Spec Spec' : List (OpId P × A.Op × A.Resp) → Prop}
    {α : List (Label P A)} {L : List (OpId P × A.Op × A.Resp)} (h : IsHLinearization Spec α L)
    (hS : Spec L → Spec' L) : IsHLinearization Spec' α L :=
  ⟨h.nodup, h.op_eq, h.resp_eq, h.complete, h.realtime, hS h.mem⟩

namespace Impl

variable {ι : Type} {B : ι → ObjSpec} {L : Type} [DecidableEq ι] (I : Impl A B P L)

/-- Strong linearizability with respect to a set `Spec` of sequential histories: there is a
prefix-preserving function mapping every finite execution to a linearization in `Spec`. -/
def HStronglyLinearizable (Spec : List (OpId P × A.Op × A.Resp) → Prop) : Prop :=
  ∃ h : List (Label P A) → List (OpId P × A.Op × A.Resp),
    (∀ α, I.Valid α → IsHLinearization Spec α (h α)) ∧ ∀ α β, I.Valid β → α <+: β → h α <+: h β

/-- For the legal histories of a nondeterministic specification this is
`NStronglyLinearizable`. -/
theorem hStronglyLinearizable_legal_iff (S : NSpec A.Op A.Resp) :
    I.HStronglyLinearizable (fun L => S.Legal S.init (L.map Prod.snd)) ↔
      I.NStronglyLinearizable S := by
  simp only [HStronglyLinearizable, NStronglyLinearizable, isHLinearization_legal_iff]

variable {I}

lemma HStronglyLinearizable.mono {Spec Spec' : List (OpId P × A.Op × A.Resp) → Prop}
    (h : I.HStronglyLinearizable Spec) (hS : ∀ L, Spec L → Spec' L) :
    I.HStronglyLinearizable Spec' := by
  obtain ⟨f, hf, hp⟩ := h
  exact ⟨f, fun α hα => (hf α hα).mono (hS _), hp⟩

/-- **Growing linearization functions.** If `h` is prefix-monotone on valid executions and, on
every valid execution `α`, `h α` lists distinct invoked instances with their operations and
actual responses, contains every completed instance, and lies in `Spec`, then `h` witnesses
strong linearizability with respect to `Spec` (real-time order is automatic). -/
theorem hStronglyLinearizable_of_prefix {Spec : List (OpId P × A.Op × A.Resp) → Prop}
    (h : List (Label P A) → List (OpId P × A.Op × A.Resp))
    (hmono : ∀ α β, I.Valid β → α <+: β → h α <+: h β)
    (hnodup : ∀ α, I.Valid α → ((h α).map Prod.fst).Nodup)
    (hop : ∀ α, I.Valid α → ∀ y ∈ h α, opOf α y.1 = some y.2.1)
    (hresp : ∀ α, I.Valid α → ∀ y ∈ h α, ∀ r, respOf α y.1 = some r → y.2.2 = r)
    (hcomp : ∀ α, I.Valid α → ∀ a, Completed α a → a ∈ (h α).map Prod.fst)
    (hspec : ∀ α, I.Valid α → Spec (h α)) : I.HStronglyLinearizable Spec := by
  refine ⟨h, fun α hα => ⟨hnodup α hα, hop α hα, hresp α hα, hcomp α hα, ?_, hspec α hα⟩,
    hmono⟩
  rintro a b ⟨β, γ, rfl, ha, hb⟩ hbL
  have hβ : I.Valid β := hα.of_append
  obtain ⟨M, hM⟩ := hmono β (β ++ γ) hα (List.prefix_append β γ)
  rw [← hM] at hbL ⊢
  have haβ := hcomp β hβ a ha
  have hbβ : b ∉ (h β).map Prod.fst := fun hm => by
    obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hm
    exact hb (Invoked.of_opOf_eq_some (hop β hβ y hy))
  simp only [List.map_append, List.mem_append] at hbL ⊢
  rcases hbL with hbL | hbL
  · exact absurd hbL hbβ
  · exact (List.Sublist.append (List.singleton_sublist.2 haβ) (List.singleton_sublist.2 hbL) :
      List.Sublist ([a] ++ [b]) _)

end Impl

end Cslib.SharedMemory
