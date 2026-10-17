import Cslib.Computability.Distributed.SharedMemory.History

-- CSLib candidate: Cslib/Computability/Distributed/SharedMemory/Spec.lean (NSpec) and
-- Cslib/Computability/Distributed/SharedMemory/History.lean (IsNLinearization)

/-!
# Nondeterministic sequential specifications

* `NSpec Op Resp` — a nondeterministic sequential specification (e.g. sets whose `take` returns an
  arbitrary element, relaxed queues): a transition *relation* `Step q o r q'`;
  `NSpec.Legal q l` — legality of a sequence of (operation, response) pairs from state `q`;
* `ObjSpec.toNSpec` — a deterministic specification as a nondeterministic one;
* `IsNLinearization S α L` — linearizations with respect to a nondeterministic specification;
  they carry the responses of the linearized operations (pending ones get the responses chosen
  by the linearization).

For deterministic specifications the two notions of linearization agree:
`IsLinearization.isNLinearization_annotate` (annotate a linearization with the responses of the
specification) and `IsNLinearization.isLinearization_map` (forget the responses);
`exists_isLinearization_iff`.
-/

namespace Cslib.SharedMemory

/-- A *nondeterministic* sequential specification over operations `Op` and responses `Resp`:
`Step q o r q'` says that applying `o` in state `q` may return `r` and move to `q'`. -/
structure NSpec (Op Resp : Type) where
  /-- States. -/
  State : Type
  /-- The initial state. -/
  init : State
  /-- The transition relation. -/
  Step : State → Op → Resp → State → Prop

namespace NSpec

variable {Op Resp : Type} (S : NSpec Op Resp)

/-- A sequence of operations with responses is legal from state `q`. -/
def Legal : S.State → List (Op × Resp) → Prop
  | _, [] => True
  | q, (o, r) :: l => ∃ q', S.Step q o r q' ∧ Legal q' l

@[simp] lemma legal_nil (q : S.State) : S.Legal q [] := trivial

@[simp] lemma legal_cons (q : S.State) (o : Op) (r : Resp) (l : List (Op × Resp)) :
    S.Legal q ((o, r) :: l) ↔ ∃ q', S.Step q o r q' ∧ S.Legal q' l := Iff.rfl

end NSpec

/-- The deterministic specification `A` as a nondeterministic one. -/
def ObjSpec.toNSpec (A : ObjSpec) : NSpec A.Op A.Resp where
  State := A.State
  init := A.init
  Step q o r q' := A.δ q o = (q', r)

@[simp] lemma ObjSpec.toNSpec_step (A : ObjSpec) (q : A.State) (o : A.Op) (r : A.Resp)
    (q' : A.State) : A.toNSpec.Step q o r q' ↔ A.δ q o = (q', r) := Iff.rfl

variable {P : Type} {A : ObjSpec}

section NLin

variable [DecidableEq P]

/-- `L` (instances with their operations and responses) is a linearization of `α` with respect
to the nondeterministic specification `S`: no duplicates, the operations are the invoked ones,
completed instances carry their actual responses and are all present, real-time order is
respected, and the sequence of operations/responses is legal for `S`. Pending instances in `L`
carry the responses chosen by the linearization. -/
structure IsNLinearization (S : NSpec A.Op A.Resp) (α : List (Label P A))
    (L : List (OpId P × A.Op × A.Resp)) : Prop where
  nodup : (L.map Prod.fst).Nodup
  op_eq : ∀ y ∈ L, opOf α y.1 = some y.2.1
  resp_eq : ∀ y ∈ L, ∀ r, respOf α y.1 = some r → y.2.2 = r
  complete : ∀ a, Completed α a → a ∈ L.map Prod.fst
  realtime : ∀ a b, Precedes α a b → b ∈ L.map Prod.fst → [a, b].Sublist (L.map Prod.fst)
  legal : S.Legal S.init (L.map Prod.snd)

end NLin

/-! ## Deterministic specifications -/

namespace ObjSpec

/-- Annotate a deterministic sequential history (run from `q`) with the responses of the
specification. -/
def annotate (A : ObjSpec) : A.State → List (OpId P × A.Op) → List (OpId P × A.Op × A.Resp)
  | _, [] => []
  | q, (x, o) :: L => (x, o, (A.δ q o).2) :: annotate A (A.δ q o).1 L

lemma annotate_append (q : A.State) (L L' : List (OpId P × A.Op)) :
    A.annotate q (L ++ L') = A.annotate q L ++ A.annotate (A.runOps q (L.map Prod.snd)) L' := by
  induction L generalizing q with
  | nil => simp [annotate]
  | cons y L ih => obtain ⟨x, o⟩ := y; simp [annotate, ih]

@[simp] lemma annotate_map_fst (q : A.State) (L : List (OpId P × A.Op)) :
    (A.annotate q L).map Prod.fst = L.map Prod.fst := by
  induction L generalizing q with
  | nil => rfl
  | cons y L ih => obtain ⟨x, o⟩ := y; simp [annotate, ih]

lemma mem_annotate {q : A.State} {L : List (OpId P × A.Op)} {y : OpId P × A.Op × A.Resp}
    (hy : y ∈ A.annotate q L) : (y.1, y.2.1) ∈ L := by
  induction L generalizing q with
  | nil => simp [annotate] at hy
  | cons z L ih =>
    obtain ⟨x, o⟩ := z
    simp only [annotate, List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp
    · exact List.mem_cons_of_mem _ (ih hy)

end ObjSpec

variable [DecidableEq P]

/-- Annotating a linearization with the responses of the specification gives a linearization
with respect to the specification viewed as a nondeterministic one. -/
lemma IsLinearization.isNLinearization_annotate {α : List (Label P A)}
    {L : List (OpId P × A.Op)} (hL : IsLinearization α L) :
    IsNLinearization A.toNSpec α (A.annotate A.init L) := by
  have key : ∀ (q : A.State) (L : List (OpId P × A.Op)), SeqOK α q L →
      (∀ y ∈ A.annotate q L, ∀ r, respOf α y.1 = some r → y.2.2 = r) ∧
      A.toNSpec.Legal q ((A.annotate q L).map Prod.snd) := by
    intro q L h
    induction L generalizing q with
    | nil => exact ⟨by simp [ObjSpec.annotate], trivial⟩
    | cons z L ih =>
      obtain ⟨x, o⟩ := z
      obtain ⟨h1, h2⟩ := h
      obtain ⟨ih1, ih2⟩ := ih _ h2
      refine ⟨?_, ?_⟩
      · intro y hy r hr
        simp only [ObjSpec.annotate, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact h1 r hr
        · exact ih1 y hy r hr
      · simp only [ObjSpec.annotate, List.map_cons]
        exact ⟨_, rfl, ih2⟩
  obtain ⟨k1, k2⟩ := key A.init L hL.seq
  refine ⟨?_, ?_, k1, ?_, ?_, k2⟩
  · rw [ObjSpec.annotate_map_fst]; exact hL.nodup
  · intro y hy; exact hL.op_eq _ (ObjSpec.mem_annotate hy)
  · intro a ha; rw [ObjSpec.annotate_map_fst]; exact hL.complete a ha
  · intro a b hab hb; rw [ObjSpec.annotate_map_fst] at hb ⊢; exact hL.realtime a b hab hb

/-- Forgetting the responses of a linearization with respect to `A.toNSpec` gives a
linearization. -/
lemma IsNLinearization.isLinearization_map {α : List (Label P A)}
    {L : List (OpId P × A.Op × A.Resp)} (hL : IsNLinearization A.toNSpec α L) :
    IsLinearization α (L.map fun y => (y.1, y.2.1)) := by
  have hfst : (L.map fun y => (y.1, y.2.1)).map Prod.fst = L.map Prod.fst := by simp
  have key : ∀ (q : A.State) (L : List (OpId P × A.Op × A.Resp)),
      (∀ y ∈ L, ∀ r, respOf α y.1 = some r → y.2.2 = r) →
      A.toNSpec.Legal q (L.map Prod.snd) → SeqOK α q (L.map fun y => (y.1, y.2.1)) := by
    intro q L h1 h2
    induction L generalizing q with
    | nil => trivial
    | cons y L ih =>
      obtain ⟨x, o, r⟩ := y
      obtain ⟨q', hq', h2⟩ := h2
      change A.δ q o = (q', r) at hq'
      refine ⟨fun r' hr' => ?_, ?_⟩
      · rw [hq']; exact h1 _ (by simp) r' hr'
      · rw [hq']; exact ih q' (fun y hy => h1 y (by simp [hy])) h2
  refine ⟨?_, ?_, ?_, ?_, key _ L hL.resp_eq hL.legal⟩
  · rw [hfst]; exact hL.nodup
  · intro y hy
    obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hy
    exact hL.op_eq z hz
  · intro a ha; rw [hfst]; exact hL.complete a ha
  · intro a b hab hb; rw [hfst] at hb ⊢; exact hL.realtime a b hab hb

/-- For a deterministic specification, an execution has a linearization iff it has one with
respect to the specification viewed as a nondeterministic one. -/
theorem exists_isLinearization_iff {α : List (Label P A)} :
    (∃ L, IsLinearization α L) ↔ ∃ L, IsNLinearization A.toNSpec α L :=
  ⟨fun ⟨_, hL⟩ => ⟨_, hL.isNLinearization_annotate⟩,
    fun ⟨_, hL⟩ => ⟨_, hL.isLinearization_map⟩⟩

end Cslib.SharedMemory
