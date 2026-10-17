import Mathlib
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Progress

/-!
# Strong linearizability

Strong linearizability (Golab, Higham and Woelfel, STOC 2011) for implementations in CSLib's
asynchronous shared-memory model (`Cslib.SharedMemory.Impl`).

An implementation is *strongly linearizable* if there is a linearization function `h` (mapping
every finite execution to a linearization of it) that is *prefix-closed*: if `α` is a prefix of
`β` then `h α` is a prefix of `h β`. Executions are label lists; since processes and base objects
are deterministic, a label list determines the whole execution (including the internal steps),
so `h` may depend on the internal steps, as in the original definition.

* `Impl.IsStrongLinFun`, `Impl.StronglyLinearizable` — for deterministic sequential
  specifications (`ObjSpec`, linearizations as in CSLib's `IsLinearization`).
* `NSpec`, `IsNLinearization`, `Impl.NStronglyLinearizable` — for *nondeterministic*
  sequential specifications (e.g. sets whose `take` returns an arbitrary element, relaxed
  queues); linearizations then carry the responses of the linearized operations.
  `Impl.StronglyLinearizable.nStronglyLinearizable`: for a deterministic specification the first
  notion implies the second.
* `Impl.LinSim`, `Impl.stronglyLinearizable_of_linSim` — a *forward simulation* into the atomic
  object (whose states are linearizations, and whose steps append operations) yields strong
  linearizability (Attiya–Enea, DISC 2019). Every step of the implementation may linearize any
  number of operations (linearization points, helping).
* `linResp`, `IsLinearization.append_ret_of_linResp` — the response a linearization assigns to an
  operation, a convenient interface for invariant-based proofs.
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory

-- CSLib candidate (whole file)

variable {A : ObjSpec} {ι : Type} {B : ι → ObjSpec} {P L : Type}

/-! ## Responses assigned by a linearization -/

section LinResp

variable [DecidableEq P]

/-- The response that the sequential specification assigns to the instance `x` in the
sequential history `L` started from state `q` (`none` if `x` does not occur in `L`). -/
def linRespFrom (A : ObjSpec) (x : OpId P) : A.State → List (OpId P × A.Op) → Option A.Resp
  | _, [] => none
  | q, (y, o) :: L => if y = x then some (A.δ q o).2 else linRespFrom A x (A.δ q o).1 L

/-- The response that the linearization `L` assigns to the instance `x`. -/
def linResp (L : List (OpId P × A.Op)) (x : OpId P) : Option A.Resp :=
  linRespFrom A x A.init L

lemma linRespFrom_append_of_mem (x : OpId P) (q : A.State) (L L' : List (OpId P × A.Op))
    (hx : x ∈ L.map Prod.fst) : linRespFrom A x q (L ++ L') = linRespFrom A x q L := by
  induction L generalizing q with
  | nil => simp at hx
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    simp only [List.cons_append, linRespFrom]
    split_ifs with h
    · rfl
    · simp only [List.map_cons, List.mem_cons] at hx
      exact ih _ (hx.resolve_left (Ne.symm h))

lemma linResp_append_of_mem {x : OpId P} {L : List (OpId P × A.Op)} (L' : List (OpId P × A.Op))
    (hx : x ∈ L.map Prod.fst) : linResp (L ++ L') x = linResp L x :=
  linRespFrom_append_of_mem x _ L L' hx

lemma linRespFrom_append_of_not_mem (x : OpId P) (q : A.State) (L L' : List (OpId P × A.Op))
    (hx : x ∉ L.map Prod.fst) :
    linRespFrom A x q (L ++ L') = linRespFrom A x (A.runOps q (L.map Prod.snd)) L' := by
  induction L generalizing q with
  | nil => simp
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    simp only [List.map_cons, List.mem_cons, not_or] at hx
    simp only [List.cons_append, linRespFrom, ite_eq_right_iff.2 (fun h => absurd h (Ne.symm hx.1)), List.map_cons,
      ObjSpec.runOps_cons]
    exact ih _ hx.2

lemma linResp_append_of_not_mem {x : OpId P} {L : List (OpId P × A.Op)}
    (L' : List (OpId P × A.Op)) (hx : x ∉ L.map Prod.fst) :
    linResp (L ++ L') x = linRespFrom A x (linState L) L' :=
  linRespFrom_append_of_not_mem x _ L L' hx

lemma linResp_append_singleton_self {x : OpId P} {L : List (OpId P × A.Op)} (o : A.Op)
    (hx : x ∉ L.map Prod.fst) : linResp (L ++ [(x, o)]) x = some (A.δ (linState L) o).2 := by
  rw [linResp_append_of_not_mem _ hx]; simp [linRespFrom]

lemma linRespFrom_isSome_iff (x : OpId P) (q : A.State) (L : List (OpId P × A.Op)) :
    (linRespFrom A x q L).isSome ↔ x ∈ L.map Prod.fst := by
  induction L generalizing q with
  | nil => simp [linRespFrom]
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    simp only [linRespFrom, List.map_cons, List.mem_cons]
    split_ifs with h
    · simp [h]
    · rw [ih]; constructor
      · exact Or.inr
      · rintro (h' | h')
        · exact absurd h'.symm h
        · exact h'

lemma linResp_isSome_iff {x : OpId P} {L : List (OpId P × A.Op)} :
    (linResp L x).isSome ↔ x ∈ L.map Prod.fst := linRespFrom_isSome_iff x _ L

/-- Splitting a linearization at an instance with a known response. -/
lemma exists_split_of_linRespFrom {x : OpId P} {q : A.State} {L : List (OpId P × A.Op)}
    {r : A.Resp} (h : linRespFrom A x q L = some r) :
    ∃ L₁ L₂ o, L = L₁ ++ (x, o) :: L₂ ∧ (A.δ (A.runOps q (L₁.map Prod.snd)) o).2 = r := by
  induction L generalizing q with
  | nil => simp [linRespFrom] at h
  | cons y L ih =>
    obtain ⟨y, o⟩ := y
    simp only [linRespFrom] at h
    split_ifs at h with hy
    · subst hy; cases h
      exact ⟨[], L, o, by simp, by simp⟩
    · obtain ⟨L₁, L₂, o', hs, hr⟩ := ih h
      exact ⟨(y, o) :: L₁, L₂, o', by simp [hs], by simpa using hr⟩

/-- A response is legal if the linearization assigns it to the returning instance. -/
lemma IsLinearization.append_ret_of_linResp {α : List (Label P A)} {L : List (OpId P × A.Op)}
    (hL : IsLinearization α L) {p : P} {r : A.Resp}
    (hr : linResp L (p, (respsOf α p).length) = some r) :
    IsLinearization (α ++ [.ret p r]) L := by
  obtain ⟨L₁, L₂, o, hs, hr'⟩ := exists_split_of_linRespFrom hr
  exact hL.append_ret L₁ L₂ o hs hr'

/-- The empty linearization of the empty execution. -/
lemma isLinearization_nil : IsLinearization ([] : List (Label P A)) [] :=
  ⟨by simp, by simp, fun a ha => by simp [Completed] at ha, fun a b _ hb => by simp at hb,
    trivial⟩

/-- Linearizing several pending instances at once (in the given order). -/
lemma IsLinearization.push_list {α : List (Label P A)} {L : List (OpId P × A.Op)}
    (hL : IsLinearization α L) (M : List (OpId P × A.Op))
    (hM : ∀ y ∈ M, opOf α y.1 = some y.2 ∧ ¬ Completed α y.1)
    (hnd : (M.map Prod.fst).Nodup) (hdisj : ∀ y ∈ M, y.1 ∉ L.map Prod.fst) :
    IsLinearization α (L ++ M) := by
  induction M using List.reverseRecOn with
  | nil => simpa using hL
  | append_singleton M y ih =>
    have ih' := ih (fun z hz => hM z (by simp [hz]))
      (by rw [List.map_append] at hnd; exact (List.nodup_append.1 hnd).1)
      (fun z hz => hdisj z (by simp [hz]))
    rw [← List.append_assoc]
    obtain ⟨h1, h2⟩ := hM y (by simp)
    refine ih'.push h1 ?_ h2
    rw [List.map_append, List.mem_append, not_or]
    refine ⟨hdisj y (by simp), fun hm => ?_⟩
    rw [List.map_append, List.nodup_append] at hnd
    exact hnd.2.2 _ hm _ (by simp) rfl

end LinResp

/-! ## Strong linearizability (deterministic specifications) -/

namespace Impl

variable [DecidableEq P] [DecidableEq ι] (I : Impl A B P L)

/-- A *strong linearization function* (Golab–Higham–Woelfel): a linearization function that is
prefix-closed on executions. -/
def IsStrongLinFun (h : List (Label P A) → List (OpId P × A.Op)) : Prop :=
  I.IsLinFun h ∧ ∀ α β, I.Valid β → α <+: β → h α <+: h β

/-- The implementation is *strongly linearizable*. -/
def StronglyLinearizable : Prop := ∃ h, I.IsStrongLinFun h

theorem StronglyLinearizable.linearizable {I : Impl A B P L} (h : I.StronglyLinearizable) :
    I.Linearizable := by
  obtain ⟨f, hf, -⟩ := h; exact ⟨f, hf⟩

/-! ### Forward simulations -/

/-- A *forward simulation* of the implementation by the atomic object whose states are
linearizations (Attiya–Enea): `R α C L` relates an execution `α` with final configuration `C`
to a linearization `L`; every step extends the linearization by zero or more operations. -/
structure LinSim (R : List (Label P A) → Config A B P L → List (OpId P × A.Op) → Prop) :
    Prop where
  init : R [] I.initCfg []
  step : ∀ α C L ℓ C', I.run α = some C → R α C L → I.step C ℓ = some C' →
    ∃ L', R (α ++ [ℓ]) C' (L ++ L')
  lin : ∀ α C L, I.run α = some C → R α C L → IsLinearization α L

section Sim

variable (R : List (Label P A) → Config A B P L → List (OpId P × A.Op) → Prop)

/-- One step of the canonical linearization function of a simulation. -/
noncomputable def simExt (α : List (Label P A)) (ℓ : Label P A) (L : List (OpId P × A.Op)) :
    List (OpId P × A.Op) := by
  classical
  exact if h : ∃ L', ∀ C C', I.run α = some C → I.step C ℓ = some C' →
      R (α ++ [ℓ]) C' (L ++ L') then L ++ h.choose else L

/-- The canonical linearization function of a simulation, on reversed executions. -/
noncomputable def simLinRev : List (Label P A) → List (OpId P × A.Op)
  | [] => []
  | ℓ :: rα => I.simExt R rα.reverse ℓ (simLinRev rα)

/-- The canonical linearization function of a simulation. -/
noncomputable def simLin (α : List (Label P A)) : List (OpId P × A.Op) :=
  I.simLinRev R α.reverse

lemma simLin_append_singleton (α : List (Label P A)) (ℓ : Label P A) :
    I.simLin R (α ++ [ℓ]) = I.simExt R α ℓ (I.simLin R α) := by
  simp [simLin, simLinRev]

lemma simLin_prefix_singleton (α : List (Label P A)) (ℓ : Label P A) :
    I.simLin R α <+: I.simLin R (α ++ [ℓ]) := by
  rw [simLin_append_singleton, simExt]
  split_ifs
  · exact List.prefix_append _ _
  · exact List.prefix_refl _

lemma simLin_prefix (α β : List (Label P A)) : I.simLin R α <+: I.simLin R (α ++ β) := by
  induction β using List.reverseRecOn with
  | nil => simp
  | append_singleton β ℓ ih =>
    rw [← List.append_assoc]
    exact ih.trans (I.simLin_prefix_singleton R _ ℓ)

lemma simLin_spec (hR : I.LinSim R) (α : List (Label P A)) (C : Config A B P L)
    (h : I.run α = some C) : R α C (I.simLin R α) := by
  induction α using List.reverseRecOn generalizing C with
  | nil => simp only [run_nil, Option.some.injEq] at h; subst h; exact hR.init
  | append_singleton α ℓ ih =>
    rw [run, runFrom_append] at h
    cases hα : I.runFrom I.initCfg α with
    | none => simp [hα] at h
    | some C₀ =>
      simp only [hα, Option.bind_some, runFrom_singleton] at h
      have hR0 := ih C₀ hα
      obtain ⟨L', hL'⟩ := hR.step α C₀ _ ℓ C hα hR0 h
      have hex : ∃ L', ∀ C₁ C₁', I.run α = some C₁ → I.step C₁ ℓ = some C₁' →
          R (α ++ [ℓ]) C₁' (I.simLin R α ++ L') := by
        refine ⟨L', fun C₁ C₁' h1 h2 => ?_⟩
        have e1 : C₁ = C₀ := by rw [run] at h1; rw [hα] at h1; exact (Option.some.inj h1).symm
        subst e1
        rw [h] at h2; cases h2; exact hL'
      rw [simLin_append_singleton, simExt]
      classical
      rw [dite_eq_left_of_eq_true (eq_true hex)]
      exact hex.choose_spec C₀ C hα h

/-- **Forward simulation ⇒ strong linearizability.** -/
theorem stronglyLinearizable_of_linSim (hR : I.LinSim R) : I.StronglyLinearizable := by
  refine ⟨I.simLin R, fun α ⟨C, hC⟩ => hR.lin α C _ hC (I.simLin_spec R hR α C hC), ?_⟩
  rintro α β - ⟨γ, rfl⟩
  exact I.simLin_prefix R α γ

end Sim

end Impl

/-! ## Nondeterministic sequential specifications -/

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

namespace Impl

variable [DecidableEq ι] (I : Impl A B P L)

/-- Strong linearizability with respect to a nondeterministic specification `S`. -/
def NStronglyLinearizable (S : NSpec A.Op A.Resp) : Prop :=
  ∃ h : List (Label P A) → List (OpId P × A.Op × A.Resp),
    (∀ α, I.Valid α → IsNLinearization S α (h α)) ∧ ∀ α β, I.Valid β → α <+: β → h α <+: h β

/-- Annotate a deterministic sequential history with the responses of the specification. -/
def annotate (A : ObjSpec) : A.State → List (OpId P × A.Op) → List (OpId P × A.Op × A.Resp)
  | _, [] => []
  | q, (x, o) :: L => (x, o, (A.δ q o).2) :: annotate A (A.δ q o).1 L

omit [DecidableEq P] [DecidableEq ι] in
lemma annotate_append (q : A.State) (L L' : List (OpId P × A.Op)) :
    annotate A q (L ++ L') = annotate A q L ++ annotate A (A.runOps q (L.map Prod.snd)) L' := by
  induction L generalizing q with
  | nil => simp [annotate]
  | cons y L ih => obtain ⟨x, o⟩ := y; simp [annotate, ih]

omit [DecidableEq P] [DecidableEq ι] in
lemma annotate_map_fst (q : A.State) (L : List (OpId P × A.Op)) :
    (annotate A q L).map Prod.fst = L.map Prod.fst := by
  induction L generalizing q with
  | nil => rfl
  | cons y L ih => obtain ⟨x, o⟩ := y; simp [annotate, ih]

omit [DecidableEq P] [DecidableEq ι] in
lemma mem_annotate {q : A.State} {L : List (OpId P × A.Op)} {y : OpId P × A.Op × A.Resp}
    (hy : y ∈ annotate A q L) : (y.1, y.2.1) ∈ L := by
  induction L generalizing q with
  | nil => simp [annotate] at hy
  | cons z L ih =>
    obtain ⟨x, o⟩ := z
    simp only [annotate, List.mem_cons] at hy
    rcases hy with rfl | hy
    · simp
    · exact List.mem_cons_of_mem _ (ih hy)

omit [DecidableEq ι] in
lemma isNLinearization_annotate {α : List (Label P A)} {L : List (OpId P × A.Op)}
    (hL : IsLinearization α L) : IsNLinearization A.toNSpec α (annotate A A.init L) := by
  have key : ∀ (q : A.State) (L : List (OpId P × A.Op)), SeqOK α q L →
      (∀ y ∈ annotate A q L, ∀ r, respOf α y.1 = some r → y.2.2 = r) ∧
      A.toNSpec.Legal q ((annotate A q L).map Prod.snd) := by
    intro q L h
    induction L generalizing q with
    | nil => exact ⟨by simp [annotate], trivial⟩
    | cons z L ih =>
      obtain ⟨x, o⟩ := z
      obtain ⟨h1, h2⟩ := h
      obtain ⟨ih1, ih2⟩ := ih _ h2
      refine ⟨?_, ?_⟩
      · intro y hy r hr
        simp only [annotate, List.mem_cons] at hy
        rcases hy with rfl | hy
        · exact h1 r hr
        · exact ih1 y hy r hr
      · simp only [annotate, List.map_cons]
        exact ⟨_, rfl, ih2⟩
  obtain ⟨k1, k2⟩ := key A.init L hL.seq
  refine ⟨?_, ?_, k1, ?_, ?_, k2⟩
  · rw [annotate_map_fst]; exact hL.nodup
  · intro y hy; exact hL.op_eq _ (mem_annotate hy)
  · intro a ha; rw [annotate_map_fst]; exact hL.complete a ha
  · intro a b hab hb; rw [annotate_map_fst] at hb ⊢; exact hL.realtime a b hab hb

/-- For deterministic specifications, strong linearizability implies strong linearizability
with respect to the specification viewed as a nondeterministic one. -/
theorem StronglyLinearizable.nStronglyLinearizable {I : Impl A B P L}
    (h : I.StronglyLinearizable) : I.NStronglyLinearizable A.toNSpec := by
  obtain ⟨f, hf, hpre⟩ := h
  refine ⟨fun α => annotate A A.init (f α), fun α hα => isNLinearization_annotate (hf α hα), ?_⟩
  intro α β hβ hαβ
  obtain ⟨M, hM⟩ := hpre α β hβ hαβ
  show annotate A A.init (f α) <+: annotate A A.init (f β)
  rw [← hM, annotate_append]
  exact List.prefix_append _ _

end Impl

end NLin

end Cslib.SharedMemory
