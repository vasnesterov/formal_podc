import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Locality
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Bridge
import Papers.PODC2020.IntermediateValueLin.Defs

/-!
# Locality of intermediate value linearizability (Section 3.2 and Appendix A of Rinberg–Keidar)

Rinberg, Keidar, *Intermediate Value Linearizability: A Quantitative Correctness Criterion*,
PODC 2020, full version arXiv:2006.12889.

Claim (Section 3.2, proof in Appendix A): *a history `H` of a well-formed execution over a set of
objects `X` is IVL iff for each object `x ∈ X`, `H|x` is IVL.*

Locality is a statement about **multi-object** histories, so we work in CSLib's multi-object
Herlihy–Wing history framework (`Cslib.SharedMemory.HerlihyWing`): a history is a list of events
`inv p x o` / `res p x r`, operation instances are `OpId = (p, x, k)` (the `k`-th operation of `p`
on `x`), and a linearization is a list of operation records `M` with `IsLinA spec H M` (the amended
Herlihy–Wing definition of Sela–Herlihy–Petrank: real-time order is respected towards every
linearized operation, including linearized pending ones).

* `eraseH H` is the skeleton history `H?` (every response value replaced by `? = ()`).
* A skeleton linearization of `H` is an `M` with `IsLinA (fun _ => Set.univ) (eraseH H) M`: every
  sequential skeleton history is legal.
* `QSpec Op Res` (from `Defs.lean`): a deterministic sequential object (state, initial state,
  transition function); a multi-object specification is a family `S : X → QSpec Op Res`.
* `tauHW S M a` is the paper's `ret(a, τ_H(M))`: the response of `a` when the operations of object
  `a.x` in `M` are run through `S a.x` from its initial state (objects are independent, so this
  is exactly the unique legal history of the multi-object specification with skeleton `M`).
* `IVL S H` (Definition 1, for multi-object histories).
* `ivl_locality`: the locality theorem.
* `isIVLFor_iff_ivl_toHist`, `isIVL_iff_ivl_toHist`: for a single object, `IVL` agrees with the
  execution-level definition `IsIVLFor` / `IsIVL` of `Defs.lean` (via CSLib's `toHist`).

## Comparison with the paper

* The paper's Definition 1 is stated for "a history `H` of an object"; locality needs it for
  multi-object histories, with the multi-object specification of Section 2.1 (`H|x ∈ H_x` for every
  `x`), whose `τ_H` acts on each object independently. `IVL` is that reading.
* The paper compares only queries; updates return no value. Here every operation has a response
  and we compare all completed operations (for quantitative objects updates return a fixed dummy
  value both in histories and in specifications, so the comparison is trivial for them).
* Definition of linearization (Section 2.1): "`H'` preserves the partial order `≺_H`", where
  `op₁ ≺_H op₂` iff `rsp(op₁)` precedes `inv(op₂)`. Since `≺_H` is defined via the invocation of
  `op₂` only, it relates a completed `op₁` to a pending `op₂` as well; we read it as the amended
  definition (`IsLinA`). Under the original Herlihy–Wing reading (`IsLinO`, `≺_H` only between
  completed operations) linearizability is not local (Sela–Herlihy–Petrank), and the same
  counterexample shape would apply to skeleton linearizations, so the reading matters.
* Appendix A, "if" direction: the paper takes the union of the per-object orders `≺_{H_1^x}` and the
  real-time order of `H` and asserts that "this partial order is well defined" because the
  per-object orders respect real time and are disjoint. This is the non-trivial part of
  Herlihy–Wing locality: the union of these relations is not transitive and its transitive closure
  being acyclic needs an argument (cycles may alternate between objects and real-time edges). The
  formal proof uses CSLib's `mergedM` (operations ordered by explicit linearization points), which
  is a proof of exactly this step. Also "Let ... linearization `H_2` of `H 2`" is a typo for `H?`.
* Appendix A, "only if" ("immediate"): the restriction of a skeleton linearization to `x` is a
  skeleton linearization of `H|x` (`IsLinA.restrictX`), and `τ` of an operation of `x` only depends
  on the operations of `x`.
* We assume `H` well-formed (as the paper: histories of well-formed executions).
-/

set_option linter.unusedSectionVars false

open Cslib.SharedMemory.HerlihyWing

namespace Podc.IntermediateValueLin.HW

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-! ### Skeleton histories -/

/-- An event with its response value erased (replaced by `? = ()`). -/
def eraseEv : Event P X Op Res → Event P X Op Unit
  | .inv p x o => .inv p x o
  | .res p x _ => .res p x ()

/-- The skeleton history `H?`: all response values replaced by `?`. -/
def eraseH (H : History P X Op Res) : History P X Op Unit := H.map eraseEv

/-- An operation record with its response erased. -/
def eraseRec (e : OpRec P X Op Res) : OpRec P X Op Unit := ⟨e.p, e.x, e.o, ()⟩

@[simp] lemma eraseEv_obj (e : Event P X Op Res) : (eraseEv e).obj = e.obj := by
  cases e <;> rfl

@[simp] lemma eraseEv_proc (e : Event P X Op Res) : (eraseEv e).proc = e.proc := by
  cases e <;> rfl

lemma eraseEv_invOf (p : P) (x : X) (e : Event P X Op Res) :
    (eraseEv e).invOf p x = e.invOf p x := by
  cases e <;> rfl

lemma eraseEv_resOf (p : P) (x : X) (e : Event P X Op Res) :
    (eraseEv e).resOf p x = (e.resOf p x).map (fun _ => ()) := by
  cases e with
  | inv q y o => rfl
  | res q y r => by_cases h : q = p ∧ y = x <;> simp [eraseEv, h]

@[simp] lemma eraseH_nil : eraseH ([] : History P X Op Res) = [] := rfl

@[simp] lemma eraseH_append (H H' : History P X Op Res) :
    eraseH (H ++ H') = eraseH H ++ eraseH H' := List.map_append

lemma restrictX_eraseH (H : History P X Op Res) (x : X) :
    restrictX (eraseH H) x = eraseH (restrictX H x) := by
  unfold restrictX eraseH
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  simp

lemma restrictP_eraseH (H : History P X Op Res) (p : P) :
    restrictP (eraseH H) p = eraseH (restrictP H p) := by
  unfold restrictP eraseH
  rw [List.filter_map]
  congr 1
  apply List.filter_congr
  intro e _
  simp

lemma eraseH_seqHist (M : List (OpRec P X Op Res)) :
    eraseH (seqHist M) = seqHist (M.map eraseRec) := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    rw [List.map_cons, seqHist_cons, seqHist_cons, ← ih]
    rfl

lemma isSeq_eraseH {s : History P X Op Res} (h : IsSeq s) : IsSeq (eraseH s) := by
  obtain ⟨M, h | ⟨p, x, o, h⟩⟩ := h
  · exact ⟨M.map eraseRec, Or.inl (by rw [h, eraseH_seqHist])⟩
  · exact ⟨M.map eraseRec, Or.inr ⟨p, x, o, by rw [h, eraseH_append, eraseH_seqHist]; rfl⟩⟩

/-- The skeleton of a well-formed history is well-formed. -/
lemma wellFormed_eraseH {H : History P X Op Res} (h : WellFormed H) : WellFormed (eraseH H) :=
  fun p => by rw [restrictP_eraseH]; exact isSeq_eraseH (h p)

@[simp] lemma opsOf_eraseH (H : History P X Op Res) (p : P) (x : X) :
    opsOf (eraseH H) p x = opsOf H p x := by
  unfold opsOf eraseH
  rw [List.filterMap_map]
  congr 1
  funext e
  exact eraseEv_invOf p x e

@[simp] lemma ressOf_eraseH (H : History P X Op Res) (p : P) (x : X) :
    ressOf (eraseH H) p x = (ressOf H p x).map (fun _ => ()) := by
  unfold ressOf eraseH
  rw [List.filterMap_map, List.map_filterMap]
  congr 1
  funext e
  exact eraseEv_resOf p x e

@[simp] lemma opOf_eraseH (H : History P X Op Res) (a : OpId P X) :
    opOf (eraseH H) a = opOf H a := by
  simp [opOf]

@[simp] lemma invoked_eraseH {H : History P X Op Res} {a : OpId P X} :
    Invoked (eraseH H) a ↔ Invoked H a := by
  simp [Invoked]

@[simp] lemma completed_eraseH {H : History P X Op Res} {a : OpId P X} :
    Completed (eraseH H) a ↔ Completed H a := by
  simp [Completed]

lemma resOf_eraseH (H : History P X Op Res) (a : OpId P X) :
    resOf (eraseH H) a = (resOf H a).map (fun _ => ()) := by
  simp only [resOf, ressOf_eraseH, List.getElem?_map]

@[simp] lemma precedes_eraseH {H : History P X Op Res} {a b : OpId P X} :
    Precedes (eraseH H) a b ↔ Precedes H a b := by
  constructor
  · rintro ⟨β', γ', h, h1, h2⟩
    obtain ⟨β, γ, rfl, rfl, rfl⟩ := List.map_eq_append_iff.1 h
    exact ⟨β, γ, rfl, completed_eraseH.1 h1, fun h => h2 (invoked_eraseH.2 h)⟩
  · rintro ⟨β, γ, rfl, h1, h2⟩
    exact ⟨eraseH β, eraseH γ, eraseH_append β γ, completed_eraseH.2 h1,
      fun h => h2 (invoked_eraseH.1 h)⟩

/-! ### Skeleton linearizations -/

/-- The skeleton specification: every sequential skeleton history is legal. -/
abbrev skelSpecHW : SeqSpec P X Op Unit := fun _ => Set.univ

/-- `M` is a linearization of the skeleton history `H?` (amended Herlihy–Wing definition;
responses are ignored). -/
abbrev IsSkelLinHW (H : History P X Op Res) (M : List (OpRec P X Op Unit)) : Prop :=
  IsLinA skelSpecHW (eraseH H) M

/-- The records of a linearization of `H|x` are operations on `x`. -/
lemma rec_obj_eq_of_isLinA {Res' : Type} {spec : SeqSpec P X Op Res'} {H : History P X Op Res'}
    {x : X} {M : List (OpRec P X Op Res')} (hM : IsLinA spec (restrictX H x) M)
    {e : OpRec P X Op Res'} (he : e ∈ M) : e.x = x := by
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 he
  have hz : ((idsOf M)[i]'(by simpa using hi), M[i]) ∈ (idsOf M).zip M :=
    List.mem_iff_getElem.2 ⟨i, by simpa using hi, by simp⟩
  rw [← (mem_zip_idsOf hz).2]
  exact hM.obj_eq (List.of_mem_zip hz).1

/-! ### Deterministic (quantitative) sequential objects and `τ` -/

/-- The operations of object `x` in the sequential skeleton `M`, keyed by their identities. -/
def objRun (M : List (OpRec P X Op Unit)) (x : X) : List (OpId P X × Op) :=
  (idsOf (M.filter (·.x = x))).zip ((M.filter (·.x = x)).map (·.o))

/-- `tauHW S M a` is the paper's `ret(a, τ_H(M))`: the response of the instance `a` in the unique
legal sequential history of the multi-object specification `S` with skeleton `M`. Objects are
independent, so it is computed by running the operations of object `a.x` in `M` through
`S a.x`. -/
def tauHW (S : X → QSpec Op Res) (M : List (OpRec P X Op Unit)) (a : OpId P X) : Option Res :=
  (S a.x).obj.respIn (S a.x).init (objRun M a.x) a

lemma objRun_filter (M : List (OpRec P X Op Unit)) (x : X) :
    objRun (M.filter (·.x = x)) x = objRun M x := by
  unfold objRun
  rw [List.filter_filter]
  simp

lemma tauHW_filter (S : X → QSpec Op Res) (M : List (OpRec P X Op Unit)) {a : OpId P X} {x : X}
    (hx : a.x = x) : tauHW S (M.filter (·.x = x)) a = tauHW S M a := by
  subst hx
  unfold tauHW
  rw [objRun_filter]

lemma tauHW_eq_of_filter_eq (S : X → QSpec Op Res) {M N : List (OpRec P X Op Unit)}
    {a : OpId P X} (h : M.filter (·.x = a.x) = N.filter (·.x = a.x)) :
    tauHW S M a = tauHW S N a := by
  unfold tauHW objRun
  rw [h]

/-! ### Definition 1 -/

/-- **Definition 1** of Rinberg–Keidar (intermediate value linearizability), for multi-object
histories. A well-formed history `H` is IVL with respect to the deterministic specification `S`
(one deterministic object per `x`) if there are two linearizations `M₁`, `M₂` of the skeleton
history `H?` such that every operation `a` that returns `r` in `H` satisfies
`ret(a, τ(M₁)) ≤ r ≤ ret(a, τ(M₂))`. -/
def IVL [Preorder Res] (S : X → QSpec Op Res) (H : History P X Op Res) : Prop :=
  WellFormed H ∧ ∃ M₁ M₂, IsSkelLinHW H M₁ ∧ IsSkelLinHW H M₂ ∧
    ∀ a r, resOf H a = some r → ∃ r₁ r₂, tauHW S M₁ a = some r₁ ∧ tauHW S M₂ a = some r₂ ∧
      r₁ ≤ r ∧ r ≤ r₂

/-! ### Locality -/

variable [Preorder Res] {S : X → QSpec Op Res}

/-- "Only if" part of locality: the object subhistories of an IVL history are IVL. -/
theorem IVL.restrictX {H : History P X Op Res} (h : IVL S H) (x : X) :
    IVL S (Cslib.SharedMemory.HerlihyWing.restrictX H x) := by
  obtain ⟨hH, M₁, M₂, h₁, h₂, hv⟩ := h
  have hnil : ∀ y, ([] : History P X Op Unit) ∈ skelSpecHW (P := P) y := fun _ => trivial
  have hlin : ∀ M, IsSkelLinHW H M →
      IsSkelLinHW (Cslib.SharedMemory.HerlihyWing.restrictX H x) (M.filter (·.x = x)) := by
    intro M hM
    have := IsLinA.restrictX (wellFormed_eraseH hH) hM hnil x
    rwa [restrictX_eraseH] at this
  refine ⟨wellFormed_restrictX hH x, _, _, hlin M₁ h₁, hlin M₂ h₂, ?_⟩
  intro a r hr
  have hax : a.x = x := (completed_restrictX.1 (Completed.of_resOf hr)).1
  rw [resOf_restrictX hax] at hr
  rw [tauHW_filter S M₁ hax, tauHW_filter S M₂ hax]
  exact hv a r hr

/-- "If" part of locality: a well-formed history whose object subhistories are IVL is IVL. -/
theorem IVL.of_restrictX {H : History P X Op Res} (hH : WellFormed H)
    (h : ∀ x, IVL S (Cslib.SharedMemory.HerlihyWing.restrictX H x)) : IVL S H := by
  choose _ M₁ M₂ h₁ h₂ hv using h
  have h₁' : ∀ x, IsLinA skelSpecHW (Cslib.SharedMemory.HerlihyWing.restrictX (eraseH H) x)
      (M₁ x) := fun x => by rw [restrictX_eraseH]; exact h₁ x
  have h₂' : ∀ x, IsLinA skelSpecHW (Cslib.SharedMemory.HerlihyWing.restrictX (eraseH H) x)
      (M₂ x) := fun x => by rw [restrictX_eraseH]; exact h₂ x
  refine ⟨hH, mergedM (H := eraseH H) M₁, mergedM (H := eraseH H) M₂,
    isLinA_mergedM h₁' (wellFormed_eraseH hH), isLinA_mergedM h₂' (wellFormed_eraseH hH), ?_⟩
  intro a r hr
  have hself : ∀ (Ms : X → List (OpRec P X Op Unit)),
      (∀ x, IsLinA skelSpecHW (Cslib.SharedMemory.HerlihyWing.restrictX (eraseH H) x) (Ms x)) →
      tauHW S (mergedM (H := eraseH H) Ms) a = tauHW S (Ms a.x) a := by
    intro Ms hMs
    apply tauHW_eq_of_filter_eq
    rw [mergedM_filter hMs, eq_comm, List.filter_eq_self]
    intro e he
    simpa using rec_obj_eq_of_isLinA (hMs a.x) he
  rw [hself M₁ h₁', hself M₂ h₂']
  exact hv a.x a r (by rw [resOf_restrictX rfl]; exact hr)

/-- **Locality of IVL** (Rinberg–Keidar, Theorem in Section 3.2, proof in Appendix A): a
well-formed history `H` over a set of objects `X` is IVL iff for each object `x ∈ X`, `H|x` is
IVL. -/
theorem ivl_locality {H : History P X Op Res} (hH : WellFormed H) :
    IVL S H ↔ ∀ x, IVL S (Cslib.SharedMemory.HerlihyWing.restrictX H x) :=
  ⟨fun h x => h.restrictX x, IVL.of_restrictX hH⟩

/-! ### Bridge to the single-object, execution-level definition `IsIVL` -/

section Bridge

open Cslib.SharedMemory (ObjSpec Label)

lemma respIn_map_key {K K' : Type} [DecidableEq K] [DecidableEq K'] (A : ObjSpec) {f : K → K'}
    (hf : Function.Injective f) (q : A.State) (L : List (K × A.Op)) (b : K) :
    A.respIn q (L.map fun y => (f y.1, y.2)) (f b) = A.respIn q L b := by
  induction L generalizing q with
  | nil => rfl
  | cons y L ih =>
    obtain ⟨c, o⟩ := y
    simp only [List.map_cons, ObjSpec.respIn_cons, hf.eq_iff]
    split_ifs <;> first | rfl | exact ih _

variable {A : ObjSpec}

lemma toHist_skel (α : List (Label P A)) : toHist (skel α) = eraseH (toHist α) := by
  induction α with
  | nil => rfl
  | cons ℓ α ih =>
    rw [skel_cons, toHist_cons, toHist_cons, eraseH_append, ← ih]
    cases ℓ <;> rfl

lemma objRun_unit {Op : Type} (M : List (OpRec P Unit Op Unit)) :
    objRun M () = (idsOf M).zip (M.map (·.o)) := by
  unfold objRun
  rw [List.filter_eq_self.2 (by simp)]

omit [DecidableEq P] in
lemma map_o_recsOf (B : ObjSpec) (q : B.State) (L : List (Cslib.SharedMemory.OpId P × B.Op)) :
    (recsOf B q L).map (·.o) = L.map (·.2) := by
  induction L generalizing q with
  | nil => rfl
  | cons y L ih => obtain ⟨x, o⟩ := y; simp [recsOf, ih]

omit [DecidableEq P] in
lemma zip_map_fst_snd {K K' B : Type} (f : K → K') (L : List (K × B)) :
    ((L.map Prod.fst).map f).zip (L.map (·.2)) = L.map fun y => (f y.1, y.2) := by
  induction L with
  | nil => rfl
  | cons y L ih => simp only [List.map_cons, List.zip_cons_cons, ih]

/-- A skeleton linearization in the sense of `Defs.lean` gives one in the sense of `IsLinA`,
with the same `τ`. -/
lemma exists_isSkelLinHW {α : List (Label P A)} (hα : Cslib.SharedMemory.WellFormed α)
    {L : List (Cslib.SharedMemory.OpId P × A.Op)} (hL : IsSkelLin α L) :
    ∃ M, IsSkelLinHW (toHist α) M ∧
      ∀ (S : QSpec A.Op A.Resp) a, tauHW (fun _ => S) M a = tau S L (uid a) := by
  have hα' : Cslib.SharedMemory.WellFormed (skel α) := by
    have := wellFormed_eraseH ((wellFormed_toHist_iff α).2 hα)
    rw [← toHist_skel] at this
    exact (wellFormed_toHist_iff _).1 this
  have hM := isLinA_of_isLinearization hα' hL
  rw [toHist_skel] at hM
  set M : List (OpRec P Unit A.Op Unit) := recsOf (skelSpec A) () L with hMdef
  have hids : idsOf M = (L.map Prod.fst).map cid :=
    idsOf_eq_of_canon _ (fun p => hL.procIds_eq hα' p) _
      (by rw [hMdef, List.map_map]; exact map_p_recsOf (A := skelSpec A) () L)
  refine ⟨M, ⟨⟨hM.recs, hM.complete, ⟨hM.legal.1, fun _ => trivial⟩, hM.procOrder⟩,
    hM.realtime⟩, fun S a => ?_⟩
  have hrun : objRun M () = L.map fun y => (cid y.1, y.2) := by
    rw [objRun_unit, hids, hMdef]
    erw [map_o_recsOf (skelSpec A) () L]
    exact zip_map_fst_snd cid L
  show S.obj.respIn S.init (objRun M ()) a = S.obj.respIn S.init L (uid a)
  rw [hrun, ← respIn_map_key S.obj cid_injective, cid_uid]

/-- A skeleton linearization in the sense of `IsLinA` gives one in the sense of `Defs.lean`, with
the same `τ`. -/
lemma exists_isSkelLin {α : List (Label P A)} {M : List (OpRec P Unit A.Op Unit)}
    (hM : IsSkelLinHW (toHist α) M) :
    ∃ L, IsSkelLin α L ∧
      ∀ (S : QSpec A.Op A.Resp) a, tau S L (uid a) = tauHW (fun _ => S) M a := by
  have hrun : ∀ N : List (OpRec P Unit A.Op Unit), runOK (skelSpec A).δ () N := by
    intro N
    induction N with
    | nil => trivial
    | cons e N ih => exact ⟨rfl, ih⟩
  have hM' : IsLinA (specOf (skelSpec A)) (toHist (skel α)) M := by
    rw [toHist_skel]
    refine ⟨⟨hM.recs, hM.complete, ⟨hM.legal.1, fun x => ?_⟩, hM.procOrder⟩, hM.realtime⟩
    rw [restrictX_seqHist]
    exact seqHist_mem_detSpec.2 (hrun _)
  refine ⟨_, isLinearization_of_isLinA hM', fun S a => ?_⟩
  have h1 : toCslibLin (A := skelSpec A) M = (objRun M ()).map fun y => (uid y.1, y.2) := by
    rw [objRun_unit, toCslibLin, List.zip_map_right, List.map_map]
    rfl
  show S.obj.respIn S.init (toCslibLin (A := skelSpec A) M) (uid a) =
    S.obj.respIn S.init (objRun M ()) a
  rw [h1, respIn_map_key S.obj uid_injective]

/-- For a single object, `IVL` is the execution-level Definition 1 `IsIVLFor` of `Defs.lean`:
a well-formed execution `α` is IVL with respect to `S` iff its history `toHist α` is. -/
theorem isIVLFor_iff_ivl_toHist [Preorder A.Resp] (S : QSpec A.Op A.Resp) {α : List (Label P A)}
    (hα : Cslib.SharedMemory.WellFormed α) :
    IsIVLFor S α ↔ IVL (fun _ => S) (toHist α) := by
  constructor
  · rintro ⟨L₁, L₂, h₁, h₂, hv⟩
    obtain ⟨M₁, hM₁, ht₁⟩ := exists_isSkelLinHW hα h₁
    obtain ⟨M₂, hM₂, ht₂⟩ := exists_isSkelLinHW hα h₂
    refine ⟨(wellFormed_toHist_iff α).2 hα, M₁, M₂, hM₁, hM₂, fun a r hr => ?_⟩
    rw [resOf_toHist] at hr
    rw [ht₁ S, ht₂ S]
    exact hv _ r hr
  · rintro ⟨-, M₁, M₂, h₁, h₂, hv⟩
    obtain ⟨L₁, hL₁, ht₁⟩ := exists_isSkelLin h₁
    obtain ⟨L₂, hL₂, ht₂⟩ := exists_isSkelLin h₂
    refine ⟨L₁, L₂, hL₁, hL₂, fun a r hr => ?_⟩
    have := hv (cid a) r (by rw [resOf_toHist, uid_cid]; exact hr)
    rwa [← ht₁ S, ← ht₂ S, uid_cid] at this

/-- `isIVLFor_iff_ivl_toHist` for the specification of the interface object `A` itself. -/
theorem isIVL_iff_ivl_toHist [Preorder A.Resp] {α : List (Label P A)}
    (hα : Cslib.SharedMemory.WellFormed α) :
    IsIVL A α ↔ IVL (fun _ => A.toQSpec) (toHist α) :=
  isIVLFor_iff_ivl_toHist A.toQSpec hα

end Bridge

end Podc.IntermediateValueLin.HW
