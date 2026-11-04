import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Locality
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Nonblocking
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.DetSpec

/-!
# Weak consistency, t-permutations and t-linearizations (Section 3.2)

We formalize the history-level notions of Serafini, Dobre, Majuntke, Bokor and Suri,
*Eventually Linearizable Shared Objects* (PODC 2010), on top of the Herlihy–Wing history
framework of CSLib (`Cslib.SharedMemory.HerlihyWing`): histories are lists of invocation and
response events `inv p x o` / `res p x r`, and an operation instance is identified by its
`OpId` `(p, x, k)` (the `k`-th operation of process `p` on object `x`), which is invariant under
restriction to an object.

* `IdSeq`: a sequential history whose operations carry explicit identities (an operation of `H`
  together with the record `⟨p, x, o, r⟩` it has in the sequential history). The results `r`
  need not be the results of `H`. Unlike the CSLib list characterizations (`idsOf`), explicit
  identities do not force a process's operations to appear in program order: the paper's
  `τ(i, o)` and `t`-permutations need not respect program order of other processes (or of
  operations invoked before `t`).
* `IsSeqOf spec H L`: `L` is a legal sequential history of distinct operations of `H`.
* `WeaklyConsistent spec H`: for every operation `o` completed by `p_i` there is a legal
  sequential history `τ(i, o)` (we index it by the operation, whose identity contains its
  process) with (i) last operation `o`, with its result in `H`; (ii) only operations invoked in
  `H` before `o` completed; (iii) `τ(i, o') ⊆ τ(i, o)` for the operations `o'` of `p_i` invoked
  before `o`.
* `after invTime t`: the operations invoked after time `t` (for a global clock `invTime`).
  All definitions below are stated for an arbitrary set `A` of "late" operations (the
  operations invoked after `t`); `A = after invTime t` gives the paper's notions.
* `IsTPerm spec H A L`: `L` is a `t`-permutation: (P1) the operations of `L` are exactly those
  invoked in `H`; (P2) `<_{H,t} ⊆ <_L`, where `o₁ <_{H,t} o₂` iff `o₂` is late and the response
  of `o₁` precedes the invocation of `o₂`.
* `IsTLin spec H A L`: `L` is a `t`-linearization: a `t`-permutation in which completed late
  operations have their results in `H`. `TLinearizable spec H A`.
-/

-- CSLib candidate: weak consistency and t-linearizability on Herlihy–Wing histories
-- (Cslib/Computability/Distributed/SharedMemory/HerlihyWing/EventualLin.lean).
namespace Podc.EventualLinearizability

open Cslib.SharedMemory.HerlihyWing

variable {P X Op Res : Type} [DecidableEq P] [DecidableEq X]

/-- A sequential history with explicit operation identities. -/
abbrev IdSeq (P X Op Res : Type) := List (OpId P X × OpRec P X Op Res)

/-- The identities of the operations of `L`, in order. -/
abbrev IdSeq.ids (L : IdSeq P X Op Res) : List (OpId P X) := L.map Prod.fst

/-- The records of `L`, in order: `seqHist L.recs` is the sequential history. -/
abbrev IdSeq.recs (L : IdSeq P X Op Res) : List (OpRec P X Op Res) := L.map Prod.snd

/-- `L` is a legal sequential history of distinct operations of `H`: every entry `(a, e)` is an
operation `a` invoked in `H` with its operation `e.o` (and its process and object), the
identities are distinct, and the sequential history `seqHist L.recs` is legal. -/
structure IsSeqOf (spec : SeqSpec P X Op Res) (H : History P X Op Res)
    (L : IdSeq P X Op Res) : Prop where
  ofHist : ∀ ae ∈ L, ae.2.p = ae.1.p ∧ ae.2.x = ae.1.x ∧ opOf H ae.1 = some ae.2.o
  nodup : L.ids.Nodup
  legal : Legal spec (seqHist L.recs)

/-- The conditions (i)–(iii) of weak consistency for a family `τ` of sequential histories, one
for each completed operation `a` (the paper's `τ(i, o)` with `o = a` and `p_i = a.p`). -/
def WCWitness (spec : SeqSpec P X Op Res) (H : History P X Op Res)
    (τ : OpId P X → IdSeq P X Op Res) : Prop :=
  ∀ a, Completed H a →
    IsSeqOf spec H (τ a) ∧
    -- (i) the last event of `τ(i, o)` is a response of `o` with its result in `H`
    (∃ e, (τ a).getLast? = some (a, e) ∧ resOf H a = some e.r) ∧
    -- (ii) every operation of `τ(i, o)` is invoked in `H` before `o` completes
    (∀ b ∈ (τ a).ids, ¬ Precedes H a b) ∧
    -- (iii) `τ(i, o') ⊆ τ(i, o)` for every operation `o'` invoked by `p_i` before `o`
    (∀ b, b.p = a.p → Precedes H b a → ∀ c ∈ (τ b).ids, c ∈ (τ a).ids)

/-- **Weak consistency** (Section 3.2). -/
def WeaklyConsistent (spec : SeqSpec P X Op Res) (H : History P X Op Res) : Prop :=
  ∃ τ, WCWitness spec H τ

/-- The operations invoked after time `t`, for a global clock assigning to every operation
the time of its invocation. -/
def after (invTime : OpId P X → ℕ) (t : ℕ) : Set (OpId P X) := {a | t < invTime a}

omit [DecidableEq P] [DecidableEq X] in
lemma after_anti (invTime : OpId P X → ℕ) {t t' : ℕ} (h : t ≤ t') :
    after invTime t' ⊆ after invTime t := fun _ ha => lt_of_le_of_lt h ha

/-- The relation `<_{H,t}` with `A` = the operations invoked after `t`: `b` is late and the
response of `a` precedes the invocation of `b`. -/
def RTAfter (H : History P X Op Res) (A : Set (OpId P X)) (a b : OpId P X) : Prop :=
  b ∈ A ∧ Invoked H b ∧ Precedes H a b

/-- **`t`-permutation** (Section 3.2): (P1) the operations of `L` are exactly the operations
invoked in `H`, and (P2) `<_{H,t} ⊆ <_L`. Results need not match `H`. -/
structure IsTPerm (spec : SeqSpec P X Op Res) (H : History P X Op Res)
    (A : Set (OpId P X)) (L : IdSeq P X Op Res) : Prop extends IsSeqOf spec H L where
  all : ∀ a, Invoked H a → a ∈ L.ids
  order : ∀ a b, RTAfter H A a b → [a, b].Sublist L.ids

/-- **`t`-linearization** (Section 3.2): a `t`-permutation where the results of all (completed)
operations invoked after `t` are the same as in `H`. -/
structure IsTLin (spec : SeqSpec P X Op Res) (H : History P X Op Res)
    (A : Set (OpId P X)) (L : IdSeq P X Op Res) : Prop extends IsTPerm spec H A L where
  results : ∀ a e, (a, e) ∈ L → a ∈ A → Completed H a → resOf H a = some e.r

/-- `H` is `t`-linearizable (`A` = the operations invoked after `t`). -/
def TLinearizable (spec : SeqSpec P X Op Res) (H : History P X Op Res)
    (A : Set (OpId P X)) : Prop :=
  ∃ L, IsTLin spec H A L

/-- `t`-linearizability is monotone in the set of late operations (a larger `t` is weaker). -/
lemma IsTLin.mono {spec : SeqSpec P X Op Res} {H : History P X Op Res} {A B : Set (OpId P X)}
    {L : IdSeq P X Op Res} (h : IsTLin spec H A L) (hBA : B ⊆ A) : IsTLin spec H B L :=
  { h with
    order := fun a b hab => h.order a b ⟨hBA hab.1, hab.2⟩
    results := fun a e hae ha hc => h.results a e hae (hBA ha) hc }

lemma TLinearizable.mono {spec : SeqSpec P X Op Res} {H : History P X Op Res}
    {A B : Set (OpId P X)} (h : TLinearizable spec H A) (hBA : B ⊆ A) :
    TLinearizable spec H B :=
  let ⟨L, hL⟩ := h; ⟨L, hL.mono hBA⟩

end Podc.EventualLinearizability
