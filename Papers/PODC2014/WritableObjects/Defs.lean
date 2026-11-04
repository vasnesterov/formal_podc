import Cslib.Computability.Distributed.SharedMemory.History

/-!
# Making objects writable: the template of Figure 4.4

Definitions for Aghazadeh, Golab, Woelfel, *Making Objects Writable*, PODC 2014, in the numbering
of Chapter 4 of Aghazadeh's PhD thesis (U. Calgary 2018), which contains the full proofs.

## Model

A *writable type* `T` (an `ObjSpec` from CSLib) has operations `wr v` that set the state to `v`
regardless of the current state (`Writable`). A *sequentially writable* object `SW` of type `T`
is an implementation whose histories are linearizable provided that no write overlaps any other
operation (`SeqWritable`). The paper turns an array `A` of such objects plus a register `Ptr`
into a linearizable object `WT` of type `T` (template of Figure 4.4):

* `Write(v)` by `p`: choose a write-index `f` owned by `p` that is not in use, call
  `A[f].SWrite(v)`, then write `f` to `Ptr`;
* `Exec(o)` by `q` (for a non-write operation `o`): determine an exec-index `i`, call
  `A[i].Oper(o)` and return its response.

We work with *transcripts*: lists of the events (`Ev`) relevant to the template, i.e. the
invocations and responses of the high-level operations on `WT`, the invocations and responses of
operations on the objects `A[i]`, and the writes to `Ptr`. All other steps (accesses of auxiliary
registers, internal steps of the `SW` objects) are omitted: they do not affect any of the notions
below. The high-level history `highH W α` and the history `lowH W i α` of the object `A[i]` are
CSLib histories (`List (Label P T)`), so CSLib's `IsLinearization` applies to both.

A *point* `t ≤ α.length` is the moment after the first `t` events of `α`; `ptrAt α t` is the value
of `Ptr` at point `t` (`none` = `⊥`, the initial value).

* `Template W owner α`: every process follows the template (a per-process control automaton
  `PStep`, witnessed by control states `σ p t`), only the owner of an index `f` performs
  `A[f].SWrite`, and `A[f]` is not in use when the `SWrite` is invoked.
* `CondC α`: condition (C) of Lemma 4.5.
-/

namespace Podc.WritableObjects

open Cslib.SharedMemory

/-- A *writable* type: `wr v` changes the state to `v` regardless of the current state (and its
response `wresp v` does not depend on the current state; in the paper `Write()` returns
nothing). -/
structure Writable (T : ObjSpec) where
  /-- The write operation `Write(v)`. -/
  wr : T.State → T.Op
  /-- The (state-independent) response of `Write(v)`. -/
  wresp : T.State → T.Resp
  δ_wr : ∀ s v, T.δ s (wr v) = (v, wresp v)

variable {P ι : Type} {T : ObjSpec}

/-- The events of a transcript of an implementation following the template of Figure 4.4. -/
inductive Ev (P ι : Type) (T : ObjSpec) where
  /-- `p` invokes `WT.Write(v)`. -/
  | winv (p : P) (v : T.State)
  /-- `p` invokes `WT.Exec(o)`. -/
  | einv (p : P) (o : T.Op)
  /-- `p` returns `r` from its pending operation on `WT`. -/
  | hret (p : P) (r : T.Resp)
  /-- `p` invokes `A[i].SWrite(v)`. -/
  | swinv (p : P) (i : ι) (v : T.State)
  /-- `p` invokes `A[i].Oper(o)`. -/
  | opinv (p : P) (i : ι) (o : T.Op)
  /-- the pending operation of `p` on `A[i]` returns `r`. -/
  | aret (p : P) (i : ι) (r : T.Resp)
  /-- `p` writes `i` to `Ptr`. -/
  | ptr (p : P) (i : ι)

namespace Ev

/-- The process executing an event. -/
def proc : Ev P ι T → P
  | winv p _ | einv p _ | hret p _ | swinv p _ _ | opinv p _ _ | aret p _ _ | ptr p _ => p

/-- The high-level label of an event (`Write(v)` is the operation `W.wr v` of `T`). -/
def toHigh (W : Writable T) : Ev P ι T → Option (Label P T)
  | winv p v => some (.inv p (W.wr v))
  | einv p o => some (.inv p o)
  | hret p r => some (.ret p r)
  | _ => none

/-- The label of an event in the history of the base object `A[i]`. -/
def toLow [DecidableEq ι] (W : Writable T) (i : ι) : Ev P ι T → Option (Label P T)
  | swinv p j v => if j = i then some (.inv p (W.wr v)) else none
  | opinv p j o => if j = i then some (.inv p o) else none
  | aret p j r => if j = i then some (.ret p r) else none
  | _ => none

/-- The index written to `Ptr` by a `ptr` event. -/
def ptrVal : Ev P ι T → Option ι
  | ptr _ i => some i
  | _ => none

end Ev

/-- The history of the implemented object `WT`. -/
def highH (W : Writable T) (α : List (Ev P ι T)) : List (Label P T) :=
  α.filterMap (Ev.toHigh W)

/-- The history of the base object `A[i]`. -/
def lowH [DecidableEq ι] (W : Writable T) (i : ι) (α : List (Ev P ι T)) : List (Label P T) :=
  α.filterMap (Ev.toLow W i)

/-- The value of `Ptr` at point `t` (after the first `t` events); `none` is the initial `⊥`. -/
def ptrAt (α : List (Ev P ι T)) (t : ℕ) : Option ι :=
  ((α.take t).filterMap Ev.ptrVal).getLast?

/-! ## Sequential writability -/

/-- In the history `h` of a base object, no write operation (`W.wr v`) overlaps any other
operation: for every write instance `x` and every other invoked instance `y`, one of them
precedes the other in real time. -/
def WritesIsolated [DecidableEq P] (W : Writable T) (h : List (Label P T)) : Prop :=
  ∀ x y : OpId P, x ≠ y → (∃ v, opOf h x = some (W.wr v)) → Invoked h y →
    Precedes h x y ∨ Precedes h y x

/-- The history `h` of a base object is admissible for a *sequentially writable* object: if no
write overlaps another operation, then `h` is linearizable (w.r.t. `T`). -/
def SeqWritable [DecidableEq P] (W : Writable T) (h : List (Label P T)) : Prop :=
  WritesIsolated W h → ∃ L, IsLinearization h L

/-! ## The template (Figure 4.4) -/

/-- Control states of a process following the template. -/
inductive PSt (ι : Type) (T : ObjSpec) where
  /-- no pending operation on `WT` -/
  | idle
  /-- in `Write(v)`, before `A[f].SWrite(v)` -/
  | wBeg (v : T.State)
  /-- in `Write(v)`, `A[f].SWrite(v)` pending -/
  | wSW (v : T.State) (f : ι)
  /-- in `Write(v)`, `A[f].SWrite(v)` returned, `Ptr` not yet written -/
  | wPtr (v : T.State) (f : ι)
  /-- in `Write(v)`, after writing `Ptr` -/
  | wEnd (v : T.State)
  /-- in `Exec(o)`, before `A[i].Oper(o)` -/
  | eBeg (o : T.Op)
  /-- in `Exec`, `A[i].Oper` pending -/
  | eOp (i : ι)
  /-- in `Exec`, `A[i].Oper` returned `r` -/
  | eEnd (r : T.Resp)

/-- One event of process `p` in the template (Figure 4.4): `Write(v)` = choose a write-index `f`
owned by `p`, `A[f].SWrite(v)`, `Ptr.Write(f)`, return; `Exec(o)` (for a non-write operation
`o`) = `A[i].Oper(o)` for some exec-index `i`, return its response. Other steps (choosing the
indices, auxiliary registers) are not recorded. -/
inductive PStep (W : Writable T) (owner : ι → P) (p : P) : PSt ι T → Ev P ι T → PSt ι T → Prop
  | winv (v : T.State) : PStep W owner p .idle (.winv p v) (.wBeg v)
  | einv (o : T.Op) (ho : ∀ v, o ≠ W.wr v) : PStep W owner p .idle (.einv p o) (.eBeg o)
  | swinv (v : T.State) (f : ι) (hf : owner f = p) :
      PStep W owner p (.wBeg v) (.swinv p f v) (.wSW v f)
  | swret (v : T.State) (f : ι) (r : T.Resp) : PStep W owner p (.wSW v f) (.aret p f r) (.wPtr v f)
  | ptr (v : T.State) (f : ι) : PStep W owner p (.wPtr v f) (.ptr p f) (.wEnd v)
  | wret (v : T.State) : PStep W owner p (.wEnd v) (.hret p (W.wresp v)) .idle
  | opinv (o : T.Op) (i : ι) : PStep W owner p (.eBeg o) (.opinv p i o) (.eOp i)
  | opret (i : ι) (r : T.Resp) : PStep W owner p (.eOp i) (.aret p i r) (.eEnd r)
  | eret (r : T.Resp) : PStep W owner p (.eEnd r) (.hret p r) .idle

/-- The transcript `α` follows the template of Figure 4.4 (with ownership function `owner`):
* every process runs the control automaton `PStep` (witnessed by its control states `σ p t` at
  the points `t`), in particular only the owner of `f` invokes `A[f].SWrite` and only inside a
  `Write` that then writes `f` to `Ptr`;
* `A[f]` is not in use (`Ptr ≠ f`) when `A[f].SWrite` is invoked. (The paper asks this at the
  invocation of the enclosing `Write`, which implies it: `notInUse_of_atWriteInv`.) -/
structure Template (W : Writable T) (owner : ι → P) (α : List (Ev P ι T)) : Prop where
  ctrl : ∃ σ : P → ℕ → PSt ι T, ∀ p, σ p 0 = .idle ∧
    ∀ t (ht : t < α.length),
      (α[t].proc = p → PStep W owner p (σ p t) α[t] (σ p (t + 1))) ∧
      (α[t].proc ≠ p → σ p (t + 1) = σ p t)
  notInUse : ∀ t p f v, α[t]? = some (.swinv p f v) → ptrAt α t ≠ some f

/-- Condition (C) of Lemma 4.5: for each `Exec` call `E` of `q` (invoked at event `e`) that
invokes `Op = A[i].Oper(o)` (at event `t`) there is a point `ts` between the invocation of `E`
and the invocation of `Op` such that
* (C1) `A[i]` is in use at `ts` (`Ptr = i`), and
* (C2) no `A[i].SWrite` overlaps `[ts, Op's response]`: every `A[i].SWrite` (by `p`, invoked at
  event `a`) either has returned before `ts`, or is invoked after `Op` has returned. -/
def CondC (α : List (Ev P ι T)) : Prop :=
  ∀ e t q o o' i, e < t → α[e]? = some (.einv q o') → α[t]? = some (.opinv q i o) →
    (∀ k (hk : k < α.length), e < k → k < t → α[k].proc ≠ q) →
    ∃ ts, e < ts ∧ ts ≤ t ∧ ptrAt α ts = some i ∧
      ∀ a p v, α[a]? = some (.swinv p i v) →
        (∃ b r, a < b ∧ b < ts ∧ α[b]? = some (.aret p i r)) ∨
        (∃ c r, t < c ∧ c < a ∧ α[c]? = some (.aret q i r))

end Podc.WritableObjects
