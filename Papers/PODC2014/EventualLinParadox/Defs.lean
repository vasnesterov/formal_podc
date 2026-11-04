import Mathlib

/-!
# Histories, weak consistency and `t`-linearizability (Section 3)

Guerraoui, Ruppert. *A Paradox of Eventual Linearizability in Shared Memory.* PODC 2014.

We formalize the history-level notions of Section 3 for **finite and infinite** histories.

* `ObjType Q Op Res`: a sequential specification `(Q, Q₀, INV, RES, δ)` with a transition
  *relation* `δ q op r q'` (possibly nondeterministic, possibly partial). `Deterministic`,
  `FiniteNondet`, `Total`.
* `History P X Op Res := ℕ → Option (Ev P X Op Res)`: a *timed* history. Position `i` carries at
  most one event: an invocation `inv p x op` (process `p` invokes `op` on object `x`) or a
  response `res a r`, where `a` is the position of the matching invocation. **An operation is
  identified by the position of its invocation.** Positions without an event (`none`) are
  allowed; a gap-free history is literally the paper's sequence of events, and the paper's
  "first `t` events" are then the positions `< t`. Gaps make positions invariant under taking
  prefixes (`take`) and restricting to an object (`restrict`), and let an execution produce its
  history step by step (one position per step).
* `SeqHist Res := ℕ → Option (ℕ × Res)`: a (finite or infinite) sequential history, an entry
  `(a, r)` meaning "operation `a` with response `r`", again with gaps allowed (only the order of
  the entries matters). `Legal spec H S`: every entry is an operation invoked in `H`, and for every
  object `x` there is a sequence of states `q₀ ∈ Q₀, q₁, …` following `δ` along the entries on `x`.
* `WeaklyConsistent` (Definition 1), `IsTLin`/`TLinearizable` (Definition 2),
  `EventuallyLinearizable` (Definition 3), `Linearizable` (`0`-linearizable).
-/

namespace Podc.EventualLinParadox

/-- A sequential specification `(Q, Q₀, INV, RES, δ)` (Section 3). -/
structure ObjType (Q Op Res : Type) where
  /-- The possible initial states `Q₀`. -/
  init : Set Q
  /-- The transition relation: `δ q op r q'`. -/
  δ : Q → Op → Res → Q → Prop

namespace ObjType

variable {Q Op Res : Type} (T : ObjType Q Op Res)

/-- For every state and operation there is a unique response and new state. -/
def Deterministic : Prop := ∀ q op, ∃! rq : Res × Q, T.δ q op rq.1 rq.2

/-- For every state and operation there are finitely many responses and new states. -/
def FiniteNondet : Prop := ∀ q op, {rq : Res × Q | T.δ q op rq.1 rq.2}.Finite

/-- Every operation can be applied in every state. -/
def Total : Prop := ∀ q op, ∃ r q', T.δ q op r q'

/-- The type initialized to the state `q₀` (an object of type `T` initialized to `q₀`). -/
def initAt (q₀ : Q) : ObjType Q Op Res := { T with init := {q₀} }

lemma Deterministic.total {T : ObjType Q Op Res} (h : T.Deterministic) : T.Total := fun q op =>
  let ⟨rq, hrq, _⟩ := h q op; ⟨rq.1, rq.2, hrq⟩

end ObjType

/-- An event: an invocation of `op` by process `p` on object `x`, or the response `r` to the
operation invoked at position `a`. -/
inductive Ev (P X Op Res : Type) where
  | inv (p : P) (x : X) (op : Op)
  | res (a : ℕ) (r : Res)

/-- A (finite or infinite) timed history. -/
abbrev History (P X Op Res : Type) := ℕ → Option (Ev P X Op Res)

/-- A (finite or infinite) sequential history: entries `(operation, response)`; gaps allowed. -/
abbrev SeqHist (Res : Type) := ℕ → Option (ℕ × Res)

variable {P X Op Res Q : Type}

section History

variable (H : History P X Op Res)

/-- Operation `a` is invoked in `H`. -/
def Invoked (a : ℕ) : Prop := ∃ p x op, H a = some (.inv p x op)

/-- Operation `a` has a response in `H`. -/
def Completed (a : ℕ) : Prop := ∃ j r, H j = some (.res a r)

/-- `a` precedes `b` in real time: the response of `a` comes before the invocation of `b`. -/
def Precedes (a b : ℕ) : Prop := ∃ j r, H j = some (.res a r) ∧ j < b ∧ Invoked H b

/-- `a` and `b` are invoked by the same process. -/
def SameProc (a b : ℕ) : Prop :=
  ∃ p x x' op op', H a = some (.inv p x op) ∧ H b = some (.inv p x' op')

/-- `a` is an operation on object `x`. -/
def OnObj (x : X) (a : ℕ) : Prop := ∃ p op, H a = some (.inv p x op)

/-- The prefix of `H` consisting of the positions `< m`. -/
def take (m : ℕ) : History P X Op Res := fun i => if i < m then H i else none

open Classical in
/-- The restriction `H|x` of `H` to the events on object `x` (positions are kept). -/
noncomputable def restrict (x : X) : History P X Op Res := fun i =>
  match H i with
  | some (.inv p y op) => if y = x then some (.inv p y op) else none
  | some (.res a r) => if OnObj H x a then some (.res a r) else none
  | none => none

/-- Well-formedness: responses answer earlier invocations, at most once, and each process
invokes a new operation only after its previous operation responded. -/
structure WellFormed : Prop where
  res_inv : ∀ a j r, H j = some (.res a r) → a < j ∧ Invoked H a
  res_unique : ∀ a j j' r r', H j = some (.res a r) → H j' = some (.res a r') → j = j'
  seq : ∀ a b p x x' op op', H a = some (.inv p x op) → H b = some (.inv p x' op') → a < b →
    ∃ j r, j < b ∧ H j = some (.res a r)

end History

namespace SeqHist

variable (S : SeqHist Res)

/-- Every operation appears at most once. -/
def Nodup : Prop := ∀ k k' a r r', S k = some (a, r) → S k' = some (a, r') → k = k'

/-- Operation `a` appears in `S`. -/
def Mem (a : ℕ) : Prop := ∃ k r, S k = some (a, r)

/-- `a` appears before `b` in `S`. -/
def Before (a b : ℕ) : Prop := ∃ k k' r r', k < k' ∧ S k = some (a, r) ∧ S k' = some (b, r')

end SeqHist

/-- One step of the state sequence of object `x` along the entry `e` of a sequential history. -/
def SeqStep (T : ObjType Q Op Res) (H : History P X Op Res) (x : X) :
    Option (ℕ × Res) → Q → Q → Prop
  | some (a, r), q, q' =>
    (∃ p op, H a = some (.inv p x op) ∧ T.δ q op r q') ∨ (¬ OnObj H x a ∧ q' = q)
  | none, q, q' => q' = q

/-- A sequential history `S` of operations of `H` is **legal**: every entry is an operation
invoked in `H`, and for each object `x` there is a sequence of states `q₀ ∈ Q₀, q₁, …` such
that each entry on `x` is a transition of `x`'s specification. -/
def Legal (spec : X → ObjType Q Op Res) (H : History P X Op Res) (S : SeqHist Res) : Prop :=
  (∀ k a r, S k = some (a, r) → Invoked H a) ∧
  ∀ x, ∃ q : ℕ → Q, q 0 ∈ (spec x).init ∧ ∀ k, SeqStep (spec x) H x (S k) (q k) (q (k + 1))

/-- **Definition 1** (weak consistency). For each operation `a` with a response `r` (at
position `j`) there is a legal sequential history that contains only operations invoked before
`a` terminates, contains all operations of `a`'s process that precede `a`, and ends with `a`
with response `r`. -/
def WeaklyConsistent (spec : X → ObjType Q Op Res) (H : History P X Op Res) : Prop :=
  ∀ a j r, H j = some (.res a r) → ∃ S : SeqHist Res, S.Nodup ∧ Legal spec H S ∧
    (∀ b, S.Mem b → b < j) ∧
    (∀ b, SameProc H b a → Precedes H b a → S.Mem b) ∧
    (∃ k, S k = some (a, r) ∧ ∀ k', k < k' → S k' = none)

/-- **Definition 2** (`t`-linearization). `H'` is the part of `H` at positions `≥ t`. -/
structure IsTLin (spec : X → ObjType Q Op Res) (H : History P X Op Res) (t : ℕ)
    (S : SeqHist Res) : Prop where
  nodup : S.Nodup
  /-- `S` is legal (in particular each operation of `S` is invoked in `H`). -/
  legal : Legal spec H S
  /-- Each operation completed in `H` is in `S`. -/
  complete : ∀ a j r, H j = some (.res a r) → S.Mem a
  /-- Real-time order of `H'` is respected (for operations of `S`). -/
  rt : ∀ a b j r, H j = some (.res a r) → t ≤ j → j < b → Invoked H b → S.Mem b → S.Before a b
  /-- Operations with a response in `H'` have the same response in `S`. -/
  resp : ∀ a j r, H j = some (.res a r) → t ≤ j → ∃ k, S k = some (a, r)

/-- `H` is `t`-linearizable. -/
def TLinearizable (spec : X → ObjType Q Op Res) (H : History P X Op Res) (t : ℕ) : Prop :=
  ∃ S, IsTLin spec H t S

/-- `H` is linearizable (`0`-linearizable, [Herlihy–Wing]). -/
def Linearizable (spec : X → ObjType Q Op Res) (H : History P X Op Res) : Prop :=
  TLinearizable spec H 0

/-- **Definition 3** (eventual linearizability of a history). -/
def EventuallyLinearizable (spec : X → ObjType Q Op Res) (H : History P X Op Res) : Prop :=
  WeaklyConsistent spec H ∧ ∃ t, TLinearizable spec H t

/-- The **fetch&increment** type (Section 3.2): the state is a natural number, initially `0`;
the single operation `fetch&inc` adds one and returns the old value. -/
def fai : ObjType ℕ Unit ℕ where
  init := {0}
  δ q _ r q' := r = q ∧ q' = q + 1

lemma fai_deterministic : fai.Deterministic := fun q _ =>
  ⟨(q, q + 1), ⟨rfl, rfl⟩, fun ⟨r, q'⟩ ⟨h1, h2⟩ => by simp_all⟩

end Podc.EventualLinParadox
