import Mathlib

/-!
# The model of [AEM15]: replicated data stores, executions, abstract executions

Attiya, Ellen, Morrison. *Limitations of Highly-Available Eventually-Consistent Data Stores.*
PODC 2015.

* Replicas are partial state machines (`Store`): `step i σ e = some σ'` iff event `e` is enabled
  at replica `i` in state `σ` (Section 2). Events are client operations `do(o, op, v)`
  (`Ev.do_`), broadcasts `send(m)` and receipts `recv(m)`.
* A finite execution is a list of `(replica, event)` pairs (`Store.IsExec`, Definition 1): the
  local subsequence of every replica is a run of its state machine and every receipt of `m` at
  `i` is preceded by a `send(m)` at some `j ≠ i`. Infinite executions are sequences all of whose
  prefixes are executions (`Store.IsInfExec`); sufficiently connected ones are
  `Store.SuffConnected` (Definition 3).
* All objects are multi-value registers (MVRs). An abstract execution (`AE`, Definition 4) is
  indexed by `ℕ` with a domain predicate; `ord` is the total order `H`, `vis` the visibility
  relation. `AE.mvr` is the MVR specification (Figure 1b, Definition 7), `AE.Correct`
  Definition 8, `AE.CC` Definition 12, `AE.EC` Definition 13.
* `AE.On A s` says that `A` is an abstract execution on the do-events of the (finite or
  infinite) execution `s`, with the per-replica order of `s`: this is compliance (Definition 9)
  up to renaming the events, see `README.md`.
-/

namespace Podc.EventualConsistencyLimits

/-- Operations on a multi-value register. -/
inductive Op (V : Type*) where
  | read
  | write (v : V)

/-- Responses of operations: `ok` for writes, a set of values for reads. -/
inductive Resp (V : Type*) where
  | ok
  | vals (S : Set V)

/-- A client operation `do(o, op, v)`: object, operation and response. -/
structure DoEv (Obj V : Type*) where
  obj : Obj
  op : Op V
  rv : Resp V

/-- Events of a replica (Section 2). -/
inductive Ev (Obj V M : Type*) where
  | do_ (d : DoEv Obj V)
  | send (m : M)
  | recv (m : M)

/-- A replicated data store: every replica `i` is a state machine with initial state `init i`
and partial transition function `step i`. -/
structure Store (ι Obj V M St : Type*) where
  init : ι → St
  step : ι → St → Ev Obj V M → Option St

variable {ι Obj V M St : Type*}

/-- The subsequence of events of replica `i`. -/
def proj [DecidableEq ι] (i : ι) (α : List (ι × Ev Obj V M)) : List (Ev Obj V M) :=
  α.filterMap fun x => if x.1 = i then some x.2 else none

namespace Store

variable (D : Store ι Obj V M St)

/-- Local run of replica `i` on a sequence of its events. -/
def run (i : ι) (l : List (Ev Obj V M)) : Option St := l.foldlM (D.step i) (D.init i)

variable [DecidableEq ι]

/-- State of replica `i` at the end of the finite sequence `α` (if it is well formed at `i`). -/
def state (i : ι) (α : List (ι × Ev Obj V M)) : Option St := D.run i (proj i α)

/-- Definition 1: well-formed finite executions, built event by event. -/
inductive IsExec : List (ι × Ev Obj V M) → Prop
  | nil : IsExec []
  | snoc {α : List (ι × Ev Obj V M)} {i : ι} {e : Ev Obj V M} {σ σ' : St} :
      IsExec α → D.state i α = some σ → D.step i σ e = some σ' →
      (∀ m, e = .recv m → ∃ j, j ≠ i ∧ (j, .send m) ∈ α) → IsExec (α ++ [(i, e)])

/-- The first `n` events of an infinite sequence. -/
def pre (s : ℕ → ι × Ev Obj V M) (n : ℕ) : List (ι × Ev Obj V M) := (List.range n).map s

/-- Infinite executions: every finite prefix is an execution. -/
def IsInfExec (s : ℕ → ι × Ev Obj V M) : Prop := ∀ n, D.IsExec (pre s n)

/-- Replica `i` has a message pending in state `σ`: some `send` is enabled. -/
def Pending (i : ι) (σ : St) : Prop := ∃ m σ', D.step i σ (.send m) = some σ'

/-- Definition 3: the network is sufficiently connected in an infinite execution:
(1) no replica has a message pending at all events of a suffix, and (2) every message sent is
received by every other replica. -/
def SuffConnected (s : ℕ → ι × Ev Obj V M) : Prop :=
  (∀ i N, ∃ n ≥ N, ∀ σ, D.state i (pre s (n + 1)) = some σ → ¬ D.Pending i σ) ∧
  (∀ p i m, s p = (i, .send m) → ∀ j, j ≠ i → ∃ q, s q = (j, .recv m))

/-! ### Assumptions on data stores -/

/-- Section 2: a replica has no message pending right after a `send` ("a send event relays
everything the replica has to send"). -/
def SendClears : Prop := ∀ i σ m σ', D.step i σ (.send m) = some σ' → ¬ D.Pending i σ'

/-- Definition 15: op-driven messages. -/
def OpDriven : Prop :=
  (∀ i, ¬ D.Pending i (D.init i)) ∧
  ∀ i σ m σ', D.step i σ (.recv m) = some σ' → ¬ D.Pending i σ → ¬ D.Pending i σ'

/-- Definition 16: invisible reads. -/
def InvisibleReads : Prop :=
  ∀ i σ o r σ', D.step i σ (.do_ ⟨o, .read, r⟩) = some σ' → σ' = σ

/-- High availability (implicit in Section 2): every operation can be invoked at every replica
in every state and immediately returns some response. -/
def Available : Prop := ∀ i σ o op, ∃ r σ', D.step i σ (.do_ ⟨o, op, r⟩) = some σ'

/-- Receive events are always enabled (implicit in Section 2: messages may be delivered at any
time, any number of times). -/
def RecvEnabled : Prop := ∀ i σ m, ∃ σ', D.step i σ (.recv m) = some σ'

end Store

/-! ### Abstract executions -/

/-- An abstract execution (Definition 4), indexed by `ℕ` with domain `dom`: `rep e` is the
replica of `e`, `ev e` the operation, `ord` the total order `H` and `vis` the visibility
relation. -/
structure AE (ι Obj V : Type*) where
  dom : ℕ → Prop
  rep : ℕ → ι
  ev : ℕ → DoEv Obj V
  ord : ℕ → ℕ → Prop
  vis : ℕ → ℕ → Prop

namespace AE

variable (A : AE ι Obj V)

/-- Definition 4 (with `ord` a total order on `dom` in which every event has finitely many
predecessors, i.e. `H` is a sequence). -/
structure WF : Prop where
  ord_dom : ∀ {a b}, A.ord a b → A.dom a ∧ A.dom b
  ord_irrefl : ∀ a, ¬ A.ord a a
  ord_trans : ∀ {a b c}, A.ord a b → A.ord b c → A.ord a c
  ord_total : ∀ {a b}, A.dom a → A.dom b → a ≠ b → A.ord a b ∨ A.ord b a
  ord_fin : ∀ b, {a | A.ord a b}.Finite
  /-- Definition 4 (3). -/
  vis_ord : ∀ {a b}, A.vis a b → A.ord a b
  /-- Definition 4 (1). -/
  vis_sess : ∀ {a b}, A.ord a b → A.rep a = A.rep b → A.vis a b
  /-- Definition 4 (2). -/
  vis_mono : ∀ {a b c}, A.vis a b → A.ord b c → A.rep b = A.rep c → A.vis a c

/-- `e` is a write. -/
def IsWrite (e : ℕ) : Prop := ∃ v, (A.ev e).op = .write v

/-- The writes in the operation context of `e` (Definition 7): writes to `obj e` visible
to `e`. -/
def ctxW (e : ℕ) : Set ℕ :=
  {a | A.vis a e ∧ (A.ev a).obj = (A.ev e).obj ∧ A.IsWrite a}

/-- The MVR specification `f_MVR` (Figure 1b) applied to the operation context of `e`. -/
def mvr (e : ℕ) : Resp V :=
  match (A.ev e).op with
  | .write _ => .ok
  | .read => .vals {v | ∃ a ∈ A.ctxW e, (A.ev a).op = .write v ∧ ∀ b ∈ A.ctxW e, ¬ A.vis a b}

/-- Definition 8: every response conforms to the MVR specification. -/
def Correct : Prop := ∀ e, A.dom e → (A.ev e).rv = A.mvr e

/-- Definition 12: causal consistency. -/
def CC : Prop := A.Correct ∧ ∀ a b c, A.vis a b → A.vis b c → A.vis a c

/-- Definition 13: eventual consistency. -/
def EC : Prop :=
  ∀ e, A.dom e → {e' | A.dom e' ∧ (A.ev e').obj = (A.ev e).obj ∧ ¬ A.vis e e'}.Finite

/-- `A` is an abstract execution on the do-events of the (finite or infinite) execution `s`,
with the same per-replica order (compliance, Definition 9). -/
def On (s : ℕ → Option (ι × Ev Obj V M)) : Prop :=
  (∀ p, A.dom p ↔ ∃ i d, s p = some (i, .do_ d)) ∧
  (∀ p i d, s p = some (i, .do_ d) → A.rep p = i ∧ A.ev p = d) ∧
  (∀ p q, A.dom p → A.dom q → A.rep p = A.rep q → p < q → A.ord p q)

end AE

namespace Store

variable (D : Store ι Obj V M St) [DecidableEq ι]

/-- A finite execution as a partial sequence. -/
def seqL (α : List (ι × Ev Obj V M)) : ℕ → Option (ι × Ev Obj V M) := fun p => α[p]?

/-- Causal consistency of a data store (Definitions 10–12): every finite execution complies
with a causally consistent (in particular correct) abstract execution. -/
def CausallyConsistent : Prop :=
  ∀ α, D.IsExec α → ∃ A : AE ι Obj V, A.On (seqL α) ∧ A.WF ∧ A.CC

/-- Eventual consistency of a data store, repaired form of Definition 14: every infinite,
sufficiently connected execution complies with some correct, eventually consistent abstract
execution satisfying `P` (e.g. membership in the consistency model the store satisfies).
See `Def14.lean` for the literal form. -/
def EventuallyConsistent (P : AE ι Obj V → Prop) : Prop :=
  ∀ s, D.IsInfExec s → D.SuffConnected s →
    ∃ A : AE ι Obj V, A.On (fun p => some (s p)) ∧ A.WF ∧ A.Correct ∧ A.EC ∧ P A

end Store

end Podc.EventualConsistencyLimits
