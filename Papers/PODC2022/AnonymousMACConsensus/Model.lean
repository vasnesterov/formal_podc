import Mathlib

/-!
# MAC-SC: a store-collect object over an abstract MAC layer (model)

Tseng, Zhang. *Brief Announcement: Computability and Anonymous Storage-Efficient Consensus with an
Abstract MAC Layer.* PODC 2022.

This file fixes

* the **specification**: histories of `Store`/`Collect` operations and the paper's *regularity*
  condition (Properties I and II, Definition 1), stated purely on histories;
* the **model**: a single-hop abstract MAC layer (every broadcast is delivered to every node,
  including the sender, at most once; the acknowledgment comes only after every node that has not
  crashed yet has received the message), asynchronous nodes, any number of crash failures, one
  background message handler per node with a FIFO queue of delivered messages that has priority
  over the main thread (assumption (iii) of the paper; switched off by `prio = false`);
* **Algorithm 1 (MAC-SC)**.

Values are tagged by the index of the store operation at its node (`Entry V = ℕ × V`): this is the
paper's "every stored value is unique, which can be achieved using sequence numbers and node
identifiers", and it is what makes the merge `A ∪ B` ("the newer value from each node") computable
by a node.
-/

namespace Podc.AnonymousMACConsensus

variable {ι V : Type*}

/-! ## Views -/

/-- A view entry: the index of the store operation at its node (its sequence number) and the
stored value. -/
abbrev Entry (V : Type*) := ℕ × V

/-- A view: at most one entry `(v_j, j)` per node `j` (`none` is `V(j) = ⊥`). -/
abbrev View (ι V : Type*) := ι → Option (Entry V)

/-- The empty view `∅`. -/
def View.empty : View ι V := fun _ => none

/-- The view `{(v, i)}` with one entry. -/
def View.single [DecidableEq ι] (i : ι) (e : Entry V) : View ι V :=
  fun j => if j = i then some e else none

/-- Recency key of an entry: `⊥ ↦ 0`, `(m, v) ↦ m + 1`. -/
def key : Option (Entry V) → ℕ
  | none => 0
  | some (m, _) => m + 1

/-- The newer of two entries of the same node. -/
def newer (x y : Option (Entry V)) : Option (Entry V) := if key x < key y then y else x

/-- The merge `A ∪ B` of the paper: the newer entry for each node. -/
def View.merge (A B : View ι V) : View ι V := fun j => newer (A j) (B j)

/-! ## Operations and histories -/

/-- The operations of a store-collect object. -/
inductive Op (V : Type*)
  | store (v : V)
  | collect

/-- Responses: `ACK` for `Store`, a view for `Collect`. -/
inductive Resp (ι V : Type*)
  | ack
  | view (W : View ι V)

/-- Invocation and response events. The operation `(i, n)` is the `n`-th operation of node `i`;
the stored value of the store operation `(j, m)` is identified by the entry `(m, v)`. -/
inductive Label (ι V : Type*)
  | inv (i : ι) (n : ℕ) (o : Op V)
  | ret (i : ι) (n : ℕ) (r : Resp ι V)

/-- A history: the sequence of invocation and response events of an execution (the real-time
order `<_H` is the order in the list). -/
abbrev History (ι V : Type*) := List (Label ι V)

/-- `e <_H f`: event `e` occurs before event `f`. -/
def Before (h : History ι V) (e f : Label ι V) : Prop :=
  ∃ p q : ℕ, p < q ∧ h[p]? = some e ∧ h[q]? = some f

/-- Operation `a` precedes operation `b`: `resp(a) <_H inv(b)`. -/
def Precedes (h : History ι V) (a b : ι × ℕ) : Prop :=
  ∃ r o, Before h (.ret a.1 a.2 r) (.inv b.1 b.2 o)

/-- `(j, m)` is the operation `Store_j(v)` of the history. -/
def IsStore (h : History ι V) (j : ι) (m : ℕ) (v : V) : Prop :=
  Label.inv j m (.store v) ∈ h

/-- `V₁ ⪯ V₂`: for every `(v₁, j) ∈ V₁` there is `(v₂, j) ∈ V₂` with `v₁ = v₂` or the invocation of
`Store_j(v₂)` after the response of `Store_j(v₁)`. -/
def ViewLE (h : History ι V) (V₁ V₂ : View ι V) : Prop :=
  ∀ j m₁ v₁, V₁ j = some (m₁, v₁) → ∃ m₂ v₂, V₂ j = some (m₂, v₂) ∧
    ((m₂, v₂) = (m₁, v₁) ∨ ∃ r, Before h (.ret j m₁ r) (.inv j m₂ (.store v₂)))

/-- Regularity, first bullet (Property I): for each `Collect` `c = (i, n)` returning `W` and each
node `j`, (i) if `W(j) = ⊥` then no `Store` by `j` precedes `c`; (ii) if `W(j) = v` then the
invocation of `Store_j(v)` precedes `c`'s response, and no `Store_j(v')`, `v' ≠ v`, responds after
`Store_j(v)`'s response and before `c`'s invocation. -/
def RegularI (h : History ι V) : Prop :=
  ∀ i n W, Label.ret i n (.view W) ∈ h → ∀ j,
    (W j = none → ∀ m v, IsStore h j m v → ¬ Precedes h (j, m) (i, n)) ∧
    (∀ m v, W j = some (m, v) →
      Before h (.inv j m (.store v)) (.ret i n (.view W)) ∧
      ¬ ∃ m' v' r r', m' ≠ m ∧ IsStore h j m' v' ∧
        Before h (.ret j m r) (.ret j m' r') ∧ Before h (.ret j m' r') (.inv i n .collect))

/-- Regularity, second bullet (Property II): if collect `c₁` precedes collect `c₂` then
`V₁ ⪯ V₂`. -/
def RegularII (h : History ι V) : Prop :=
  ∀ i₁ n₁ W₁ i₂ n₂ W₂, Label.ret i₁ n₁ (.view W₁) ∈ h → Label.ret i₂ n₂ (.view W₂) ∈ h →
    Precedes h (i₁, n₁) (i₂, n₂) → ViewLE h W₁ W₂

/-- A history *satisfies regularity* (paper, Section 3, before Definition 1). -/
def Regular (h : History ι V) : Prop := RegularI h ∧ RegularII h

/-! ## The abstract MAC layer model running MAC-SC -/

/-- The main thread of a node. `bcast o cv got`: the `mac-broadcast(STORE, cv)` of operation `o`
is in progress and has been delivered to the nodes `got`; `acked o cv`: the acknowledgment has
arrived, the `return` line has not been executed yet. -/
inductive Phase (ι V : Type*)
  | idle
  | invoked (o : Op V)
  | bcast (o : Op V) (cv : View ι V) (got : Set ι)
  | acked (o : Op V) (cv : View ι V)

/-- The pending operation. -/
def Phase.op? : Phase ι V → Option (Op V)
  | .idle => none
  | .invoked o => some o
  | .bcast o _ _ => some o
  | .acked o _ => some o

/-- The view `currentView` of the pending operation, once computed. -/
def Phase.cv? : Phase ι V → Option (View ι V)
  | .idle => none
  | .invoked _ => none
  | .bcast _ cv _ => some cv
  | .acked _ cv => some cv

/-- A global configuration. -/
structure Config (ι V : Type*) where
  /-- The local variable `view_i`. -/
  view : ι → View ι V
  /-- Messages delivered to the node by the MAC layer, not yet processed by its handler. -/
  queue : ι → List (View ι V)
  /-- Number of operations completed by the node (the index of its pending operation). -/
  cnt : ι → ℕ
  /-- State of the main thread. -/
  phase : ι → Phase ι V
  /-- Crashed nodes. -/
  crashed : Set ι

/-- The initial configuration: all views empty, no pending operation. -/
def Config.init : Config ι V := ⟨fun _ => View.empty, fun _ => [], fun _ => 0, fun _ => .idle, ∅⟩

/-- Line 1 (`Store_i(v)`: `view_i ∪ {(v, i)}`) and line 4 (`Collect_i`: `view_i`) of Algorithm 1;
the stored value is tagged with the index of the operation. -/
def lineView [DecidableEq ι] (c : Config ι V) (i : ι) : Op V → View ι V
  | .store v => (c.view i).merge (View.single i (c.cnt i, v))
  | .collect => c.view i

/-- Lines 3 and 6 of Algorithm 1. -/
def resp : Op V → View ι V → Resp ι V
  | .store _, _ => .ack
  | .collect, cv => .view cv

/-- One step of MAC-SC in the abstract MAC layer. `prio`: the message handler has priority over
the main thread (the main thread reads `view_i` only when no delivered message is pending).
Steps that produce no invocation/response event have label `none`. -/
inductive Step [DecidableEq ι] (prio : Bool) : Config ι V → Option (Label ι V) → Config ι V → Prop
  /-- A client invokes an operation at an idle, non-crashed node. -/
  | invoke (c : Config ι V) (i : ι) (o : Op V) (halive : i ∉ c.crashed)
      (hidle : c.phase i = .idle) :
      Step prio c (some (.inv i (c.cnt i) o)) { c with phase := Function.update c.phase i (.invoked o) }
  /-- Lines 1–2 / 4–5: compute `currentView` and call `mac-broadcast`. -/
  | exec (c : Config ι V) (i : ι) (o : Op V) (halive : i ∉ c.crashed)
      (hph : c.phase i = .invoked o) (hq : prio = true → c.queue i = []) :
      Step prio c none
        { c with phase := Function.update c.phase i (.bcast o (lineView c i o) ∅) }
  /-- The MAC layer delivers the message of `i` to `k` (also after `i` crashed). -/
  | deliver (c : Config ι V) (i k : ι) (o : Op V) (cv : View ι V) (got : Set ι)
      (hph : c.phase i = .bcast o cv got) (hk : k ∉ got) :
      Step prio c none
        { c with phase := Function.update c.phase i (.bcast o cv (insert k got)),
                 queue := Function.update c.queue k (c.queue k ++ [cv]) }
  /-- Lines 7–8: the handler of `k` processes the first queued message. -/
  | handle (c : Config ι V) (k : ι) (W : View ι V) (q : List (View ι V)) (halive : k ∉ c.crashed)
      (hq : c.queue k = W :: q) :
      Step prio c none
        { c with view := Function.update c.view k ((c.view k).merge W),
                 queue := Function.update c.queue k q }
  /-- The acknowledgment, once every non-crashed node has received the message. -/
  | ack (c : Config ι V) (i : ι) (o : Op V) (cv : View ι V) (got : Set ι) (halive : i ∉ c.crashed)
      (hph : c.phase i = .bcast o cv got) (hall : ∀ k, k ∉ c.crashed → k ∈ got) :
      Step prio c none { c with phase := Function.update c.phase i (.acked o cv) }
  /-- Lines 3 / 6: return. -/
  | ret (c : Config ι V) (i : ι) (o : Op V) (cv : View ι V) (halive : i ∉ c.crashed)
      (hph : c.phase i = .acked o cv) :
      Step prio c (some (.ret i (c.cnt i) (resp o cv)))
        { c with phase := Function.update c.phase i .idle,
                 cnt := Function.update c.cnt i (c.cnt i + 1) }
  /-- A crash. -/
  | crash (c : Config ι V) (i : ι) : Step prio c none { c with crashed := insert i c.crashed }

/-- Reachable configurations together with the history produced so far. -/
inductive Reach [DecidableEq ι] (prio : Bool) : Config ι V → History ι V → Prop
  | init : Reach prio Config.init []
  | step {c c' : Config ι V} {h : History ι V} {l : Option (Label ι V)} :
      Reach prio c h → Step prio c l c' → Reach prio c' (h ++ l.toList)

variable (ι V) in
/-- MAC-SC correctly implements the store-collect object (Definition 1): every execution
results in a history that satisfies regularity. -/
def ImplementsStoreCollect [DecidableEq ι] (prio : Bool) : Prop :=
  ∀ (c : Config ι V) (h : History ι V), Reach prio c h → Regular h

end Podc.AnonymousMACConsensus
