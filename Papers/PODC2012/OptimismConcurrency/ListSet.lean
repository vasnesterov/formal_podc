import Papers.PODC2012.OptimismConcurrency.Basic
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Bridge

/-!
# The list-based set `(LL, set)` (§2, Appendix A)

* `setObj`: the type *set* (`insert`, `remove`, `contains` on finite sets of integers), as a
  deterministic CSLib object; `specSet` is its Herlihy–Wing sequential specification.
* Nodes: base objects are locations `Loc = ℕ` (`head = 0`, `tail = 1`); a node stores a key
  (`-∞`, an integer, or `+∞`) and the location of its successor (`NodeV`).
* `LL` (Algorithm 2) as a program: `St` (control state), `act` (next read/write/return),
  `onRead`, `onWrite` (effect of a response). `new-node(v, prev.next)` is modelled as a write of
  the new node to a *fresh* (never allocated) location (action `alloc`), followed by the write
  linking it.
* `seqStep`, `SigLL`: the histories of `LL` (Σ_LL), i.e. the sequential executions of `LL` from
  the empty list (`head → tail`), where reads return the current memory, possibly ending in the
  middle of an operation.
* `honStep`, `Honest`: a history is *honest* if every read returns the value of the latest write
  to the object (a write takes effect at its `ok` response); this is the strongest reasonable
  "memory" constraint and is not required by the paper (§2 only asks for obedience).
-/

namespace Podc.OptimismConcurrency

open Cslib.SharedMemory

/-- Locations of nodes (the base objects of `LL`). -/
abbrev Loc := ℕ

/-- The head sentinel. -/
def headL : Loc := 0
/-- The tail sentinel. -/
def tailL : Loc := 1

/-- Keys: `-∞`, an integer, `+∞`. -/
inductive Key | ninf | fin (z : ℤ) | pinf
  deriving DecidableEq, Repr

/-- `k < v` for a key `k` and an integer `v`. -/
def Key.ltZ : Key → ℤ → Bool
  | .ninf, _ => true
  | .fin z, v => decide (z < v)
  | .pinf, _ => false

/-- A node: its value (`val`) and the location of its successor (`next`). -/
structure NodeV where
  key : Key
  next : Loc
  deriving DecidableEq, Repr

/-- Operations of the type *set*. -/
inductive SetOp | insert (v : ℤ) | remove (v : ℤ) | contains (v : ℤ)
  deriving DecidableEq, Repr

/-- The argument of an operation. -/
def SetOp.arg : SetOp → ℤ
  | .insert v | .remove v | .contains v => v

/-- The type *set* (Appendix A): states are finite sets of integers, initially empty. -/
def setδ : Finset ℤ → SetOp → Finset ℤ × Bool
  | q, .contains v => (q, decide (v ∈ q))
  | q, .insert v => (insert v q, decide (v ∉ q))
  | q, .remove v => (q.erase v, decide (v ∈ q))

/-- The type *set* as a deterministic object. -/
def setObj : ObjSpec where
  State := Finset ℤ
  Op := SetOp
  Resp := Bool
  init := ∅
  δ := setδ

/-- Sequential specification of *set* (Herlihy–Wing form). -/
abbrev specSet (P : Type) : HerlihyWing.SeqSpec P Unit SetOp Bool :=
  HerlihyWing.specOf (P := P) setObj

/-- Histories of the list-based set. -/
abbrev LHist (P : Type) := Hist P Unit SetOp Bool Loc NodeV
/-- Events of the list-based set. -/
abbrev LEv (P : Type) := Ev P Unit SetOp Bool Loc NodeV
/-- Schedules of the list-based set. -/
abbrev LSched (P : Type) := List (SEv P Unit SetOp Loc NodeV)

/-! ## Algorithm 2 (`LL`) as a program -/

/-- Control state of an operation of `LL`. `old` is the location of `prev`. -/
inductive St
  /-- before `prev ← read(head)` -/
  | start
  /-- traversing: next is `curr ← read(prev.next)` -/
  | trav (old : Loc) (prev : NodeV)
  /-- `insert`: next is `X ← new-node(n)` (write of `n` to a fresh location) -/
  | alloc (old : Loc) (prev : NodeV) (n : NodeV)
  /-- next is `write(old, n)`, then return `r` -/
  | wr (old : Loc) (n : NodeV) (r : Bool)
  /-- next is `return r` -/
  | done (r : Bool)
  deriving DecidableEq, Repr

/-- Next action of `LL`. -/
inductive Act
  | read (y : Loc)
  | write (y : Loc) (n : NodeV)
  /-- write `n` to a fresh location -/
  | alloc (n : NodeV)
  | ret (r : Bool)
  deriving DecidableEq, Repr

/-- The next action of the operation `o` in control state `s`. -/
def act (_o : SetOp) : St → Act
  | .start => .read headL
  | .trav _ prev => .read prev.next
  | .alloc _ _ n => .alloc n
  | .wr old n _ => .write old n
  | .done r => .ret r

/-- End of the traversal: `curr.val ≥ v` (lines 13–16, 25–27, 34 of Algorithm 2). -/
def finish : SetOp → Loc → NodeV → NodeV → St
  | .contains v, _, _, curr => .done (decide (curr.key = .fin v))
  | .insert v, old, prev, curr =>
      if curr.key = .fin v then .done false else .alloc old prev ⟨.fin v, prev.next⟩
  | .remove v, old, prev, curr =>
      if curr.key = .fin v then .wr old ⟨prev.key, curr.next⟩ true else .done false

/-- Effect of a read of `y` returning `n`. -/
def onRead (o : SetOp) : St → Loc → NodeV → St
  | .start, _, n => .trav headL n
  | .trav old prev, y, curr =>
      if curr.key.ltZ o.arg then .trav y curr else finish o old prev curr
  | s, _, _ => s

/-- Effect of the completion of a write to `y`. -/
def onWrite : St → Loc → St
  | .alloc old prev _, y => .wr old ⟨prev.key, y⟩ true
  | .wr _ _ r, _ => .done r
  | s, _ => s

/-! ## Memory -/

/-- Memory: the content of every allocated location. -/
abbrev Mem := Loc → Option NodeV

/-- Initial memory: the empty list `head → tail`. -/
def mem0 : Mem := fun l =>
  if l = headL then some ⟨.ninf, tailL⟩ else if l = tailL then some ⟨.pinf, tailL⟩ else none

/-- A pending read or write. -/
inductive Pend
  | rd (y : Loc)
  | wr (y : Loc) (n : NodeV)
  deriving DecidableEq, Repr

/-! ## Sequential histories of `LL` (Σ_LL) -/

/-- Configuration of a sequential execution of `LL`. -/
structure SCfg (P : Type) where
  mem : Mem
  /-- the operation in progress: process, operation, control state -/
  cur : Option (P × SetOp × St)
  pend : Option Pend

/-- Initial configuration. -/
def scfg0 {P : Type} : SCfg P := ⟨mem0, none, none⟩

variable {P : Type} [DecidableEq P]

/-- One event of a sequential execution of `LL` (reads return the current memory, writes take
effect at their response, operations run one at a time). -/
def seqStep (c : SCfg P) : LEv P → Option (SCfg P)
  | .inv p _ o => match c.cur with
    | none => some { c with cur := some (p, o, .start) }
    | some _ => none
  | .rinv p _ y => match c.cur, c.pend with
    | some (q, o, s), none => if q = p ∧ act o s = .read y then some { c with pend := some (.rd y) }
        else none
    | _, _ => none
  | .rres p _ v => match c.cur, c.pend with
    | some (q, o, s), some (.rd y) =>
        if q = p ∧ v = c.mem y ∧ v.isSome then
          some { c with cur := some (q, o, onRead o s y (v.getD ⟨.ninf, 0⟩)), pend := none }
        else none
    | _, _ => none
  | .winv p _ y n => match c.cur, c.pend with
    | some (q, o, s), none =>
        if q = p ∧ (act o s = .write y n ∨ (act o s = .alloc n ∧ c.mem y = none)) then
          some { c with pend := some (.wr y n) }
        else none
    | _, _ => none
  | .wres p _ ok => match c.cur, c.pend with
    | some (q, o, s), some (.wr y n) =>
        if q = p ∧ ok = true then
          some ⟨Function.update c.mem y (some n), some (q, o, onWrite s y), none⟩
        else none
    | _, _ => none
  | .res p _ r => match c.cur, c.pend with
    | some (q, o, s), none => if q = p ∧ act o s = .ret r then some { c with cur := none }
        else none
    | _, _ => none

/-- Run `seqStep` along a history. -/
def seqRun (c : SCfg P) : LHist P → Option (SCfg P)
  | [] => some c
  | e :: l => (seqStep c e).bind (fun c' => seqRun c' l)

/-- **Σ_LL**: the histories of the sequential implementation `LL` (sequential executions from
the empty list, possibly ending in the middle of an operation). -/
def SigLL : Set (LHist P) := {S | (seqRun scfg0 S).isSome}

instance (S : LHist P) : Decidable (S ∈ (SigLL : Set (LHist P))) :=
  inferInstanceAs (Decidable ((seqRun scfg0 S).isSome = true))

/-! ## Honest histories -/

/-- Configuration for checking honesty: memory and the pending read/write of every process. -/
structure HCfg (P : Type) where
  mem : Mem
  pend : P → Option Pend

/-- Initial honesty configuration. -/
def hcfg0 : HCfg P := ⟨mem0, fun _ => none⟩

/-- One event: reads must return the current content, writes take effect at their `ok`. Aborted
reads and writes have no effect. High-level events are ignored. -/
def honStep (c : HCfg P) : LEv P → Option (HCfg P)
  | .rinv p _ y => some { c with pend := Function.update c.pend p (some (.rd y)) }
  | .winv p _ y n => some { c with pend := Function.update c.pend p (some (.wr y n)) }
  | .rres p _ v => match c.pend p with
    | some (.rd y) =>
        if v.isNone ∨ v = c.mem y then some { c with pend := Function.update c.pend p none }
        else none
    | _ => none
  | .wres p _ ok => match c.pend p with
    | some (.wr y n) =>
        some ⟨if ok then Function.update c.mem y (some n) else c.mem,
          Function.update c.pend p none⟩
    | _ => none
  | _ => some c

/-- Run `honStep` along a history. -/
def honRun (c : HCfg P) : LHist P → Option (HCfg P)
  | [] => some c
  | e :: l => (honStep c e).bind (fun c' => honRun c' l)

/-- `H` is honest: every successful read returns the latest value written to the object (the
memory starts as the empty list). -/
def Honest (H : LHist P) : Prop := (honRun hcfg0 H).isSome

instance (H : LHist P) : Decidable (Honest H) :=
  inferInstanceAs (Decidable ((honRun hcfg0 H).isSome = true))

/-- LS-linearizability of histories of the list-based set w.r.t. `(LL, set)`. -/
abbrev LSL_LL (H : LHist P) : Prop := LSL SigLL (specSet P) H

end Podc.OptimismConcurrency
