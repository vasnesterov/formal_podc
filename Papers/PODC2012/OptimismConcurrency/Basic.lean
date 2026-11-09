import Mathlib
import Cslib.Computability.Distributed.SharedMemory.HerlihyWing.Locality

/-!
# Two-level histories, LS-linearizability, schedules

Gramoli, Kuznetsov, Ravi, *Optimism for Boosting Concurrency* (arXiv 1203.4751v8; PODC 2012
brief announcement "From Sequential to Concurrent: Correctness and Relative Efficiency"),
Sections 2–4.

A history of a concurrent implementation of a sequential implementation `IS` has two levels:
high-level operations (`inv`/`res`) of the implemented type and, inside them, the reads and
writes of the base objects ("t-objects") of `IS` (`rinv`/`rres`, `winv`/`wres`). A read or a write
may abort: its response is `⊥` (`rres p x none`, `wres p x false`), and then the enclosing
high-level operation is aborted (the `⊥` event is also its response, §2).

* `Ev`, `Hist`: events and histories (every event carries the process and the high-level object).
* `localView H p x k` = `H|π` for the `k`-th operation `π` of `p` on `x`, without its last
  aborted read or write (§3).
* `LocSer SigIS H` (local serializability w.r.t. the set `Σ` of histories of `IS`), `hl H` (the
  high-level history `H̃`: invocations and responses of non-aborted operations), `LSL SigIS spec H`
  (**Definition 1**, LS-linearizability, with Herlihy–Wing linearizability from CSLib).
* `complete H` (events of the operations that returned a matching response), schedules `SEv`,
  `sched`, `Exports`, `Accepts` (§4).

Histories are only meaningful when well-formed; as in the paper, the definitions are applied to
the histories produced by implementations, which are well-formed.
-/

namespace Podc.OptimismConcurrency

/-- Events of a two-level history. `x` is the high-level object, `y` a base object of the
sequential implementation, `v` a value of a base object. -/
inductive Ev (P X Op Res Obj Val : Type) where
  /-- `p` invokes the high-level operation `o` on `x`. -/
  | inv (p : P) (x : X) (o : Op)
  /-- `p` receives the (matching) response `r` from `x`. -/
  | res (p : P) (x : X) (r : Res)
  /-- `p` invokes `read(y)` (inside its operation on `x`). -/
  | rinv (p : P) (x : X) (y : Obj)
  /-- The read of `p` returns `v`; `none` is `⊥` (the read, and the operation, abort). -/
  | rres (p : P) (x : X) (v : Option Val)
  /-- `p` invokes `write(y, v)`. -/
  | winv (p : P) (x : X) (y : Obj) (v : Val)
  /-- The write of `p` returns `ok` (`true`) or `⊥` (`false`: the write and the operation abort). -/
  | wres (p : P) (x : X) (ok : Bool)
  deriving DecidableEq

/-- Histories. -/
abbrev Hist (P X Op Res Obj Val : Type) := List (Ev P X Op Res Obj Val)

variable {P X Op Res Obj Val : Type}

namespace Ev

/-- The process of an event. -/
def proc : Ev P X Op Res Obj Val → P
  | inv p .. | res p .. | rinv p .. | rres p .. | winv p .. | wres p .. => p

/-- The high-level object of an event. -/
def obj : Ev P X Op Res Obj Val → X
  | inv _ x _ | res _ x _ | rinv _ x _ | rres _ x _ | winv _ x _ _ | wres _ x _ => x

/-- High-level invocation. -/
def isInv : Ev P X Op Res Obj Val → Bool
  | inv .. => true
  | _ => false

/-- An abort (`⊥` response of a read or a write). -/
def isAbort : Ev P X Op Res Obj Val → Bool
  | rres _ _ none => true
  | wres _ _ false => true
  | _ => false

/-- A high-level response. -/
def isRes : Ev P X Op Res Obj Val → Bool
  | res .. => true
  | _ => false

/-- Terminal event of an operation: its response or an abort. -/
def isTerm (e : Ev P X Op Res Obj Val) : Bool := e.isRes || e.isAbort

@[simp] lemma proc_inv (p : P) (x : X) (o : Op) :
    (inv p x o : Ev P X Op Res Obj Val).proc = p := rfl
@[simp] lemma proc_res (p : P) (x : X) (r : Res) :
    (res p x r : Ev P X Op Res Obj Val).proc = p := rfl
@[simp] lemma proc_rinv (p : P) (x : X) (y : Obj) :
    (rinv p x y : Ev P X Op Res Obj Val).proc = p := rfl
@[simp] lemma proc_rres (p : P) (x : X) (v : Option Val) :
    (rres p x v : Ev P X Op Res Obj Val).proc = p := rfl
@[simp] lemma proc_winv (p : P) (x : X) (y : Obj) (v : Val) :
    (winv p x y v : Ev P X Op Res Obj Val).proc = p := rfl
@[simp] lemma proc_wres (p : P) (x : X) (b : Bool) :
    (wres p x b : Ev P X Op Res Obj Val).proc = p := rfl
@[simp] lemma obj_inv (p : P) (x : X) (o : Op) :
    (inv p x o : Ev P X Op Res Obj Val).obj = x := rfl
@[simp] lemma obj_res (p : P) (x : X) (r : Res) :
    (res p x r : Ev P X Op Res Obj Val).obj = x := rfl
@[simp] lemma obj_rinv (p : P) (x : X) (y : Obj) :
    (rinv p x y : Ev P X Op Res Obj Val).obj = x := rfl
@[simp] lemma obj_rres (p : P) (x : X) (v : Option Val) :
    (rres p x v : Ev P X Op Res Obj Val).obj = x := rfl
@[simp] lemma obj_winv (p : P) (x : X) (y : Obj) (v : Val) :
    (winv p x y v : Ev P X Op Res Obj Val).obj = x := rfl
@[simp] lemma obj_wres (p : P) (x : X) (b : Bool) :
    (wres p x b : Ev P X Op Res Obj Val).obj = x := rfl

end Ev

variable [DecidableEq P] [DecidableEq X]

/-! ## Operations of a history -/

/-- Events of `p` on `x`. -/
def restrictPX (H : Hist P X Op Res Obj Val) (p : P) (x : X) : Hist P X Op Res Obj Val :=
  H.filter (fun e => decide (e.proc = p) && decide (e.obj = x))

/-- The terminal event (response or abort) of the operation of `p` on `x` that is running at
the start of `l` (the first terminal event of `p` on `x` in `l`). -/
def termOf (p : P) (x : X) (l : Hist P X Op Res Obj Val) : Option (Ev P X Op Res Obj Val) :=
  l.find? (fun e => decide (e.proc = p) && decide (e.obj = x) && e.isTerm)

/-- Filter with look-ahead: keep `e` iff `f e later` where `later` is the rest of the history. -/
def lookFilter {α : Type*} (f : α → List α → Bool) : List α → List α
  | [] => []
  | e :: l => if f e l then e :: lookFilter f l else lookFilter f l

/-- Split the events of one process on one object into its operations: each segment starts at a
high-level invocation (events before the first invocation are dropped). -/
def splitOps (l : Hist P X Op Res Obj Val) : List (Hist P X Op Res Obj Val) :=
  (l.foldr (fun e (acc : Hist P X Op Res Obj Val × List (Hist P X Op Res Obj Val)) =>
    if e.isInv then ([], (e :: acc.1) :: acc.2) else (e :: acc.1, acc.2)) ([], [])).2

/-- Remove the last aborted read or write (its invocation and its `⊥` response), if any. -/
def dropAbort (l : Hist P X Op Res Obj Val) : Hist P X Op Res Obj Val :=
  if l.getLast?.any Ev.isAbort then l.dropLast.dropLast else l

/-- `H|π` for the `k`-th operation `π` of `p` on `x` (§3): its events, except for the last
aborted read or write. -/
def localView (H : Hist P X Op Res Obj Val) (p : P) (x : X) (k : ℕ) : Hist P X Op Res Obj Val :=
  dropAbort ((splitOps (restrictPX H p x)).getD k [])

/-- Number of operations of `p` on `x` invoked in `H`. -/
def numOps (H : Hist P X Op Res Obj Val) (p : P) (x : X) : ℕ :=
  (splitOps (restrictPX H p x)).length

/-! ## LS-linearizability (Definition 1) -/

/-- **Local serializability** w.r.t. the set `Σ` of histories of the sequential implementation:
for every operation `π` of `H` there is `S ∈ Σ` with `H|π = S|π`. Since histories of a
sequential implementation are sequential and prefix-closed, we take `S` ending with `π`. -/
def LocSer (SigIS : Set (Hist P X Op Res Obj Val)) (H : Hist P X Op Res Obj Val) : Prop :=
  ∀ p x k, k < numOps H p x → ∃ S₀, S₀ ++ localView H p x k ∈ SigIS

/-- Keep a high-level invocation unless its operation aborted; keep every high-level response. -/
def keepHL (e : Ev P X Op Res Obj Val) (later : Hist P X Op Res Obj Val) : Bool :=
  match e with
  | .inv p x _ => !((termOf p x later).any Ev.isAbort)
  | .res .. => true
  | _ => false

/-- High-level events as Herlihy–Wing events. -/
def toHW : Ev P X Op Res Obj Val → Option (Cslib.SharedMemory.HerlihyWing.Event P X Op Res)
  | .inv p x o => some (.inv p x o)
  | .res p x r => some (.res p x r)
  | _ => none

/-- The high-level history `H̃` of `H`: invocations and responses of the non-aborted
operations. -/
def hl (H : Hist P X Op Res Obj Val) : Cslib.SharedMemory.HerlihyWing.History P X Op Res :=
  (lookFilter keepHL H).filterMap toHW

/-- **Definition 1** (LS-linearizability): `H` is locally serializable w.r.t. `Σ` (the
histories of `IS`) and its high-level history is linearizable w.r.t. `spec` (the type `τ`). -/
def LSL (SigIS : Set (Hist P X Op Res Obj Val))
    (spec : Cslib.SharedMemory.HerlihyWing.SeqSpec P X Op Res) (H : Hist P X Op Res Obj Val) :
    Prop :=
  LocSer SigIS H ∧ Cslib.SharedMemory.HerlihyWing.Linearizable spec (hl H)

/-! ## Schedules and acceptance (§4) -/

/-- Keep the events of the operations that returned a matching response. -/
def keepC (e : Ev P X Op Res Obj Val) (later : Hist P X Op Res Obj Val) : Bool :=
  (termOf e.proc e.obj (e :: later)).any Ev.isRes

/-- `complete(H)`: the events of the complete operations that returned a matching response. -/
def complete (H : Hist P X Op Res Obj Val) : Hist P X Op Res Obj Val := lookFilter keepC H

/-- Schedule events: events without read values and high-level responses. -/
inductive SEv (P X Op Obj Val : Type) where
  | inv (p : P) (x : X) (o : Op)
  | res (p : P) (x : X)
  | rinv (p : P) (x : X) (y : Obj)
  | rres (p : P) (x : X)
  | winv (p : P) (x : X) (y : Obj) (v : Val)
  | wres (p : P) (x : X)
  deriving DecidableEq

/-- Forget values (read values, high-level responses, success flags). -/
def Ev.erase : Ev P X Op Res Obj Val → SEv P X Op Obj Val
  | .inv p x o => .inv p x o
  | .res p x _ => .res p x
  | .rinv p x y => .rinv p x y
  | .rres p x _ => .rres p x
  | .winv p x y v => .winv p x y v
  | .wres p x _ => .wres p x

/-- The schedule exhibited by `complete(H)`. -/
def sched (H : Hist P X Op Res Obj Val) : List (SEv P X Op Obj Val) := (complete H).map Ev.erase

/-- `H` exports the schedule `σ`: `complete(H)` exhibits the order of `σ`. -/
def Exports (H : Hist P X Op Res Obj Val) (σ : List (SEv P X Op Obj Val)) : Prop := sched H = σ

/-- An implementation, given by the set of histories it exports, accepts `σ`. -/
def Accepts (I : Set (Hist P X Op Res Obj Val)) (σ : List (SEv P X Op Obj Val)) : Prop :=
  ∃ H ∈ I, Exports H σ

/-- `σ` is an `(IS, τ)`-LSL schedule: some LSL history exports it. -/
def LSLSched (SigIS : Set (Hist P X Op Res Obj Val))
    (spec : Cslib.SharedMemory.HerlihyWing.SeqSpec P X Op Res)
    (σ : List (SEv P X Op Obj Val)) : Prop :=
  ∃ H, LSL SigIS spec H ∧ Exports H σ

end Podc.OptimismConcurrency
