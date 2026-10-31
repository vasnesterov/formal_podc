import Papers.PODC2010.HindsightLinearizability.Heap
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Progress

/-!
# The optimistic set algorithm of Fig. 1 and the set specification of Fig. 2

The algorithm is an implementation (`Cslib.SharedMemory.Impl`) of the sequential set object
`setSpec` (Fig. 2) from a single base object, the heap `heapObj`, whose operations are the
primitive instructions and atomic sections of Fig. 1 that touch shared memory:

* `readH` (line 21 `p = H`),
* `readNext p` (lines 22/26 `c = p.n`, assumed atomic as in footnote 1 of the paper),
* `readKey c` (line 24 `c.k < k`),
* `addSec p c k` (the atomic section of `add`, lines 85–98),
* `removeSec p c k` (the atomic section of `remove`, lines 65–78).

Every invocation of a thread starts at line 21; a failed validation restarts it (`start`).
Nodes are natural numbers; a node is allocated iff it is `< cnt`, and `alloc(E)` returns the
fresh node `cnt` (memory is never reclaimed). The initialized state (Section 4: the state
produced by `init()`) has the tail node `0` (allocated first) and the head node `1`.

A null-pointer dereference sends the thread to the local state `err` (the paper's `σ_error`);
memory safety is the statement that `err` is never reached.

Keys are `Key = WithBot (WithTop ℤ)`: `⊥ = -∞`, `⊤ = ∞`, and the integers in between.
-/

namespace Podc.HindsightLinearizability

open Cslib.SharedMemory

/-- Keys: the integers extended with `-∞ = ⊥` and `∞ = ⊤`. -/
abbrev Key := WithBot (WithTop ℤ)

/-- The finite key `z`. -/
def fin (z : ℤ) : Key := ((z : WithTop ℤ) : WithBot (WithTop ℤ))

@[simp] lemma fin_lt_fin {a b : ℤ} : fin a < fin b ↔ a < b := by simp [fin]
@[simp] lemma fin_le_fin {a b : ℤ} : fin a ≤ fin b ↔ a ≤ b := by simp [fin]
@[simp] lemma fin_inj {a b : ℤ} : fin a = fin b ↔ a = b := by simp [fin]
@[simp] lemma bot_lt_fin (a : ℤ) : (⊥ : Key) < fin a := WithBot.bot_lt_coe _
@[simp] lemma fin_lt_top (a : ℤ) : fin a < (⊤ : Key) := by
  simp only [fin]; exact WithBot.coe_lt_coe.2 (WithTop.coe_lt_top a)
@[simp] lemma fin_ne_top (a : ℤ) : fin a ≠ (⊤ : Key) := (fin_lt_top a).ne
@[simp] lemma fin_ne_bot (a : ℤ) : fin a ≠ (⊥ : Key) := (bot_lt_fin a).ne'

/-! ### The heap -/

/-- The thread-shared state: the shared variables `H`, `T` and the heap of nodes of type `E`.
Nodes `u < cnt` are allocated. -/
structure Mem where
  /-- Number of allocated nodes; the allocated nodes are `0, …, cnt - 1`. -/
  cnt : ℕ
  /-- `n`-fields (`none` = `null`). -/
  next : ℕ → Option ℕ
  /-- `k`-fields. -/
  key : ℕ → Key
  /-- `m`-fields. -/
  mark : ℕ → Bool
  /-- The shared variable `H`. -/
  H : ℕ
  /-- The shared variable `T`. -/
  T : ℕ

/-- The heap state (in the sense of `HeapState`) of a memory. -/
def Mem.hs (m : Mem) : HeapState ℕ Key :=
  ⟨{u | u < m.cnt}, m.next, m.key, m.mark, m.H, m.T⟩

@[simp] lemma Mem.hs_alloc (m : Mem) : m.hs.alloc = {u | u < m.cnt} := rfl
@[simp] lemma Mem.hs_next (m : Mem) : m.hs.next = m.next := rfl
@[simp] lemma Mem.hs_key (m : Mem) : m.hs.key = m.key := rfl
@[simp] lemma Mem.hs_mark (m : Mem) : m.hs.mark = m.mark := rfl
@[simp] lemma Mem.hs_H (m : Mem) : m.hs.H = m.H := rfl
@[simp] lemma Mem.hs_T (m : Mem) : m.hs.T = m.T := rfl

/-- The initialized state produced by `init()` (lines 0–11): `T = 0` (key `∞`, no successor),
`H = 1` (key `-∞`, successor `T`). -/
def initMem : Mem where
  cnt := 2
  next u := if u = 1 then some 0 else none
  key u := if u = 0 then ⊤ else ⊥
  mark _ := false
  H := 1
  T := 0

/-- `alloc(E)` followed by the initialization of the new node `t = cnt` with mark `false`,
key `k` and successor `c` (lines 89–92), and `p.n = t` (line 93). -/
def Mem.insertAfter (m : Mem) (p c : ℕ) (k : ℤ) : Mem where
  cnt := m.cnt + 1
  next := Function.update (Function.update m.next m.cnt (some c)) p (some m.cnt)
  key := Function.update m.key m.cnt (fin k)
  mark := Function.update m.mark m.cnt false
  H := m.H
  T := m.T

/-- `c.m = true; p.n = c.n` (lines 70–73). -/
def Mem.unlink (m : Mem) (p c : ℕ) : Mem where
  cnt := m.cnt
  next := Function.update m.next p (m.next c)
  key := m.key
  mark := Function.update m.mark c true
  H := m.H
  T := m.T

/-- Operations on the heap: the shared-memory accesses of Fig. 1. -/
inductive HOp where
  /-- Read the shared variable `H` (line 21). -/
  | readH
  /-- `c = p.n` (lines 22, 26). -/
  | readNext (p : ℕ)
  /-- Read `c.k` (line 24). -/
  | readKey (c : ℕ)
  /-- The atomic section of `add(k)` (lines 85–98). -/
  | addSec (p c : ℕ) (k : ℤ)
  /-- The atomic section of `remove(k)` (lines 65–78). -/
  | removeSec (p c : ℕ) (k : ℤ)

/-- Responses of heap operations. -/
inductive HResp where
  /-- A pointer value (`none` = `null`). -/
  | ptr (o : Option ℕ)
  /-- A key. -/
  | key (k : Key)
  /-- Outcome of an atomic section: `none` = the validation failed (restart), `some b` = the
  validation succeeded and `retval = b`. -/
  | sec (r : Option Bool)

/-- The effect of a heap operation. -/
def heapδ (m : Mem) : HOp → Mem × HResp
  | .readH => (m, .ptr (some m.H))
  | .readNext p => (m, .ptr (m.next p))
  | .readKey c => (m, .key (m.key c))
  | .addSec p c k =>
    if m.next p = some c ∧ m.mark p = false then
      if m.key c ≠ fin k then (m.insertAfter p c k, .sec (some true))
      else (m, .sec (some false))
    else (m, .sec none)
  | .removeSec p c k =>
    if m.next p = some c ∧ m.mark p = false then
      if m.key c = fin k then (m.unlink p c, .sec (some true))
      else (m, .sec (some false))
    else (m, .sec none)

/-- The heap as a (single) base object. -/
def heapObj : ObjSpec where
  State := Mem
  Op := HOp
  Resp := HResp
  init := initMem
  δ := heapδ

/-! ### The sequential specification of a set (Fig. 2) -/

/-- Operations of the set. -/
inductive SetOp where
  | add (k : ℤ)
  | remove (k : ℤ)
  | contains (k : ℤ)
  deriving DecidableEq

/-- The key argument of an operation. -/
def SetOp.key : SetOp → ℤ
  | .add k => k
  | .remove k => k
  | .contains k => k

open Classical in
/-- Fig. 2: the sequential specification of a set of integers, initially empty. -/
noncomputable def setSpec : ObjSpec where
  State := Set ℤ
  Op := SetOp
  Resp := Bool
  init := ∅
  δ S
    | .add k => (insert k S, decide (k ∉ S))
    | .remove k => (S \ {k}, decide (k ∈ S))
    | .contains k => (S, decide (k ∈ S))

/-! ### The threads -/

/-- Local states (program counter and local variables) of a thread. -/
inductive Loc where
  /-- No pending operation. -/
  | idle
  /-- Line 21: `p = H` (start or restart of `locate`). -/
  | start (o : SetOp)
  /-- Lines 22/26: `c = p.n`. -/
  | cross (o : SetOp) (p : ℕ)
  /-- Line 24: test `c.k < k`. -/
  | test (o : SetOp) (p c : ℕ)
  /-- The atomic section of `add` / `remove`. -/
  | sec (o : SetOp) (p c : ℕ)
  /-- About to return `b`. -/
  | done (b : Bool)
  /-- A null pointer was dereferenced (`σ_error`). -/
  | err

/-- The heap operation of the atomic section of `o`. -/
def secOp (o : SetOp) (p c : ℕ) : HOp :=
  match o with
  | .add k => .addSec p c k
  | .remove k => .removeSec p c k
  | .contains _ => .readH

/-- Continuation after reading `c.k = kc` at line 24: continue the traversal, or leave
`locate` (lines 42–43 for `contains`, which compares the key just read; the atomic section
for `add`/`remove`). -/
def afterKey (o : SetOp) (p c : ℕ) (kc : Key) : Loc :=
  if kc < fin o.key then .cross o c
  else match o with
    | .contains k => .done (decide (kc = fin k))
    | _ => .sec o p c

/-- The program of Fig. 1, one step per shared-memory access. -/
def act (l : Loc) : Action setSpec (fun _ : Unit => heapObj) Loc :=
  match l with
  | .start o => .access () HOp.readH (fun r => match r with
      | .ptr (some h) => .cross o h
      | _ => .err)
  | .cross o p => .access () (HOp.readNext p) (fun r => match r with
      | .ptr (some c) => .test o p c
      | _ => .err)
  | .test o p c => .access () (HOp.readKey c) (fun r => match r with
      | .key kc => afterKey o p c kc
      | _ => .err)
  | .sec o p c => .access () (secOp o p c) (fun r => match r with
      | .sec none => .start o
      | .sec (some b) => .done b
      | _ => .err)
  | .done b => .ret b .idle
  | .idle => .ret false .idle
  | .err => .access () HOp.readH (fun _ => .err)

/-- The concurrent set of Fig. 1 for threads `P`. -/
noncomputable def impl (P : Type) : Impl setSpec (fun _ : Unit => heapObj) P Loc where
  memInit _ := initMem
  locInit _ := .idle
  invoke _ _ o := .start o
  act _ l := act l

/-- The abstraction function of Section 7.2: `Abs(σ) = K_σ \ {-∞, ∞}`, the integer keys of the
backbone nodes. -/
def Abs (m : Mem) : Set ℤ := {z | fin z ∈ m.hs.backboneKeys}

end Podc.HindsightLinearizability
