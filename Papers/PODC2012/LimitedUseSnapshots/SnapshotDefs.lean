import Papers.PODC2012.LimitedUseSnapshots.Spec
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.StrongLin
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.Pi
import Mathlib.Algebra.Group.Pi.Basic

/-!
# Section 4 of Aspnes–Attiya–Censor-Hillel–Ellen: single-writer snapshots from max arrays

Aspnes, Attiya, Censor-Hillel, Ellen, *Limited-Use Atomic Snapshots with Polylogarithmic Step
Complexity* (PODC 2012 / J. ACM 62(1), 2015), Section 4, **Algorithm 3**: a single-writer snapshot
object built from 2-component max arrays (one per internal node of a binary tree whose leaves are
the processes), registers (the `view` arrays) and a max register at the root.

## Model

* Asynchronous shared memory, deterministic processes, no failures needed for safety (the model
  of CSLib, `Cslib.SharedMemory.Impl`; crashed processes are processes that stop taking steps).
* **Base objects are atomic**: the paper uses `MaxArray` as a black box (its linearizable
  implementation is Section 3), so every max array `u.ma` is one atomic `maxArrObj` (with
  unbounded components), `root.mr` is one atomic `maxRegObj` and every entry `u.view[k]` is one
  atomic register. The arrays are unbounded families indexed by `ℕ`; the bound `b` of the paper
  is recovered by `Snapshot.indices_le_updates` (all indices are at most the number of invoked
  `Update`s).
* The tree is an arbitrary binary tree `T : BTree P` whose leaves are exactly the processes
  (each once). Nodes are addressed by *reversed* paths `a : List Bool` (`[]` = root, `b :: a` =
  child `b` of node `a`, `false` = left). The paper's strict balanced tree is one instance
  (depth `⌈log₂ n⌉`, see `SnapshotCost.lean`).
* A partial snapshot (the content of `u.view[k]`) is represented by a full vector `P → V`, of which
  only the components of the leaves below `u` are meaningful; concatenation `lview · rview` is
  "take the components of left leaves from `lview`, the others from `rview`" (`concat`). A leaf
  stores the value `v` as the constant vector `fun _ => v`. All view registers initially hold the
  initial vector `v₀`, so `u.view[0]` is the concatenation of the initial values.
* `count_i` is the persistent local counter of the paper. The local assignment
  `count_i ← count_i + 1` (Line 2) is performed together with the leaf write (Line 5) instead of
  at invocation; since `count_i` is local, this is invisible to other processes.
* The single-writer discipline (`Update(s, i, v)` only by process `i`) is `Impl.allowed`.
-/

namespace Podc.LimitedUseSnapshots.Snapshot

open Cslib.SharedMemory

/-! ### Binary trees with processes at the leaves -/

/-- A binary tree with processes at the leaves. -/
inductive BTree (P : Type) where
  | leaf (p : P)
  | node (l r : BTree P)
  deriving DecidableEq

namespace BTree

variable {P : Type}

/-- The leaves of a tree, from left to right. -/
def leaves : BTree P → List P
  | leaf p => [p]
  | node l r => l.leaves ++ r.leaves

/-- Child `b` of a node (`false` = left). -/
def child : BTree P → Bool → Option (BTree P)
  | leaf _, _ => none
  | node l _, false => some l
  | node _ r, true => some r

/-- The subtree at the reversed address `a` (`[]` = the tree itself, `b :: a` = child `b` of the
subtree at `a`). -/
def sub (t : BTree P) : List Bool → Option (BTree P)
  | [] => some t
  | b :: a => (t.sub a).bind (fun u => u.child b)

/-- The (reversed) address of the leaf of process `j`. -/
def path [DecidableEq P] : BTree P → P → List Bool
  | leaf _, _ => []
  | node l r, j => if j ∈ l.leaves then l.path j ++ [false] else r.path j ++ [true]

/-- The depth of a tree. -/
def depth : BTree P → ℕ
  | leaf _ => 0
  | node l r => max l.depth r.depth + 1

/-- Well-formed trees for the process set `P`: every process is exactly one leaf. -/
structure WF (t : BTree P) : Prop where
  nodup : t.leaves.Nodup
  mem : ∀ p, p ∈ t.leaves

/-- The leaves below the node at address `a` (`[]` if there is no such node). -/
def leavesAt (t : BTree P) (a : List Bool) : List P := ((t.sub a).map leaves).getD []

end BTree

/-! ### The implemented object: a single-writer snapshot over arbitrary values -/

/-- Operations of a single-writer snapshot: `update i v` (only by process `i`) and `scan`. -/
inductive SOp (P V : Type) where
  | update (i : P) (v : V)
  | scan
  deriving DecidableEq

/-- Sequential specification of a snapshot object with one component per process `P`, values `V`
and initial vector `v₀`. `update` returns `none` (an acknowledgement), `scan` returns `some` of
the current vector. -/
abbrev swSnap (P V : Type) [DecidableEq P] (v₀ : P → V) : ObjSpec where
  State := P → V
  Op := SOp P V
  Resp := Option (P → V)
  init := v₀
  δ q
    | .update i v => (Function.update q i v, none)
    | .scan => (q, some q)

/-! ### Base objects -/

/-- Base objects of Algorithm 3: the max array `ma` of the node at address `a`, the max register
`root.mr`, and the register `view[k]` of the node at address `a`. -/
inductive Obj where
  | ma (a : List Bool)
  | mr
  | view (a : List Bool) (k : ℕ)
  deriving DecidableEq

/-- Specifications of the base objects. -/
abbrev objSpec (P V : Type) (v₀ : P → V) : Obj → ObjSpec
  | .ma _ => maxArrObj
  | .mr => maxRegObj
  | .view _ _ => register (P → V) v₀

/-! ### Local states -/

/-- Program counters of Algorithm 3 (local variables included). Every program counter performs
exactly one base-object access or returns.

* `lw v`: Line 5, write `v` into `leaf_i.view[count_i + 1]` (and increment `count_i`, Line 2);
* `up a ptr`: Lines 7–10, `MaxUpdate_b(u.parent.ma, ptr)` where `u` is the node at address
  `a = b :: p` (so `p` is the parent);
* `sc p`: Line 12, `MaxScan(ma)` at the node `p`;
* `rl p x y`, `rr p x y lv`: Lines 13–14, read the children's views;
* `wv p k val`: Line 16, write `val` into `view[k]` of node `p`;
* `wm d`: Line 18, `WriteMax(root.mr, d)`;
* `ackU`: return of `Update`;
* `s0`, `s1 c`, `retS val`: Lines 20–21 of `Scan`. -/
inductive PC (P V : Type) where
  | idle
  | lw (v : V)
  | up (a : List Bool) (ptr : ℕ)
  | sc (p : List Bool)
  | rl (p : List Bool) (x y : ℕ)
  | rr (p : List Bool) (x y : ℕ) (lv : P → V)
  | wv (p : List Bool) (k : ℕ) (val : P → V)
  | wm (d : ℕ)
  | ackU
  | s0
  | s1 (c : ℕ)
  | retS (val : P → V)

/-- Local state: the persistent counter `count_i` and the program counter. -/
structure Loc (P V : Type) where
  cnt : ℕ
  pc : PC P V

variable {P V : Type} [DecidableEq P]

/-- After writing `view[k]` of the node `a`: go up (`a ≠ root`) or write the root max register. -/
def cont (a : List Bool) (k : ℕ) : PC P V := if a = [] then .wm k else .up a k

/-- Concatenation of the partial snapshots of the two children of the node `p` (Line 16). -/
def concat (T : BTree P) (p : List Bool) (lv rv : P → V) : P → V :=
  fun j => if j ∈ T.leavesAt (false :: p) then lv j else rv j

/-- The next action of process `i` (Algorithm 3). -/
def act (T : BTree P) (v₀ : P → V) (i : P) (l : Loc P V) :
    Action (swSnap P V v₀) (objSpec P V v₀) (Loc P V) :=
  match l.pc with
  | .idle => .ret none l
  | .lw v => .access (.view (T.path i) (l.cnt + 1)) (RWOp.write (fun _ => v))
      (fun _ => ⟨l.cnt + 1, cont (T.path i) (l.cnt + 1)⟩)
  | .up [] ptr => .access .mr (MaxOp.writeMax ptr) (fun _ => ⟨l.cnt, .ackU⟩)
  | .up (b :: p) ptr => .access (.ma p) (if b then MAOp.upd1 ptr else MAOp.upd0 ptr)
      (fun _ => ⟨l.cnt, .sc p⟩)
  | .sc p => .access (.ma p) MAOp.scan (fun r => ⟨l.cnt, .rl p r.1 r.2⟩)
  | .rl p x y => .access (.view (false :: p) x) RWOp.read (fun lv => ⟨l.cnt, .rr p x y lv⟩)
  | .rr p x y lv => .access (.view (true :: p) y) RWOp.read
      (fun rv => ⟨l.cnt, .wv p (x + y) (concat T p lv rv)⟩)
  | .wv p k val => .access (.view p k) (RWOp.write val) (fun _ => ⟨l.cnt, cont p k⟩)
  | .wm d => .access .mr (MaxOp.writeMax d) (fun _ => ⟨l.cnt, .ackU⟩)
  | .ackU => .ret none ⟨l.cnt, .idle⟩
  | .s0 => .access .mr MaxOp.readMax (fun c => ⟨l.cnt, .s1 c⟩)
  | .s1 c => .access (.view [] c) RWOp.read (fun v => ⟨l.cnt, .retS v⟩)
  | .retS v => .ret (some v) ⟨l.cnt, .idle⟩

/-- Initial memory: max arrays `(0, 0)`, `root.mr = 0`, every view register holds `v₀`. -/
def memInit (v₀ : P → V) : (o : Obj) → (objSpec P V v₀ o).State
  | .ma _ => ((0, 0) : ℕ × ℕ)
  | .mr => (0 : ℕ)
  | .view _ _ => v₀

/-- Single-writer discipline: process `i` may only update component `i`. -/
def allowed (i : P) : SOp P V → Prop
  | .update j _ => j = i
  | .scan => True

instance (i : P) (o : SOp P V) : Decidable (allowed i o) := by
  cases o <;> unfold allowed <;> infer_instance

/-- **Algorithm 3** of the paper, for the tree `T` and initial vector `v₀`. -/
abbrev alg3 (T : BTree P) (v₀ : P → V) : Impl (swSnap P V v₀) (objSpec P V v₀) P (Loc P V) where
  memInit := memInit v₀
  locInit _ := ⟨0, .idle⟩
  invoke _ l o := match o with
    | .update _ v => ⟨l.cnt, .lw v⟩
    | .scan => ⟨l.cnt, .s0⟩
  act := act T v₀
  allowed := allowed

end Podc.LimitedUseSnapshots.Snapshot
