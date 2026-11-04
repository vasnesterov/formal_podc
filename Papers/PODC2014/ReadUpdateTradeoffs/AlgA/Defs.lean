import Mathlib
import Cslib.Computability.Distributed.SharedMemory.LinPoints
import Cslib.Computability.Distributed.SharedMemory.Potential
import Cslib.Computability.Distributed.SharedMemory.Objects.MaxRegister

/-!
# Algorithm A of Hendler–Khait (PODC 2014, Section 5): the model

Algorithm A is a wait-free `N`-process max register from read/write/CAS base objects:

```
 1: function Read
 2:    return T.root.value
 3: procedure Propagate(n)
 4:    while n.parent ≠ nil do
 5:       n ← n.parent                      -- paper: `n ← node.parent` (typo)
 6:       for i = 1 to 2 do
 7:          old_value ← n.value
 8:          new_value ← max(n.left_child.value, n.right_child.value)
 9:          CAS(n.value, old_value, new_value)
10: procedure Write_i(value)
11:    if value < N then
12:       L ← T_L.leaves[value]
13:    else
14:       L ← T_R.leaves[i]
15:       old_value ← L.value
16:       if value ≤ old_value then return
17:    L.value ← value
18:    Propagate(L)
```

## Model

CSLib's asynchronous shared-memory model (`Cslib.SharedMemory.Impl`): `N` deterministic
processes `Fin N`, atomic base objects, executions as label lists, an arbitrary (adversarial)
interleaving, no failures other than processes stopping to take steps (which wait-freedom
covers). The high-level object is CSLib's `maxRegObj` (a max register over `ℕ`, initially `0`).

* **Values.** The paper's node values are integers initialised to `−∞` and the operands are
  naturals. We use `ℕ` with initial value `0`; since `maxRegObj` also starts at `0`, a
  `WriteMax(0)` is a no-op in the specification and `0` plays the role of `−∞`.
* **Tree.** The nodes are heap-indexed natural numbers: the root is `1`, the children of `n` are
  `2n` and `2n+1`, the parent of `n` is `n / 2`. Every natural number is a base object (a CAS
  object over `ℕ`, initially `0`); nodes outside the tree are never written and read as `0`,
  which is harmless for a max. The positions of the leaves are a parameter `Layout N`
  (`leaf (.inl v)` = the leaf of `T_L` for the value `v < N`, `leaf (.inr i)` = the leaf of `T_R`
  of process `i`); linearizability and wait-freedom hold for every layout in which the leaves are
  distinct positions `≥ 2` none of which is a proper ancestor of another. A concrete layout with
  `T_L` a `B₁`-like tree (leaf `v` at depth `2⌊log₂(v+1)⌋ + 2`) and `T_R` a complete tree is in
  `AlgA/Layout.lean`.
* **`T_L` has `N` leaves** (one for every `v < N`); the paper says `N − 1` leaves but indexes them
  by all `v < N`.
* Each line of the pseudo-code that accesses shared memory is one atomic step; line 8 is two
  reads (left child, then right child). The loop test of line 4 is local (`up`).
-/

namespace Podc.ReadUpdateTradeoffs.AlgA

open Cslib.SharedMemory

/-- Every node of the tree is a CAS object over `ℕ` (supporting `read`, `write` and `cas`). -/
abbrev Base : ℕ → ObjSpec := fun _ => casObject ℕ 0

/-- Positions of the leaves in the heap-indexed binary tree: `leaf (.inl v)` is the `v`-th leaf
of `T_L` (written by `WriteMax(v)` for `v < N`), `leaf (.inr i)` is the `i`-th leaf of `T_R`
(written by process `i` for operands `≥ N`). -/
structure Layout (N : ℕ) where
  /-- The position of a leaf. -/
  leaf : Fin N ⊕ Fin N → ℕ
  /-- Leaves are not the root (nor the unused position `0`). -/
  two_le : ∀ a, 2 ≤ leaf a
  /-- Distinct leaves have distinct positions. -/
  inj : Function.Injective leaf
  /-- No leaf is a proper ancestor of a leaf. -/
  not_anc : ∀ a b k, 0 < k → leaf a / 2 ^ k ≠ leaf b

/-- Local states (program counters) of Algorithm A. The node being worked on by `Propagate` is
`c / 2`, where `c` is the child of it on the path from the leaf (`j` = second iteration of the
`for` loop of line 6). -/
inductive Loc where
  /-- No pending operation. -/
  | idle
  /-- `ReadMax`: about to read the root (line 2). -/
  | rRoot
  /-- `ReadMax`: about to return `r`. -/
  | rDone (r : ℕ)
  /-- `WriteMax(v)`, `v ≥ N`: about to read the own leaf of `T_R` (line 15). -/
  | wRead (v : ℕ)
  /-- `WriteMax(v)`: about to write `v` to the leaf at position `x` (line 17). -/
  | wLeaf (v x : ℕ)
  /-- `Propagate`: about to read `n.value` for `n = c / 2` (line 7). -/
  | pOld (v c : ℕ) (j : Bool)
  /-- `Propagate`: about to read the left child of `n = c / 2` (line 8). -/
  | pL (v c : ℕ) (j : Bool) (old : ℕ)
  /-- `Propagate`: about to read the right child of `n = c / 2` (line 8). -/
  | pR (v c : ℕ) (j : Bool) (old l : ℕ)
  /-- `Propagate`: about to apply `CAS(n.value, old, max l r)` for `n = c / 2` (line 9). -/
  | pCas (v c : ℕ) (j : Bool) (old l r : ℕ)
  /-- `WriteMax`: about to return. -/
  | wDone
  deriving DecidableEq

/-- The value carried by a response of a CAS object (`read` returns `inl v`). -/
def val : ℕ ⊕ Bool → ℕ
  | .inl x => x
  | .inr _ => 0

@[simp] lemma val_inl (x : ℕ) : val (.inl x) = x := rfl

/-- The loop test of line 4 after finishing node `n` (or the leaf `n`): stop at the root,
otherwise continue with its parent. -/
def up (v n : ℕ) : Loc := if n ≤ 1 then .wDone else .pOld v n false

variable {N : ℕ}

/-- The leaf written by `WriteMax(v)` of process `p` (lines 11–14). -/
def Layout.leafOf (lay : Layout N) (p : Fin N) (v : ℕ) : ℕ :=
  if h : v < N then lay.leaf (.inl ⟨v, h⟩) else lay.leaf (.inr p)

/-- **Algorithm A** of [Hendler–Khait, PODC'14]: an `N`-process max register from CAS objects
arranged in a binary tree with leaf positions `lay`. -/
def impl (lay : Layout N) : Impl maxRegObj Base (Fin N) Loc where
  memInit _ := 0
  locInit _ := .idle
  invoke p _ o := match o with
    | .writeMax v => if v < N then .wLeaf v (lay.leafOf p v) else .wRead v
    | .readMax => .rRoot
  act p l := match l with
    | .idle => .ret 0 .idle
    | .rRoot => .access 1 .read (fun r => .rDone (val r))
    | .rDone r => .ret r .idle
    | .wRead v => .access (lay.leaf (.inr p)) .read
        (fun r => if v ≤ val r then .wDone else .wLeaf v (lay.leaf (.inr p)))
    | .wLeaf v x => .access x (.write v) (fun _ => up v x)
    | .pOld v c j => .access (c / 2) .read (fun r => .pL v c j (val r))
    | .pL v c j old => .access (2 * (c / 2)) .read (fun r => .pR v c j old (val r))
    | .pR v c j old l => .access (2 * (c / 2) + 1) .read (fun r => .pCas v c j old l (val r))
    | .pCas v c j old l r => .access (c / 2) (.cas old (max l r))
        (fun _ => if j then up v (c / 2) else .pOld v c true)
    | .wDone => .ret 0 .idle

/-- Configurations of Algorithm A. -/
abbrev Cfg (N : ℕ) := Config maxRegObj Base (Fin N) Loc

end Podc.ReadUpdateTradeoffs.AlgA
