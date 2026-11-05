import Papers.PODC2012.LimitedUseSnapshots.Spec
import Papers.PODC2012.LimitedUseSnapshots.Tree

/-!
# Algorithm 2: the 2-component max array `MaxArray_{k×h}`

Aspnes, Attiya, Censor-Hillel, Ellen, *Limited-Use Atomic Snapshots with Polylogarithmic Step
Complexity*, Algorithm 2 (Section 3), and its correction from the authors' erratum (line 9.5:
`MaxUpdate1` performs an embedded `MaxScan` after its `WriteMax`).

The recursion of Algorithm 2 is unfolded over a tree `T : Shape` (leaves = values of the first
component, `k = T.size`; the paper's split point `m` at a node is the size of its left subtree, so
every choice of `m`, balanced or not, is covered). Base objects (`Obj`):

* `sw a` — the 1-bit multi-writer register `switch` of the internal node at address `a`;
* `sec a` — the `MaxReg_h` object `second` of the node at address `a` (`sec []` is the second
  component). These max registers are taken as **atomic** base objects (CSLib `maxRegObj`, over
  `ℕ`, so the range `h` plays no role for correctness); their `O(log h)` cost is a parameter of the
  step-complexity analysis.

Local states (`Loc`), with the line numbers of Algorithm 2:

* `d0 v a` — `MaxUpdate0(r, v)` has descended to node `a`; right steps (line 6) need no shared
  access and are skipped, a left step reads `switch` (line 3) and stops if it is `1`;
* `up v a` — `MaxUpdate0(r, v)` returns from the recursion below node `a`: it writes `switch ← 1`
  (line 7) at the deepest right step strictly above `a`, then continues upwards;
* `w1 v` — `MaxUpdate1(r, v)` about to perform `WriteMax(r.second, v)` (line 9);
* `s1 e a … s5 e a x` — a `MaxScan` at node `a` (lines 11, 12, 13, 16, 17; at a leaf, `s1` is the
  final `ReadMax(r.second)` of the `MaxArray_{1×h}` case); `e = true` marks the scan embedded in
  `MaxUpdate1` by the erratum (line 9.5), whose result is discarded;
* `rt r` — about to return `r`.

`alg T fix` is Algorithm 2 for `fix = false` and the corrected algorithm for `fix = true`.
`MaxUpdate0(v)` may only be invoked with `v < k` (`allowed`).
-/

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

/-- Base objects of Algorithm 2. -/
inductive Obj where
  /-- `switch` of the node at address `a`. -/
  | sw (a : List Bool)
  /-- `second` (a `MaxReg_h`) of the node at address `a`. -/
  | sec (a : List Bool)
  deriving DecidableEq

/-- Specifications of the base objects: 1-bit registers and (atomic) max registers. -/
abbrev baseObj : Obj → ObjSpec
  | .sw _ => binaryRegister
  | .sec _ => maxRegObj

/-- Local states of a process running Algorithm 2. -/
inductive Loc where
  | idle
  | d0 (v : ℕ) (a : List Bool)
  | up (v : ℕ) (a : List Bool)
  | w1 (v : ℕ)
  | s1 (e : Bool) (a : List Bool)
  | s2 (e : Bool) (a : List Bool) (x : ℕ)
  | s3 (e : Bool) (a : List Bool) (x : ℕ)
  | s4 (e : Bool) (a : List Bool)
  | s5 (e : Bool) (a : List Bool) (x : ℕ)
  | rt (r : ℕ × ℕ)
  deriving DecidableEq

/-- The deepest right step strictly above the node `a`: the longest `a'` with
`a' ++ true :: _ = a`. -/
def deepRight : List Bool → Option (List Bool)
  | [] => none
  | b :: c =>
    match deepRight c with
    | some a => some (b :: a)
    | none => if b then some [] else none

/-- Returning from the recursion of `MaxUpdate0(v)` below node `a`: set the switch of the deepest
right step above `a` (line 7), or return. -/
def upAct (v : ℕ) (a : List Bool) : Action maxArrObj baseObj Loc :=
  match deepRight a with
  | none => .ret (0, 0) .idle
  | some a' => .access (.sw a') (.write true) (fun _ => .up v a')

/-- `MaxUpdate0(v)` at node `a` whose subtree is `t`, with relative value `w` (lines 2–6). -/
def d0Act (v : ℕ) : ℕ → Shape → List Bool → Action maxArrObj baseObj Loc
  | _, .leaf, a => upAct v a
  | w, .node l r, a =>
    if w < l.size then
      .access (.sw a) .read (fun b => if b then .up v a else .d0 v (a ++ [false]))
    else d0Act v (w - l.size) r (a ++ [true])

/-- The next action of a process (independent of the process identity). -/
def act (T : Shape) (fix : Bool) : Loc → Action maxArrObj baseObj Loc
  | .idle => .ret (0, 0) .idle
  | .d0 v a => d0Act v (v - T.lo a) (T.subD a) a
  | .up v a => upAct v a
  | .w1 v => .access (.sec []) (.writeMax v) (fun _ => if fix then .s1 true [] else .rt (0, 0))
  | .s1 e a =>
    match T.subD a with
    | .leaf => .access (.sec a) .readMax (fun x => .rt (if e then (0, 0) else (T.lo a, x)))
    | .node _ _ => .access (.sec a) .readMax (fun x => .s2 e a x)
  | .s2 e a x => .access (.sw a) .read (fun b => if b then .s4 e a else .s3 e a x)
  | .s3 e a x => .access (.sec (a ++ [false])) (.writeMax x) (fun _ => .s1 e (a ++ [false]))
  | .s4 e a => .access (.sec a) .readMax (fun x => .s5 e a x)
  | .s5 e a x => .access (.sec (a ++ [true])) (.writeMax x) (fun _ => .s1 e (a ++ [true]))
  | .rt r => .ret r .idle

/-- Local state at the invocation of an operation. -/
def invokeLoc : MAOp → Loc
  | .upd0 v => .d0 v []
  | .upd1 v => .w1 v
  | .scan => .s1 false []

/-- Algorithm 2 (`fix = false`) and its corrected version from the erratum (`fix = true`) over
the tree `T` (`k = T.size`), for processes `P`. -/
def alg (P : Type) (T : Shape) (fix : Bool) : Impl maxArrObj baseObj P Loc where
  memInit
    | .sw _ => false
    | .sec _ => 0
  locInit _ := .idle
  invoke _ _ o := invokeLoc o
  act _ l := act T fix l
  allowed _ o :=
    match o with
    | .upd0 v => v < T.size
    | _ => True

end Podc.LimitedUseSnapshots
