import Cslib.Computability.Distributed.SharedMemory.Model
import Cslib.Computability.Distributed.SharedMemory.Objects.MaxRegister
import Mathlib.Order.Basic
import Mathlib.Order.Lattice
import Mathlib.Order.Prod.Lex.Basic

/-!
# The 2-component max array (sequential specification)

Aspnes, Attiya, Censor-Hillel, Ellen, *Limited-Use Atomic Snapshots with Polylogarithmic Step
Complexity* (PODC 2012 / J. ACM 2015), Section 2: an object of type `MaxArray_{k×h}` has two
max-register components with the operations

* `MaxUpdate0(r, v)`: set the first component to `max (first, v)`,
* `MaxUpdate1(r, v)`: set the second component to `max (second, v)`,
* `MaxScan(r)`: return both components.

`maxArrObj` is the specification with unbounded components (`ℕ × ℕ`); the ranges `k`, `h` of the
paper are imposed on the invocations by the implementations (`Impl.allowed`). Updates return the
dummy response `(0, 0)`.

`MAOp.contrib o r` is what an operation contributes to the state: `(v, 0)` / `(0, v)` for the
updates, and the returned pair `r` for a scan.
-/

namespace Podc.LimitedUseSnapshots

open Cslib.SharedMemory

/-- Operations of a 2-component max array. -/
inductive MAOp where
  /-- `MaxUpdate0(r, v)`. -/
  | upd0 (v : ℕ)
  /-- `MaxUpdate1(r, v)`. -/
  | upd1 (v : ℕ)
  /-- `MaxScan(r)`. -/
  | scan
  deriving DecidableEq

/-- Sequential specification of the 2-component max array (paper: `MaxArray_{k×h}`, with
unbounded components). -/
abbrev maxArrObj : ObjSpec where
  State := ℕ × ℕ
  Op := MAOp
  Resp := ℕ × ℕ
  init := (0, 0)
  δ q
    | .upd0 v => ((max q.1 v, q.2), (0, 0))
    | .upd1 v => ((q.1, max q.2 v), (0, 0))
    | .scan => (q, q)

@[simp] lemma maxArrObj_upd0 (q : ℕ × ℕ) (v : ℕ) :
    maxArrObj.δ q (.upd0 v) = ((max q.1 v, q.2), (0, 0)) := rfl

@[simp] lemma maxArrObj_upd1 (q : ℕ × ℕ) (v : ℕ) :
    maxArrObj.δ q (.upd1 v) = ((q.1, max q.2 v), (0, 0)) := rfl

@[simp] lemma maxArrObj_scan (q : ℕ × ℕ) : maxArrObj.δ q .scan = (q, q) := rfl

/-- The contribution of an operation with response `r` to the state of a max array. -/
def MAOp.contrib : MAOp → ℕ × ℕ → ℕ × ℕ
  | .upd0 v, _ => (v, 0)
  | .upd1 v, _ => (0, v)
  | .scan, r => r

@[simp] lemma MAOp.contrib_upd0 (v : ℕ) (r : ℕ × ℕ) : (MAOp.upd0 v).contrib r = (v, 0) := rfl
@[simp] lemma MAOp.contrib_upd1 (v : ℕ) (r : ℕ × ℕ) : (MAOp.upd1 v).contrib r = (0, v) := rfl
@[simp] lemma MAOp.contrib_scan (r : ℕ × ℕ) : MAOp.scan.contrib r = r := rfl

section History

variable {P : Type} [DecidableEq P]

/-- The contribution of the instance `x` in the execution `α`: its update value, or the result of
the scan (`(0, 0)` if not invoked, or a pending scan). -/
def contribOf (α : List (Label P maxArrObj)) (x : OpId P) : ℕ × ℕ :=
  match opOf α x with
  | some o => o.contrib ((respOf α x).getD (0, 0))
  | none => (0, 0)

end History

end Podc.LimitedUseSnapshots
