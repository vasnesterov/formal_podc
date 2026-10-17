import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Model
import Cslib.Computability.Distributed.SharedMemory.Objects.FetchAdd
import Cslib.Computability.Distributed.SharedMemory.Objects.LLSC

/-!
# Mutable timestamp systems: specification and base objects

Model of Bashari, Jamadi, Woelfel, *Efficient Bounded Timestamping from Standard
Synchronization Primitives*, PODC 2023 (full version, University of Calgary report).

* **System.** Asynchronous shared memory (CSLib `Cslib.SharedMemory.Impl`), `n` processes
  `Fin n`, deterministic programs, executions are lists of labels.
* **Implemented object** (`mtsObj n`, Section 1): an `n`-process *mutable timestamp system*
  with operations `updateTS()` and `isEarlier(x, y)`. Its sequential specification is the
  paper's "interpreted value": the processes ordered by the time of their latest `updateTS()`,
  followed by the processes that never called `updateTS()`, ordered by identifier.
  `isEarlier(x, y)` returns whether `x` comes strictly before `y` in this total order.
  Since CSLib specifications do not see the caller, `updateTS()` of process `p` is the
  operation `upd p`, and `Impl.allowed` lets only `p` invoke it.
* **Base objects** (Section 3): single-bit registers (CSLib `register Bool false`),
  LL/SC objects with `LL`, `SC`, `VL` (CSLib `llscObj`; one *link* per process and object, a
  successful `SC` clears all links — exactly the paper's definition), and a
  `mod m`-fetch-and-increment object with `read` (Section 3; the library's `modFaiObj m`).
-/

set_option linter.unusedSectionVars false

namespace Cslib.SharedMemory.BoundedTS

open Cslib.SharedMemory

/-! ## The implemented object -/

/-- Operations of an `n`-process MTS. `upd p` is `updateTS()` called by `p`. -/
inductive MOp (n : ℕ) where
  /-- `updateTS()` by process `p`. -/
  | upd (p : Fin n)
  /-- `isEarlier(x, y)`. -/
  | ie (x y : Fin n)
  deriving DecidableEq

/-- `x` comes strictly before `y` in the order "processes in `s` (order of their latest
`updateTS`), then the other processes by identifier". -/
def before {n : ℕ} (s : List (Fin n)) (x y : Fin n) : Bool :=
  match s.idxOf? x, s.idxOf? y with
  | some a, some b => decide (a < b)
  | some _, none => true
  | none, some _ => false
  | none, none => decide (x < y)

@[simp] lemma before_self {n : ℕ} (s : List (Fin n)) (x : Fin n) : before s x x = false := by
  unfold before; split <;> simp_all

/-- The sequential specification of an `n`-process mutable timestamp system (MTS).
The state lists the processes that called `updateTS()` in the order of their latest call
(earliest first). Responses: `none` for `updateTS()`, `some b` for `isEarlier`. -/
abbrev mtsObj (n : ℕ) : ObjSpec where
  State := List (Fin n)
  Op := MOp n
  Resp := Option Bool
  init := []
  δ s
    | .upd p => (s.erase p ++ [p], none)
    | .ie x y => (s, some (before s x y))

/-! ## The algorithm's data -/

/-- Contents of `TS[i]`: `(cluster, index, flag, inv)`; `index = none` is `⊥`. -/
structure TSVal where
  cl : ℕ
  idx : Option ℤ
  flag : Bool
  inv : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Contents of `LookupTable[i]`: `(x, y, res)`; `res = none` is `⊥`. -/
structure LTVal (n : ℕ) where
  x : Fin n
  y : Fin n
  res : Option Bool
  deriving DecidableEq, Repr

/-- The paper's constants (Section 4.2). -/
def zeta (n : ℕ) : ℕ := 6 * n + 2
def eta (n : ℕ) : ℕ := zeta n * n
def mu (n : ℕ) : ℕ := 6 * n ^ 3 + 6 * n ^ 2 + 2
def gamma (n : ℕ) : ℕ := 3 * n ^ 3 + 4 * n
def delta (n : ℕ) : ℕ := eta n + mu n + gamma n

/-- The dominance order `≪` on `TS` entries of processes `i` and `j` (Section 4.2). -/
def less (a b : TSVal) (i j : ℕ) : Bool :=
  match a.idx, b.idx with
  | none, none => decide (i < j)
  | some _, none => true
  | none, some _ => false
  | some x, some y => (decide (a.cl = b.cl) && decide (x < y)) || decide (a.cl = (b.cl + 2) % 3)

/-- Names of the base objects: announce bits `A[i]`, `TS[i]`, `LookupTable[i]`, `Counter`. -/
inductive Obj (n : ℕ) where
  | A (i : Fin n)
  | TS (i : Fin n)
  | LT (i : Fin n)
  | ctr
  deriving DecidableEq

/-- Initial value of `TS[i]`: `(0, ⊥, 0, 2)`. -/
def tsInit : TSVal := ⟨0, none, false, 2⟩

/-- The base objects. -/
abbrev Base (n : ℕ) [NeZero n] : Obj n → ObjSpec
  | .A _ => register Bool false
  | .TS _ => llscObj TSVal (Fin n) tsInit
  | .LT _ => llscObj (LTVal n) (Fin n) ⟨0, 0, some true⟩
  | .ctr => modFaiObj (3 * delta n)

end Cslib.SharedMemory.BoundedTS
