import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Model

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
  LL/SC objects with `LL`, `SC`, `VL` (`llscObj`; one *link* per process and object, a
  successful `SC` clears all links — exactly the paper's definition), and a
  `mod m`-fetch-and-increment object with `read` (`faiObj m`, Section 3).
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

/-! ## Base objects -/

/-- Operations of an LL/SC object; the argument `k` is the calling process (its link). -/
inductive LLOp (V K : Type) where
  | ll (k : K)
  | sc (k : K) (v : V)
  | vl (k : K)

/-- An LL/SC object with values `V` and link owners `K`. The state is the value together
with the list of owners of valid links. `LL` returns the value and creates a link; `SC(v)`
succeeds iff the caller has a valid link, in which case it writes `v` and invalidates all
links; `VL` reports whether the caller's link is valid. The response is the current value
together with a success bit. -/
abbrev llscObj (V K : Type) [DecidableEq K] (v₀ : V) : ObjSpec where
  State := V × List K
  Op := LLOp V K
  Resp := V × Bool
  init := (v₀, [])
  δ s
    | .ll k => ((s.1, if k ∈ s.2 then s.2 else k :: s.2), (s.1, true))
    | .sc k v => if k ∈ s.2 then ((v, []), (s.1, true)) else (s, (s.1, false))
    | .vl k => (s, (s.1, decide (k ∈ s.2)))

/-- Operations of a counter. -/
inductive CtrOp where
  | read
  | fai
  deriving DecidableEq

/-- A `mod m`-fetch-and-increment object with `read` (Section 3). -/
abbrev faiObj (m : ℕ) : ObjSpec where
  State := ℕ
  Op := CtrOp
  Resp := ℕ
  init := 0
  δ s
    | .read => (s, s)
    | .fai => ((s + 1) % m, s)

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
  | .ctr => faiObj (3 * delta n)

end Cslib.SharedMemory.BoundedTS
