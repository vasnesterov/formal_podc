import Papers.PODC2012.LimitedUseSnapshots.SnapshotDefs
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Order.Nat

/-!
# Section 5: multi-writer snapshots (Algorithm 4)

Aspnes, Attiya, Censor-Hillel, Ellen, *Limited-Use Atomic Snapshots with Polylogarithmic Step
Complexity*, Section 5, **Algorithm 4**: a `c`-component multi-writer snapshot from a
single-writer snapshot `s` (one component per process, holding the process's array `record_i`
of `c` pairs (value, timestamp)) and a max register `timestamp`.

## Model

* `n` processes `Fin n` (`n ≥ 1`), crash-free asynchronous shared memory (CSLib `Impl`).
* **Base objects are atomic**: `s` is one atomic single-writer snapshot (`swSnap`; the paper uses
  the linearizable Algorithm 3 — there is no composition theorem in the framework, so we follow
  the paper's modular structure and take it as a black box), `timestamp` is one atomic
  `maxRegObj` (unbounded; the paper's `(b − 1)`-limited-use max register).
* `GetTS` (Lines 13–15): `t ← 1 + ReadMax(timestamp)`, `WriteMax(timestamp, t)`, return
  `n·t + i`. The assignment `record_i[j] ← (v, ts)` is done with the `WriteMax` step.
* `CombineScan` (Lines 7–11): for every component `j`, `k ← max_k view_k[j].ts rem n`,
  `result_j ← view_k[j]`.
-/

namespace Podc.LimitedUseSnapshots.Snapshot.MW

open Cslib.SharedMemory

variable (n c : ℕ) (W : Type) (w₀ : Fin c → W)

/-- Operations of a `c`-component multi-writer snapshot. -/
inductive MOp (c : ℕ) (W : Type) where
  | update (j : Fin c) (v : W)
  | scan

/-- Sequential specification of the `c`-component multi-writer snapshot (initial vector `w₀`). -/
abbrev mwSnap : ObjSpec where
  State := Fin c → W
  Op := MOp c W
  Resp := Option (Fin c → W)
  init := w₀
  δ q
    | .update j v => (Function.update q j v, none)
    | .scan => (q, some q)

/-- A record: `c` pairs (value, timestamp). -/
abbrev Rec := Fin c → W × ℕ

/-- The initial record `(−, 0)` (the "no value" `−` is the initial value of the component). -/
def rec₀ : Rec c W := fun j => (w₀ j, 0)

/-- Base objects: the single-writer snapshot `s` and the max register `timestamp`. -/
inductive Obj4 where
  | s
  | ts
  deriving DecidableEq

/-- Specifications of the base objects. -/
abbrev obj4 : Obj4 → ObjSpec
  | .s => swSnap (Fin n) (Rec c W) (fun _ => rec₀ c W w₀)
  | .ts => maxRegObj

/-- Program counters of Algorithm 4. -/
inductive PC4 where
  | idle
  /-- Line 13: `ReadMax(timestamp)` for `MW-Update(j, v)`. -/
  | rd (j : Fin c) (v : W)
  /-- Line 14: `WriteMax(timestamp, r + 1)`; then `record_i[j] ← (v, n(r+1) + i)`. -/
  | wr (j : Fin c) (v : W) (r : ℕ)
  /-- Line 3: `Update(s, i, record_i)`. -/
  | up (j : Fin c)
  | ack
  /-- Line 5: `Scan(s)`. -/
  | sc
  | retS (val : Fin c → W)

/-- Local state: the persistent `record_i` and the program counter. -/
structure Loc4 where
  rcd : Rec c W
  pc : PC4 c W

variable {n c W}

/-- The maximal timestamp of component `j` in a view. -/
def maxTs (view : Fin n → Rec c W) (j : Fin c) : ℕ := Finset.univ.sup fun k => (view k j).2

/-- `CombineScan(c, view)` (Lines 7–11), returning the values. -/
def combine [NeZero n] (view : Fin n → Rec c W) : Fin c → W :=
  fun j => (view ⟨maxTs view j % n, Nat.mod_lt _ (NeZero.pos n)⟩ j).1

variable [NeZero n] {w₀}

/-- The next action of process `i` (Algorithm 4). -/
def act4 (i : Fin n) (l : Loc4 c W) : Action (mwSnap c W w₀) (obj4 n c W w₀) (Loc4 c W) :=
  match l.pc with
  | .idle => .ret none l
  | .rd j v => .access .ts MaxOp.readMax (fun r => ⟨l.rcd, .wr j v r⟩)
  | .wr j v r => .access .ts (MaxOp.writeMax (r + 1))
      (fun _ => ⟨Function.update l.rcd j (v, n * (r + 1) + i), .up j⟩)
  | .up _ => .access .s (SOp.update i l.rcd) (fun _ => ⟨l.rcd, .ack⟩)
  | .ack => .ret none ⟨l.rcd, .idle⟩
  | .sc => .access .s SOp.scan
      (fun view => ⟨l.rcd, .retS (combine (view.getD fun _ => rec₀ c W w₀))⟩)
  | .retS val => .ret (some val) ⟨l.rcd, .idle⟩

variable (n w₀) in
/-- **Algorithm 4** of the paper. -/
abbrev alg4 : Impl (mwSnap c W w₀) (obj4 n c W w₀) (Fin n) (Loc4 c W) where
  memInit
    | .s => fun _ => rec₀ c W w₀
    | .ts => (0 : ℕ)
  locInit _ := ⟨rec₀ c W w₀, .idle⟩
  invoke _ l o := match o with
    | .update j v => ⟨l.rcd, .rd j v⟩
    | .scan => ⟨l.rcd, .sc⟩
  act := act4

end Podc.LimitedUseSnapshots.Snapshot.MW
