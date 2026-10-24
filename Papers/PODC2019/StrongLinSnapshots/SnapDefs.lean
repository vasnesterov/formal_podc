import Papers.PODC2015.ABADetection.Defs
import Cslib.Computability.Distributed.SharedMemory.StrongLin
import Cslib.Computability.Distributed.SharedMemory.Objects.Snapshot

/-!
# The strongly linearizable snapshot of Ovens–Woelfel (PODC 2019), Algorithm 3: definitions

Section 4.3 of the paper. The implemented object is CSLib's `n`-component single-writer
snapshot `snapObj n` over `ℕ` (`0` plays the role of `⊥`; `update_p(x)` is only allowed for
`x ≠ 0` and only on component `p`). The shared objects are

* a snapshot object `S` (base object `.S`, type `snapObj n`), and
* an ABA-detecting register `R` over vectors (base object `.R`, type `abaObj` of the
  ABADetection formalization, initially the all-`⊥` vector).

**Model choice.** Both base objects are *atomic*. In the paper `S` is only a linearizable
implementation (to get bounded space) and `R` is Algorithm 2; see `README.md`.

* `SLupdate_p(x)`: 43 `S.update_p(x)`; 44 `s ← S.scan()`; 45 `R.DWrite_p(s)`.
* `SLscan_p()`: repeat { 47 `(s₁, c₁) ← R.DRead_p()`; 48 `ℓ ← S.scan()`;
  49 `(s₂, c₂) ← R.DRead_p()`; 50–51 if not `s₁ = ℓ = s₂` then `R.DWrite_p(ℓ)` }
  until `s₁ = ℓ = s₂` and `¬c₂`; return `s₂`.
-/

namespace Podc.StrongLinSnapshots.Snap

open Cslib.SharedMemory Cslib.SharedMemory.ABADetection

variable (n : ℕ)

/-- Vectors (views of the snapshot). -/
abbrev Vec := Fin n → ℕ

/-- The base objects: the linearizable snapshot `S` and the ABA-detecting register `R`. -/
inductive Obj where
  | S
  | R
  deriving DecidableEq

/-- The ABA-detecting register over vectors, initially all `⊥ = 0`. -/
abbrev RObj : ObjSpec := abaObj (Fin n) (Vec n) (fun _ => 0)

/-- The base objects' specifications. -/
abbrev B : Obj → ObjSpec
  | .S => snapObj n
  | .R => RObj n

/-- Program counters (the local state; Algorithm 3 has no persistent local variables). -/
inductive PC where
  /-- No pending operation. -/
  | idle
  /-- `SLupdate(x)`: about to execute line 43. -/
  | u43 (x : ℕ)
  /-- `SLupdate(x)`: about to execute line 44. -/
  | u44 (x : ℕ)
  /-- `SLupdate(x)`: about to execute line 45 (write `s` to `R`). -/
  | u45 (x : ℕ) (s : Vec n)
  /-- `SLupdate`: about to return. -/
  | uRet
  /-- `SLscan`: about to execute line 47. -/
  | s47
  /-- `SLscan`: about to execute line 48 (`s₁` read on line 47). -/
  | s48 (s1 : Vec n)
  /-- `SLscan`: about to execute line 49 (`ℓ` read on line 48). -/
  | s49 (s1 l : Vec n)
  /-- `SLscan`: about to execute line 51 (help: write `ℓ` to `R`). -/
  | s51 (l : Vec n)
  /-- `SLscan`: about to return `v`. -/
  | sRet (v : Vec n)

variable {n}

/-- The next action in each program counter. -/
def act (p : Fin n) : PC n → Action (snapObj n) (B n) (PC n)
  | .idle => .ret (fun _ => 0) .idle
  | .u43 x => .access .S (.update p x) (fun _ => .u44 x)
  | .u44 x => .access .S .scan (fun s => .u45 x s)
  | .u45 _ s => .access .R (.dwrite s) (fun _ => .uRet)
  | .uRet => .ret (fun _ => 0) .idle
  | .s47 => .access .R (.dread p) (fun r => .s48 r.1)
  | .s48 s1 => .access .S .scan (fun l => .s49 s1 l)
  | .s49 s1 l => .access .R (.dread p) (fun r =>
      if s1 = l ∧ l = r.1 then (if r.2 = false then .sRet r.1 else .s47) else .s51 l)
  | .s51 l => .access .R (.dwrite l) (fun _ => .s47)
  | .sRet v => .ret v .idle

/-- Which operations a process may invoke: `update_p(x)` only on its own component and only with
`x ≠ ⊥`. -/
def allowedOp (p : Fin n) : SnapOp n → Prop
  | .update i x => i = p ∧ x ≠ 0
  | .scan => True

/-- **Algorithm 3**: the strongly linearizable snapshot (with atomic `S` and `R`). -/
def impl : Impl (snapObj n) (B n) (Fin n) (PC n) where
  memInit
    | .S => fun _ => 0
    | .R => ((fun _ => 0), fun _ => false)
  locInit _ := .idle
  invoke _ _ o := match o with
    | .update _ x => .u43 x
    | .scan => .s47
  act := act
  allowed := allowedOp

end Podc.StrongLinSnapshots.Snap
