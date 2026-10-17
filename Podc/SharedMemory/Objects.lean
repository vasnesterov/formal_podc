import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Spec

/-!
# Standard shared objects with consensus number 1 or 2

Sequential specifications (`ObjSpec`, deterministic) of standard objects, usable both as base
objects and as implemented objects:

* `faaObj V` — fetch&add over an additive monoid (response: the old value);
* `tasObj` — (non-readable) test&set: returns the old bit and sets it;
* `rtasObj` — readable test&set (`tas` / `read`);
* `mtasObj` — readable multi-shot test&set (`tas` / `read` / `reset`);
* `rfaiObj` — readable fetch&increment (`fai` / `read`);
* `maxRegObj` — max register over `ℕ` (`writeMax v` / `readMax`);
* `snapObj n` — `n`-component single-writer atomic snapshot over `ℕ` (`update i v` / `scan`;
  the single-writer discipline "process `i` updates component `i`" is imposed by the
  implementation's `allowed` predicate, since objects cannot see the caller).

Bits are `Bool` with `false` = 0. Operations without a meaningful response return a fixed
acknowledgement (`0`, `false` or the zero view).
-/

namespace Cslib.SharedMemory

-- CSLib candidate (whole file)

/-- Fetch&add over `V`: `δ q a = (q + a, q)`. -/
abbrev faaObj (V : Type) [AddMonoid V] : ObjSpec where
  State := V
  Op := V
  Resp := V
  init := 0
  δ q a := (q + a, q)

/-- (Non-readable) test&set: the only operation sets the bit and returns its old value. -/
abbrev tasObj : ObjSpec where
  State := Bool
  Op := Unit
  Resp := Bool
  init := false
  δ q _ := (true, q)

/-- Operations of a readable test&set. -/
inductive RTASOp where
  | tas
  | read
  deriving DecidableEq

/-- Readable test&set. -/
abbrev rtasObj : ObjSpec where
  State := Bool
  Op := RTASOp
  Resp := Bool
  init := false
  δ q
    | .tas => (true, q)
    | .read => (q, q)

/-- Operations of a readable multi-shot test&set. -/
inductive MTASOp where
  | tas
  | read
  | reset
  deriving DecidableEq

/-- Readable multi-shot test&set: `reset` sets the bit back to `false` (and returns `false`). -/
abbrev mtasObj : ObjSpec where
  State := Bool
  Op := MTASOp
  Resp := Bool
  init := false
  δ q
    | .tas => (true, q)
    | .read => (q, q)
    | .reset => (false, false)

/-- Operations of a readable fetch&increment. -/
inductive FAIOp where
  | fai
  | read
  deriving DecidableEq

/-- Readable fetch&increment over `ℕ` (initially `0`). -/
abbrev rfaiObj : ObjSpec where
  State := ℕ
  Op := FAIOp
  Resp := ℕ
  init := 0
  δ q
    | .fai => (q + 1, q)
    | .read => (q, q)

/-- Operations of a max register. -/
inductive MaxOp where
  | writeMax (v : ℕ)
  | readMax
  deriving DecidableEq

/-- Max register over `ℕ` (initially `0`); `writeMax` returns `0` as acknowledgement. -/
abbrev maxRegObj : ObjSpec where
  State := ℕ
  Op := MaxOp
  Resp := ℕ
  init := 0
  δ q
    | .writeMax v => (max q v, 0)
    | .readMax => (q, q)

/-- Operations of an `n`-component snapshot over `ℕ`. -/
inductive SnapOp (n : ℕ) where
  | update (i : Fin n) (v : ℕ)
  | scan
  deriving DecidableEq

/-- `n`-component atomic snapshot over `ℕ` (all components initially `0`); `update` returns the
zero view as acknowledgement. -/
abbrev snapObj (n : ℕ) : ObjSpec where
  State := Fin n → ℕ
  Op := SnapOp n
  Resp := Fin n → ℕ
  init := fun _ => 0
  δ q
    | .update i v => (Function.update q i v, fun _ => 0)
    | .scan => (q, q)

end Cslib.SharedMemory
