import Podc.Computability.Distributed.SharedMemory.NRL.Erase
import Podc.Computability.Distributed.SharedMemory.NRL.Model

/-!
# Algorithm 1 of [ABH18]: a nesting-safe recoverable read/write register

The algorithm (program of process `p`, recoverable object `R` built from the atomic register
`R` and the single-writer register `S p` holding `⟨flag, curr⟩`, initially `⟨0, null⟩`):

```
 1: procedure WRITE(val)                    10: procedure WRITE.RECOVER(val)
 2:   temp ← R                              11:   ⟨flag, curr⟩ ← S_p
 3:   S_p ← ⟨1, temp⟩                       12:   if flag = 0 ∧ curr ≠ val then
 4:   R ← val                               13:     proceed from line 2
 5:   S_p ← ⟨0, val⟩                        14:   else if flag = 1 ∧ curr = R then
 6:   return ack                            15:     proceed from line 2
 7: procedure READ()                        16:   S_p ← ⟨0, val⟩
 8:   temp ← R                              17:   return ack
 9:   return temp                           18: procedure READ.RECOVER()
                                            19:   temp ← R
                                            20:   return temp
```

One primitive per step. The tests of lines 12 and 14 are internal steps (`c12`, `c15`), the read
of `R` in line 14 is the access `c14` (it is executed only when `flag = 1`, by the short-circuit
evaluation of the condition). `READ.RECOVER` (lines 19–20) is the same code as `READ` (lines
8–9), so the recovery of a read restarts at location `r8`. The recovery functions do not use the
crash location `LI_p`.

The implemented object is CSLib's `register V v₀`: a `write v` returns `v` (the paper's `ack`).
-/

namespace Podc.NestingSafeRecoverable

open Cslib.SharedMemory Cslib.SharedMemory.NRL

/-- Program locations of Algorithm 1 (named by the paper's line numbers). -/
inductive PC1 where
  | w2 | w3 | w4 | w5 | w6 | r8 | r9 | c11 | c12 | c14 | c15 | c16 | c17
  deriving DecidableEq

/-- Volatile variables of Algorithm 1: `temp` and the local copies `flag`, `curr` of `S_p`. -/
structure Loc1 (V : Type) where
  temp : V
  flag : Bool
  curr : Option V

/-- Base objects: `none` is the register `R`, `some p` is `S_p`. -/
abbrev T1 (P V : Type) (v₀ : V) : Option P → ObjSpec
  | none => register V v₀
  | some _ => register (Bool × Option V) (false, none)

/-- The argument of a `WRITE` (dummy `v₀` for a `READ`). -/
def wval {V : Type} (v₀ : V) : RWOp V → V
  | .write v => v
  | .read => v₀

/-- The steps of Algorithm 1 (process `p`, operation `o`, location `pc`, variables `v`). -/
def act1 (P V : Type) [DecidableEq V] (v₀ : V) (p : P) (o : RWOp V) (pc : PC1) (v : Loc1 V) :
    Act (T1 P V v₀) PC1 (Loc1 V) V :=
  match pc with
  | .w2 => .access none (RWOp.read : RWOp V) .w3 (fun r => { v with temp := r })
  | .w3 => .access (some p) (RWOp.write (true, some v.temp)) .w4 (fun _ => v)
  | .w4 => .access none (RWOp.write (wval v₀ o)) .w5 (fun _ => v)
  | .w5 => .access (some p) (RWOp.write (false, some (wval v₀ o))) .w6 (fun _ => v)
  | .w6 => .ret (wval v₀ o)
  | .r8 => .access none (RWOp.read : RWOp V) .r9 (fun r => { v with temp := r })
  | .r9 => .ret v.temp
  | .c11 => .access (some p) (RWOp.read : RWOp (Bool × Option V)) .c12
      (fun s => { v with flag := s.1, curr := s.2 })
  | .c12 => .internal
      (if v.flag = false ∧ v.curr ≠ some (wval v₀ o) then .w2
        else if v.flag = true then .c14 else .c16) v
  | .c14 => .access none (RWOp.read : RWOp V) .c15 (fun r => { v with temp := r })
  | .c15 => .internal (if v.curr = some v.temp then .w2 else .c16) v
  | .c16 => .access (some p) (RWOp.write (false, some (wval v₀ o))) .c17 (fun _ => v)
  | .c17 => .ret (wval v₀ o)

/-- Algorithm 1 of [ABH18] as an implementation of the register `register V v₀` in the
crash-recovery model. -/
abbrev alg1 (P V : Type) [DecidableEq V] (v₀ : V) : Alg P (register V v₀) where
  ι := Option P
  T := T1 P V v₀
  PC := PC1
  V := Loc1 V
  start _ o := (match o with | .write _ => .w2 | .read => .r8, ⟨v₀, false, none⟩)
  recover _ o _ := (match o with | .write _ => .c11 | .read => .r8, ⟨v₀, false, none⟩)
  act := act1 P V v₀

/-- The environment assumption of Section 3.1 ("all values written to the object are distinct"):
the arguments of all `WRITE` invocations are pairwise distinct (as operation instances) and differ
from the initial value `v₀`. -/
def Env1 {P V : Type} [DecidableEq P] (v₀ : V) (h : List (Label P (register V v₀))) : Prop :=
  (∀ x, opOf h x ≠ some (.write v₀)) ∧
    ∀ x y v, opOf h x = some (.write v) → opOf h y = some (.write v) → x = y

end Podc.NestingSafeRecoverable
