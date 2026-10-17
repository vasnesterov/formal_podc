import Papers.PODC2020.DetectableSpace.Lin
import Papers.PODC2020.DetectableSpace.Perturbing

/-!
# Algorithm 2: a bounded-space detectable CAS object (Section 4.1)

The shared variable `C` (supporting read and CAS primitives) stores the value of the
implemented object together with a bit vector `vec : P → Bool` (one bit per process). Process `p`
has a private non-volatile announcement structure `Ann_p` (fields `CP` and `result`, written by
the system at invocation: `Ann_p.CP := 0`, `Ann_p.result := ⊥`) and a private non-volatile
register `RD_p`.

Pseudocode (code for process `p`); every numbered line that accesses memory is one atomic step,
purely local computations (lines 29, 32) are merged with the preceding step:
```
Cas(old, new):                         Cas.Recover(old, new):
28  ⟨val, vec⟩ := C                    38  if Ann_p.result ≠ ⊥ then
29  if val ≠ old then                  39    return Ann_p.result
30    Ann_p.result := false            40  if Ann_p.CP = 0 then
31    return false                     41    return fail
32  newvec := flipBit(vec, p)          42  ⟨val, vec⟩ := C
33  RD_p := newvec[p]                  43  if vec[p] ≠ RD_p then
34  Ann_p.CP := 1                      44    return fail
35  res := C.CAS(⟨val,vec⟩, ⟨new,newvec⟩)  45  Ann_p.result := true
36  Ann_p.result := res                46  return true
37  return res
```
`Read`: read `C`, persist the value in `Ann_p.result`, return it. `Read.Recover`: if
`Ann_p.result ≠ ⊥` return it, otherwise re-execute `Read`.

Note: the paper's proof of Lemma 2 says that when `Ann_p.CP = 0` "Cas.Recover simply re-invokes
Op (line 41)", but the code (line 41) returns `fail`; we follow the code.

`alg2Gen fix v₀` is Algorithm 2 (`fix = false`, `alg2`) or our corrected version
(`fix = true`, `alg2fix`): there, `Cas(old, new)` with `old = new` reads `C` once, persists
`result := (val = old)` and returns it, never writing `C`.

The initial value of `RD_p` (`⊥` in the paper) is modelled as `false`; it is irrelevant since
`RD_p` is only read when `Ann_p.CP = 1`, i.e. after line 33 of the current operation.
-/

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg2

/-- The private non-volatile memory of a process: `Ann_p.CP`, `Ann_p.result` and `RD_p`. -/
structure Ann (V : Type) where
  CP : Bool
  result : Option (V ⊕ Bool)
  RD : Bool

/-- Program counters with the values of the local variables. -/
inductive Loc (P V : Type) where
  /-- line 28 of `Cas(old, new)` -/
  | c28 (old new : V)
  /-- line 33 (snapshot `s = ⟨val, vec⟩` read at line 28) -/
  | c33 (new : V) (s : V × (P → Bool))
  /-- line 34 -/
  | c34 (new : V) (s : V × (P → Bool))
  /-- line 35: the hardware CAS -/
  | c35 (new : V) (s : V × (P → Bool))
  /-- persist the response `r` in `Ann_p.result` (lines 30, 36, 45; and in `Read`) -/
  | wres (r : V ⊕ Bool)
  /-- return `r` (`none` = `fail`) -/
  | ret (r : Option (V ⊕ Bool))
  /-- line 38 of `Cas.Recover` -/
  | r38
  /-- line 40 -/
  | r40
  /-- line 42 -/
  | r42
  /-- line 43, with `b = vec[p]` read at line 42 -/
  | r43 (b : Bool)
  /-- `Read`: read `C` -/
  | d0
  /-- `Read.Recover`: check `Ann_p.result` -/
  | dr

variable {P V : Type} [DecidableEq P] [DecidableEq V]

open Classical in
/-- The steps of Algorithm 2 (`fix = false`) and of the corrected version (`fix = true`). -/
noncomputable def act (fix : Bool) (p : P) : Loc P V → Act (V × (P → Bool)) (Ann V) (Loc P V) (V ⊕ Bool)
  | .c28 old new => .sh fun C =>
      (if C.1 ≠ old then .wres (.inr false)
        else if fix = true ∧ old = new then .wres (.inr true) else .c33 new C, C)
  | .c33 new s => .pv fun A => (.c34 new s, { A with RD := !s.2 p })
  | .c34 new s => .pv fun A => (.c35 new s, { A with CP := true })
  | .c35 new s => .sh fun C =>
      if C = s then (.wres (.inr true), (new, Function.update s.2 p (!s.2 p)))
      else (.wres (.inr false), C)
  | .wres r => .pv fun A => (.ret (some r), { A with result := some r })
  | .ret r => .ret r
  | .r38 => .pv fun A => (match A.result with | some r => .ret (some r) | none => .r40, A)
  | .r40 => .pv fun A => (if A.CP = true then .r42 else .ret none, A)
  | .r42 => .sh fun C => (.r43 (C.2 p), C)
  | .r43 b => .pv fun A => (if b = A.RD then .wres (.inr true) else .ret none, A)
  | .d0 => .sh fun C => (.wres (.inl C.1), C)
  | .dr => .pv fun A => (match A.result with | some r => .ret (some r) | none => .d0, A)

/-- Initial local state of an operation. -/
def start : RCOp V → Loc P V
  | .read => .d0
  | .cas old new => .c28 old new

/-- Initial local state of a recovery function. -/
def recov : RCOp V → Loc P V
  | .read => .dr
  | .cas _ _ => .r38

end Alg2

open Alg2

variable {P V : Type} [DecidableEq P] [DecidableEq V]

/-- Algorithm 2 (`fix = false`) and its corrected version (`fix = true`) as recoverable
implementations of the read/CAS object `casRC V v₀`. -/
noncomputable abbrev alg2Gen (fix : Bool) (v₀ : V) : RImpl (casRC V v₀) P where
  Sh := V × (P → Bool)
  Pv := Ann V
  L := Loc P V
  sh₀ := (v₀, fun _ => false)
  pv₀ := fun _ => ⟨false, none, false⟩
  start _ o := start o
  recov _ o := recov o
  aux _ _ A := { A with CP := false, result := none }
  act := act fix

/-- **Algorithm 2** of the paper (bounded-space detectable CAS). -/
noncomputable abbrev alg2 (v₀ : V) : RImpl (casRC V v₀) P := alg2Gen false v₀

/-- The corrected Algorithm 2: `Cas(v, v)` never writes `C`. -/
noncomputable abbrev alg2fix (v₀ : V) : RImpl (casRC V v₀) P := alg2Gen true v₀

namespace Alg2

section simps
variable (fix : Bool) (v₀ : V)
@[simp] lemma alg2Gen_sh₀ : (alg2Gen (P := P) fix v₀).sh₀ = (v₀, fun _ => false) := rfl
@[simp] lemma alg2Gen_pv₀ : (alg2Gen (P := P) fix v₀).pv₀ = fun _ => ⟨false, none, false⟩ := rfl
@[simp] lemma alg2Gen_start (p : P) (o : RCOp V) : (alg2Gen fix v₀).start p o = start o := rfl
@[simp] lemma alg2Gen_recov (p : P) (o : RCOp V) : (alg2Gen fix v₀).recov p o = recov o := rfl
@[simp] lemma alg2Gen_aux (p : P) (o : RCOp V) (A : Ann V) :
    (alg2Gen fix v₀).aux p o A = { A with CP := false, result := none } := rfl
@[simp] lemma alg2Gen_act (p : P) (l : Loc P V) : (alg2Gen fix v₀).act p l = act fix p l := rfl
end simps

/-- Step measure for wait-freedom. -/
def μ : Loc P V → ℕ
  | .c28 .. => 5
  | .c33 .. => 4
  | .c34 .. => 3
  | .c35 .. => 2
  | .wres _ => 1
  | .ret _ => 0
  | .r38 => 7
  | .r40 => 6
  | .r42 => 5
  | .r43 _ => 4
  | .d0 => 2
  | .dr => 3

end Alg2

set_option linter.unusedSimpArgs false in
/-- Every operation and recovery function of (both versions of) Algorithm 2 completes within a
bounded number of its own steps (wait-freedom, first claim of Lemma 2). -/
theorem alg2Gen_boundedSteps (fix : Bool) (v₀ : V) :
    (alg2Gen (P := P) fix v₀).BoundedSteps Alg2.μ := by
  intro p l
  cases l with
  | c28 old new =>
    intro s
    simp only [alg2Gen, act]
    split_ifs <;> simp [μ]
  | c35 new s =>
    intro C
    simp only [alg2Gen, act]
    split_ifs <;> simp [μ]
  | r38 => intro A; simp only [alg2Gen, act]; cases A.result <;> simp [μ]
  | r40 => intro A; simp only [alg2Gen, act]; split_ifs <;> simp [μ]
  | r43 b => intro A; simp only [alg2Gen, act]; split_ifs <;> simp [μ]
  | dr => intro A; simp only [alg2Gen, act]; cases A.result <;> simp [μ]
  | ret r => simp [alg2Gen, act]
  | _ => intro _; simp [alg2Gen, act, μ]

/-- Algorithm 2 is (wait-free, hence) obstruction-free. -/
theorem alg2Gen_obstructionFree (fix : Bool) (v₀ : V) :
    (alg2Gen (P := P) fix v₀).ObstructionFree :=
  (alg2Gen_boundedSteps fix v₀).obstructionFree

end Papers.PODC2020.DetectableSpace
