import Papers.PODC2020.DetectableSpace.Basic

/-!
# Algorithm 1: a bounded-space detectable read/write register (Section 3)

Processes are `Fin n` (`0`-based, as in the paper's "process 0" and `A[N][N][2]`).

* Shared non-volatile memory: the register `R = ⟨val, q, toggle⟩ : V × Fin n × Bool` and the
  toggle-bit array `A[i][q][b]` (modelled as `A : Fin n × Fin n × Bool → Bool`), initially all
  `false` (`0`). Toggle indices `0, 1` are `false, true`; `1 - b` is `!b`.
* Private non-volatile memory of `p`: `Ann_p.CP` (`cp`), `Ann_p.result` (`res`, `none` = `⊥`),
  `RD_p` (`rd`, `none` = `⊥`) and `T_p` (`T`, initially `0`). At invocation the system sets
  `Ann_p.CP := 0` and `Ann_p.result := ⊥` (`aux`).
* `R` is initially `⟨v_init, 0, t₀⟩`. The paper has `t₀ = 0`; we show that this is incorrect
  (`Alg1Counter.lean`) and that `t₀ = 1` is correct (`Alg1Fix.lean`).

Every line of the pseudocode is one atomic step accessing one variable (lines 9–10 and 23–24
are loops of `n` steps, one per array entry; the two reads of line 20 are two steps):
```
Write(val):                                  Write.Recover(val):
 1 ⟨qval, q, qtoggle⟩ := R                    14 ⟨mtoggle, qval, q, qtoggle⟩ := RD_p
 2 A[p][q][1 - qtoggle] := 0                  15 if Ann_p.result ≠ ⊥ then
 3 mtoggle := T_p                             16   return ack
 4 RD_p := ⟨mtoggle, qval, q, qtoggle⟩        17 if Ann_p.CP = 0 then
 5 if R ≠ ⟨qval, q, qtoggle⟩ then goto 8      18   return fail
 6 Ann_p.CP := 1                              19 if Ann_p.CP = 1 then
 7 R := ⟨val, p, mtoggle⟩                     20   if R = ⟨qval, q, qtoggle⟩ and A[p][q][1 - qtoggle] = 0 then
 8 Ann_p.CP := 2                              21     return fail
 9 for i = 1 to N do                          22 Ann_p.CP := 2
10   A[i][p][mtoggle] := 1                    23 for i = 1 to N do
11 T_p := 1 - mtoggle                         24   A[i][p][mtoggle] := 1
12 Ann_p.result := ack                        25 T_p := 1 - mtoggle
13 return ack                                 26 Ann_p.result := ack
                                              27 return ack
```
Lines 22–27 are literally lines 8–13, so the recovery function continues with the same local
states `w8`, `w9`, `w11`, `w12`. `ack` is the written value (the response of `write v` in
CSLib's `register`). `Read`: read `R`, persist its value in `Ann_p.result`, return it;
`Read.Recover`: return `Ann_p.result` if it is not `⊥`, otherwise re-execute `Read`.
-/

namespace Papers.PODC2020.DetectableSpace

open Cslib.SharedMemory

namespace Alg1

/-- Contents of `R`: value, writer, toggle index. -/
abbrev Trip (V : Type) (n : ℕ) := V × Fin n × Bool

/-- Shared non-volatile memory: `R` and `A`. -/
structure Sh (V : Type) (n : ℕ) where
  R : Trip V n
  A : Fin n × Fin n × Bool → Bool

/-- Private non-volatile memory of a process: `Ann_p.CP`, `Ann_p.result`, `RD_p`, `T_p`. -/
structure Pv (V : Type) (n : ℕ) where
  cp : ℕ
  res : Option V
  rd : Option (Bool × Trip V n)
  T : Bool

/-- Program counters together with the values of the local (volatile) variables:
`v` = `val`, `tr` = `⟨qval, q, qtoggle⟩`, `mt` = `mtoggle`, `i` = loop index. -/
inductive Loc (V : Type) (n : ℕ) where
  | w1 (v : V)
  | w2 (v : V) (tr : Trip V n)
  | w3 (v : V) (tr : Trip V n)
  | w4 (v : V) (tr : Trip V n) (mt : Bool)
  | w5 (v : V) (tr : Trip V n) (mt : Bool)
  | w6 (v : V) (tr : Trip V n) (mt : Bool)
  | w7 (v : V) (tr : Trip V n) (mt : Bool)
  /-- line 8 (= line 22) -/
  | w8 (v : V) (tr : Trip V n) (mt : Bool)
  /-- lines 9–10 (= 23–24), next index `i` -/
  | w9 (v : V) (tr : Trip V n) (mt : Bool) (i : Fin n)
  /-- line 11 (= 25) -/
  | w11 (v : V) (tr : Trip V n) (mt : Bool)
  /-- line 12 (= 26) -/
  | w12 (v : V) (tr : Trip V n) (mt : Bool)
  | r14 (v : V)
  | r15 (v : V) (tr : Trip V n) (mt : Bool)
  | r17 (v : V) (tr : Trip V n) (mt : Bool)
  | r19 (v : V) (tr : Trip V n) (mt : Bool)
  /-- line 20, first conjunct (read `R`) -/
  | r20 (v : V) (tr : Trip V n) (mt : Bool)
  /-- line 20, second conjunct (read `A[p][q][1 - qtoggle]`) -/
  | r20b (v : V) (tr : Trip V n) (mt : Bool)
  /-- `Read`: read `R` -/
  | d1
  /-- `Read`: persist the value read -/
  | d2 (x : V)
  /-- `Read.Recover` -/
  | dr
  /-- return (`none` = `fail`) -/
  | ret (r : Option V)

variable {V : Type} [DecidableEq V] {n : ℕ} [NeZero n]

/-- The steps of Algorithm 1 (code for process `p`). -/
def act (p : Fin n) : Loc V n → Act (Sh V n) (Pv V n) (Loc V n) V
  | .w1 v => .sh fun s => (.w2 v s.R, s)
  | .w2 v tr => .sh fun s => (.w3 v tr, { s with A := Function.update s.A (p, tr.2.1, !tr.2.2) false })
  | .w3 v tr => .pv fun m => (.w4 v tr m.T, m)
  | .w4 v tr mt => .pv fun m => (.w5 v tr mt, { m with rd := some (mt, tr) })
  | .w5 v tr mt => .sh fun s => (if s.R = tr then .w6 v tr mt else .w8 v tr mt, s)
  | .w6 v tr mt => .pv fun m => (.w7 v tr mt, { m with cp := 1 })
  | .w7 v tr mt => .sh fun s => (.w8 v tr mt, { s with R := (v, p, mt) })
  | .w8 v tr mt => .pv fun m => (.w9 v tr mt 0, { m with cp := 2 })
  | .w9 v tr mt i => .sh fun s =>
      (if h : i.val + 1 < n then .w9 v tr mt ⟨i.val + 1, h⟩ else .w11 v tr mt,
        { s with A := Function.update s.A (i, p, mt) true })
  | .w11 v tr mt => .pv fun m => (.w12 v tr mt, { m with T := !mt })
  | .w12 v _ _ => .pv fun m => (.ret (some v), { m with res := some v })
  | .r14 v => .pv fun m =>
      (match m.rd with
        | some (mt, tr) => .r15 v tr mt
        | none => .r15 v (v, 0, false) false, m)
  | .r15 v tr mt => .pv fun m => (if m.res.isSome then .ret (some v) else .r17 v tr mt, m)
  | .r17 v tr mt => .pv fun m => (if m.cp = 0 then .ret none else .r19 v tr mt, m)
  | .r19 v tr mt => .pv fun m => (if m.cp = 1 then .r20 v tr mt else .w8 v tr mt, m)
  | .r20 v tr mt => .sh fun s => (if s.R = tr then .r20b v tr mt else .w8 v tr mt, s)
  | .r20b v tr mt => .sh fun s =>
      (if s.A (p, tr.2.1, !tr.2.2) = false then .ret none else .w8 v tr mt, s)
  | .d1 => .sh fun s => (.d2 s.R.1, s)
  | .d2 x => .pv fun m => (.ret (some x), { m with res := some x })
  | .dr => .pv fun m =>
      (match m.res with
        | some x => .ret (some x)
        | none => .d1, m)
  | .ret r => .ret r

/-- Initial local state of an operation. -/
def start : RWOp V → Loc V n
  | .read => .d1
  | .write v => .w1 v

/-- Initial local state of a recovery function. -/
def recov : RWOp V → Loc V n
  | .read => .dr
  | .write v => .r14 v

/-- What the caller writes to `Ann_p` at invocation: `Ann_p.CP := 0`, `Ann_p.result := ⊥`. -/
def aux (m : Pv V n) : Pv V n := { m with cp := 0, res := none }

end Alg1

open Alg1

variable {V : Type} [DecidableEq V]

/-- **Algorithm 1** for processes `Fin n`, implementing a read/write register with initial value
`v₀`; `R` is initially `⟨v₀, 0, t₀⟩` (the paper: `t₀ = 0`, i.e. `false`). -/
@[reducible] def alg1 (V : Type) [DecidableEq V] (v₀ : V) (n : ℕ) [NeZero n] (t₀ : Bool) :
    RImpl (register V v₀) (Fin n) where
  Sh := Sh V n
  Pv := Pv V n
  L := Loc V n
  sh₀ := ⟨(v₀, 0, t₀), fun _ => false⟩
  pv₀ := fun _ => ⟨0, none, none, false⟩
  start := fun _ o => start o
  recov := fun _ o => recov o
  aux := fun _ _ m => aux m
  act := act

/-- The measure certifying wait-freedom. -/
def Alg1.μ (n : ℕ) : Loc V n → ℕ
  | .w1 _ => n + 11
  | .w2 .. => n + 10
  | .w3 .. => n + 9
  | .w4 .. => n + 8
  | .w5 .. => n + 7
  | .w6 .. => n + 6
  | .w7 .. => n + 5
  | .w8 .. => n + 4
  | .w9 _ _ _ i => n + 3 - i.val
  | .w11 .. => 2
  | .w12 .. => 1
  | .r14 _ => n + 10
  | .r15 .. => n + 9
  | .r17 .. => n + 8
  | .r19 .. => n + 7
  | .r20 .. => n + 6
  | .r20b .. => n + 5
  | .d1 => 2
  | .d2 _ => 1
  | .dr => 3
  | .ret _ => 0

/-- Algorithm 1 is wait-free: every step of an operation or recovery function decreases `μ`
(lines 9–10 / 23–24 are `n` steps). -/
theorem alg1_boundedSteps (v₀ : V) (n : ℕ) [NeZero n] (t₀ : Bool) :
    (alg1 V v₀ n t₀).BoundedSteps (Alg1.μ n) := by
  intro p l
  cases l with
  | w9 v tr mt i =>
    simp only [alg1, Alg1.act]
    intro s
    have := i.isLt
    split <;> simp [Alg1.μ] <;> omega
  | r14 v =>
    simp only [alg1, Alg1.act]
    intro m
    split <;> simp [Alg1.μ]
  | dr =>
    simp only [alg1, Alg1.act]
    intro m
    split <;> simp [Alg1.μ]
  | _ =>
    simp only [alg1, Alg1.act] <;> intros <;> (try split) <;> simp [Alg1.μ]

/-- **Lemma 1 (progress part).** Algorithm 1 is wait-free, in particular obstruction-free. -/
theorem alg1_obstructionFree (v₀ : V) (n : ℕ) [NeZero n] (t₀ : Bool) :
    (alg1 V v₀ n t₀).ObstructionFree :=
  (alg1_boundedSteps v₀ n t₀).obstructionFree

end Papers.PODC2020.DetectableSpace
