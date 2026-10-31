import Mathlib
import Cslib.Computability.Distributed.SharedMemory.Linearization

/-!
# Algorithm 4 of [ABH18] (recoverable counter): two counterexamples

Algorithm 4 builds a recoverable counter from an array `R[1..N]` of recoverable read/write
objects (Algorithm 1). The paper's model (Section 2): a crash resets *all* local variables of the
crashed process to arbitrary values; if the crash happens inside a nested recoverable operation,
the system invokes the recovery function of the *innermost* pending recoverable operation, and
when it completes the caller continues after the call ("once its recovery is completed, INC
returns in line 5").

We give a concrete interpreter for Algorithm 4 composed with Algorithm 1, for `N = 2` processes,
with exactly these semantics (volatile variables are reset to `0`, the most benign choice of
"arbitrary values"), and two executions whose counter history is not linearizable:

* `read_not_nrl`: process 1 crashes inside the nested `R[2].READ` called by the counter's `READ`
  (line 14). `R[2].READ.RECOVER` returns `R[2]`'s value, but the caller's `val` and loop index
  `i` are lost; the counter's `READ` returns `0` although an `INC` completed before it started.
* `inc_recover_not_nrl`: process 0 crashes in `INC` when it is about to execute line 4 (invoke
  `R[p].WRITE`), so `LI_p = 4`; `INC.RECOVER` tests `LI_p < 4` and returns `ack` without
  incrementing (the prose says "before line 4 – INC is re-executed": the test should be
  `LI_p ≤ 4`). A later `READ` returns `0`.
-/

namespace Podc.NestingSafeRecoverable.Alg4

open Cslib.SharedMemory

/-- Counter operations. -/
inductive COp where
  | inc
  | read
  deriving DecidableEq

/-- The counter object; `INC` returns `ack` (encoded as `0`). -/
abbrev counterObj : ObjSpec where
  State := ℕ
  Op := COp
  Resp := ℕ
  init := 0
  δ s o := match o with
    | .inc => (s + 1, 0)
    | .read => (s, s)

/-- Operations of the nested recoverable read/write objects (Algorithm 1). -/
inductive IOp where
  | read
  | write (v : ℕ)
  deriving DecidableEq

/-- A frame of a nested Algorithm 1 operation on `R[obj]`: line `pc`, local `temp`, and the
locals `flag, curr` of `WRITE.RECOVER`. -/
structure Inner where
  obj : Fin 2
  op : IOp
  pc : ℕ
  temp : ℕ
  flag : Bool
  curr : Option ℕ
  deriving DecidableEq

/-- A frame of a counter operation: line `pc`, `LI_p` (`li`, set at a crash), locals. -/
structure Outer where
  op : COp
  pc : ℕ
  li : ℕ
  temp : ℕ
  val : ℕ
  i : ℕ
  deriving DecidableEq

/-- Configurations: Algorithm 1's shared variables of `R[1], R[2]` (the register `R` and the
per-process pairs `S_p`), the counter's `Resp_p`, the frames of each process and the counter
history (without crash/recovery steps). -/
structure Cfg where
  R : Fin 2 → ℕ
  S : Fin 2 → Fin 2 → Bool × Option ℕ
  Resp : Fin 2 → ℕ
  outer : Fin 2 → Option Outer
  inner : Fin 2 → Option Inner
  hist : List (Label (Fin 2) counterObj)

/-- Initially all registers are `0` and `S_p = <0, null>`. -/
def init : Cfg := ⟨fun _ => 0, fun _ _ => (false, none), fun _ => 0, fun _ => none, fun _ => none, []⟩

/-- Events. -/
inductive Ev where
  | inv (p : Fin 2) (o : COp)
  | step (p : Fin 2)
  | crash (p : Fin 2)

/-- The caller continues after a nested call returned `r`. -/
def resume (o : Outer) (r : ℕ) : Outer :=
  match o.pc with
  | 2 => { o with temp := r, pc := 3 }          -- INC line 2: temp ← R[p].READ
  | 4 => { o with pc := 5 }                     -- INC line 4: R[p].WRITE(temp)
  | 14 => { o with val := o.val + r, i := o.i + 1, pc := 13 }  -- READ line 14
  | _ => o

/-- A frame of Algorithm 1 for `R[i]`, starting at line `pc`. -/
def frame (i : Fin 2) (op : IOp) (pc : ℕ) : Inner := ⟨i, op, pc, 0, false, none⟩

/-- One step of process `p`. -/
def step (C : Cfg) (p : Fin 2) : Cfg :=
  match C.inner p with
  | some f =>
    let setF (f' : Inner) : Cfg := { C with inner := Function.update C.inner p (some f') }
    let retF (r : ℕ) : Cfg :=
      { C with inner := Function.update C.inner p none,
               outer := Function.update C.outer p ((C.outer p).map (resume · r)) }
    match f.op, f.pc with
    -- READ (lines 8-9) and READ.RECOVER (lines 19-20)
    | .read, 8 => setF { f with temp := C.R f.obj, pc := 9 }
    | .read, 9 => retF f.temp
    | .read, 19 => setF { f with temp := C.R f.obj, pc := 20 }
    | .read, 20 => retF f.temp
    -- WRITE (lines 2-6)
    | .write _, 2 => setF { f with temp := C.R f.obj, pc := 3 }
    | .write _, 3 => { C with S := Function.update C.S f.obj
                                 (Function.update (C.S f.obj) p (true, some f.temp)),
                              inner := Function.update C.inner p (some { f with pc := 4 }) }
    | .write v, 4 => { C with R := Function.update C.R f.obj v,
                              inner := Function.update C.inner p (some { f with pc := 5 }) }
    | .write v, 5 => { C with S := Function.update C.S f.obj
                                 (Function.update (C.S f.obj) p (false, some v)),
                              inner := Function.update C.inner p (some { f with pc := 6 }) }
    | .write _, 6 => retF 0
    -- WRITE.RECOVER (lines 11-17)
    | .write _, 11 => setF { f with flag := (C.S f.obj p).1, curr := (C.S f.obj p).2, pc := 12 }
    | .write v, 12 => setF { f with pc := if f.flag = false ∧ f.curr ≠ some v then 2 else 14 }
    | .write _, 14 =>
      setF { f with pc := if f.flag = true ∧ f.curr = some (C.R f.obj) then 2 else 16 }
    | .write v, 16 => { C with S := Function.update C.S f.obj
                                  (Function.update (C.S f.obj) p (false, some v)),
                               inner := Function.update C.inner p (some { f with pc := 17 }) }
    | .write _, 17 => retF 0
    | _, _ => C
  | none =>
    match C.outer p with
    | none => C
    | some o =>
      let setO (o' : Outer) : Cfg := { C with outer := Function.update C.outer p (some o') }
      let call (f : Inner) : Cfg := { C with inner := Function.update C.inner p (some f) }
      let ret (r : ℕ) : Cfg :=
        { C with outer := Function.update C.outer p none, hist := C.hist ++ [.ret p r] }
      match o.op, o.pc with
      -- INC (lines 2-5)
      | .inc, 2 => call (frame p .read 8)
      | .inc, 3 => setO { o with temp := o.temp + 1, pc := 4 }
      | .inc, 4 => call (frame p (.write o.temp) 2)
      | .inc, 5 => ret 0
      -- INC.RECOVER (lines 7-10)
      | .inc, 7 => setO { o with pc := if o.li < 4 then 2 else 10 }
      | .inc, 10 => ret 0
      -- READ (lines 12-16): line 13 is the loop test, line 14 the nested call
      | .read, 12 => setO { o with val := 0, i := 0, pc := 13 }
      | .read, 13 => setO { o with pc := if o.i < 2 then 14 else 15 }
      | .read, 14 => call (frame ⟨o.i % 2, Nat.mod_lt _ (by norm_num)⟩ .read 8)
      | .read, 15 => { C with Resp := Function.update C.Resp p o.val,
                              outer := Function.update C.outer p (some { o with pc := 16 }) }
      | .read, 16 => ret o.val
      -- READ.RECOVER (line 18)
      | .read, 18 => setO { o with pc := 12 }
      | _, _ => C

/-- A crash of `p`: all volatile variables are reset (to `0`). If a nested recoverable
operation is pending, the system invokes its recovery function (with the same arguments) and the
caller's frame keeps only its return address; otherwise the counter operation's recovery
function is invoked with `LI_p` = the line `p` was about to execute. -/
def crash (C : Cfg) (p : Fin 2) : Cfg :=
  match C.inner p with
  | some f =>
    { C with
      inner := Function.update C.inner p
        (some (match f.op with
          | .read => frame f.obj .read 19
          | .write v => frame f.obj (.write v) 11)),
      outer := Function.update C.outer p
        ((C.outer p).map fun o => { o with temp := 0, val := 0, i := 0 }) }
  | none =>
    match C.outer p with
    | none => C
    | some o =>
      let o' : Outer := ⟨o.op, match o.op with | .inc => 7 | .read => 18, o.pc, 0, 0, 0⟩
      { C with outer := Function.update C.outer p (some o') }

/-- One event. -/
def ev (C : Cfg) : Ev → Cfg
  | .inv p o =>
    match C.outer p with
    | none =>
      let o' : Outer := ⟨o, match o with | .inc => 2 | .read => 12, 0, 0, 0, 0⟩
      { C with outer := Function.update C.outer p (some o'), hist := C.hist ++ [.inv p o] }
    | some _ => C
  | .step p => step C p
  | .crash p => crash C p

/-- Running a list of events. -/
def run (C : Cfg) (es : List Ev) : Cfg := es.foldl ev C

/-! ### The counterexamples -/

/-- Process 0 increments; then process 1 reads, crashing inside the nested `R[2].READ`. -/
def schedRead : List Ev :=
  [.inv 0 .inc] ++ List.replicate 15 (.step 0) ++
  [.inv 1 .read] ++ List.replicate 8 (.step 1) ++ [.crash 1] ++ List.replicate 20 (.step 1)

/-- Process 0 crashes in `INC` about to execute line 4; then process 1 reads. -/
def schedInc : List Ev :=
  [.inv 0 .inc] ++ List.replicate 4 (.step 0) ++ [.crash 0] ++ List.replicate 5 (.step 0) ++
  [.inv 1 .read] ++ List.replicate 20 (.step 1)

lemma hist_schedRead :
    (run init schedRead).hist = [.inv 0 .inc, .ret 0 0, .inv 1 .read, .ret 1 0] := by
  rfl

/-- The crash in `schedRead` happens inside the nested `R[2].READ` (after its read of `R`), and
the values written to the read/write objects are distinct (Algorithm 1's assumption). -/
lemma schedRead_crash_inside :
    (run init ([.inv 0 .inc] ++ List.replicate 15 (.step 0) ++
      [.inv 1 .read] ++ List.replicate 8 (.step 1))).inner 1 = some ⟨1, .read, 9, 0, false, none⟩ ∧
    (run init ([.inv 0 .inc] ++ List.replicate 15 (.step 0))).R = ![1, 0] := by
  refine ⟨by decide, ?_⟩
  funext i; fin_cases i <;> decide

lemma hist_schedInc :
    (run init schedInc).hist = [.inv 0 .inc, .ret 0 0, .inv 1 .read, .ret 1 0] := by
  rfl

/-- The crash in `schedInc` happens when process 0 is about to execute line 4 of `INC` (no
nested operation pending). -/
lemma schedInc_crash_at_line4 :
    ((run init ([.inv 0 .inc] ++ List.replicate 4 (.step 0))).outer 0).map Outer.pc = some 4 ∧
    (run init ([.inv 0 .inc] ++ List.replicate 4 (.step 0))).inner 0 = none := by
  decide

/-- The history "`INC` by 0 completes, then `READ` by 1 returns 0" is not linearizable. -/
lemma not_linearizable :
    ¬ ∃ L, IsLinearization ([.inv 0 .inc, .ret 0 0, .inv 1 .read, .ret 1 0] :
      List (Label (Fin 2) counterObj)) L := by
  rintro ⟨L, hL⟩
  set α : List (Label (Fin 2) counterObj) := [.inv 0 .inc, .ret 0 0, .inv 1 .read, .ret 1 0]
  have hc0 : Completed α (0, 0) := by unfold Completed respsOf; decide
  have hc1 : Completed α (1, 0) := by unfold Completed respsOf; decide
  have hpre : Precedes α (0, 0) (1, 0) :=
    ⟨[.inv 0 .inc, .ret 0 0], [.inv 1 .read, .ret 1 0], rfl,
      by unfold Completed respsOf; decide, by unfold Invoked opsOf; decide⟩
  have hops0 : opsOf α 0 = [.inc] := rfl
  have hops1 : opsOf α 1 = [.read] := rfl
  have h0 := hL.complete _ hc0
  have h1 := hL.complete _ hc1
  have hsub := hL.realtime _ _ hpre h1
  -- every entry of `L` is one of the two operations
  have hmem : ∀ y ∈ L, y = ((0, 0), .inc) ∨ y = ((1, 0), .read) := by
    intro y hy
    have h := hL.op_eq y hy
    obtain ⟨⟨a, k⟩, o⟩ := y
    fin_cases a
    · simp only [opOf, Fin.zero_eta, Fin.isValue, hops0] at h
      rcases k with _ | k
      · simp at h; simp [h]
      · simp at h
    · simp only [opOf, Fin.mk_one, Fin.isValue, hops1] at h
      rcases k with _ | k
      · simp at h; simp [h]
      · simp at h
  -- so `L` is exactly `[INC, READ]`
  have hL2 : L = [((0, 0), .inc), ((1, 0), .read)] := by
    have hnd := hL.nodup
    rcases L with _ | ⟨y₁, _ | ⟨y₂, _ | ⟨y₃, L⟩⟩⟩
    · simp at h0
    · rcases hmem y₁ (by simp) with rfl | rfl <;> simp_all
    · rcases hmem y₁ (by simp) with rfl | rfl <;> rcases hmem y₂ (by simp) with rfl | rfl <;>
        simp_all
      exact absurd hsub (by decide)
    · exfalso
      rcases hmem y₁ (by simp) with rfl | rfl <;> rcases hmem y₂ (by simp) with rfl | rfl <;>
        rcases hmem y₃ (by simp) with rfl | rfl <;> simp_all
  have hseq := hL.seq
  rw [hL2] at hseq
  simp only [SeqOK] at hseq
  have := hseq.2.1 0 (by decide)
  simp at this

/-- **Algorithm 4 does not satisfy NRL** (counter `READ`): in the execution `schedRead` (a crash
inside the nested `R[2].READ`), the counter's history — `INC` completes, then `READ` returns `0`
— is not linearizable. -/
theorem read_not_nrl : ¬ ∃ L, IsLinearization (run init schedRead).hist L := by
  rw [hist_schedRead]; exact not_linearizable

/-- **`INC.RECOVER`'s test `LI_p < 4` is off by one**: in the execution `schedInc` (a crash
just before line 4 of `INC`), the recovered `INC` returns without incrementing, and the counter's
history is not linearizable. -/
theorem inc_recover_not_nrl : ¬ ∃ L, IsLinearization (run init schedInc).hist L := by
  rw [hist_schedInc]; exact not_linearizable

end Podc.NestingSafeRecoverable.Alg4
