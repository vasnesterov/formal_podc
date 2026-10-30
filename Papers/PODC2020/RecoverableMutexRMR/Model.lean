import Mathlib

/-!
# The recoverable mutual exclusion algorithm of Chan and Woelfel (PODC 2020)

David Yu Cheng Chan, Philipp Woelfel. *Recoverable Mutual Exclusion with Constant Amortized RMR
Complexity from Standard Primitives.* PODC 2020, Figure 1.

```
Shared: FAI C, D (init 0); CAS A[1..∞] (init 0); CAS W[1..n] (init (0,false));
        CAS Exit[1..n] (init false); CAS Token (init 0).
Enter():  2 repeat  3 if W[p].read() = (0,false) then  4 c ← 1 + C.FAI()
                                                         5 W[p].CAS((0,false),(c,false))
          6 until Waiting_Room()          7 enter the critical section
Exit():   9 Exit[p].write(true)  10 W[p].write(0,false)  11 Move_Token()
         12 Exit[p].write(false) 13 return to the remainder section
Recover(): 15 D.FAI()  16 if Exit[p].read() then 17 jump to Exit()
           18 (−,b) ← W[p].read()  19 if b then 20 enter the critical section  21 jump to Enter()
Waiting_Room(): 23 (w,−) ← W[p].read()  24 A[w].CAS(0,p)  25 if A[w].read() ≠ p then
                26 W[p].write(0,false)  27 return false
                28 D.FAI()  29 Move_Token()  30 repeat 31 until W[p].read() = (w,true)  32 return true
Move_Token(): 34 ℓ ← Token.read()  35 d ← D.read()  36 c ← C.read()  37 if ℓ < c then
              38 p' ← A[ℓ+1].read()  39 if p' > 0 then
              40   W[p'].CAS((ℓ+1,false),(ℓ+1,true))
              41   if W[p'].read() ≠ (ℓ+1,true) and p = p' then
              42     if Token.CAS(ℓ,ℓ+1) then 43 Move_Token()
              44 else 45 if c ≤ d then 46 A[ℓ+1].CAS(0,−1)
              47   if A[ℓ+1].read() = −1 then 48 if Token.CAS(ℓ,ℓ+1) then 49 Move_Token()
              50 return
```

## Model

* Asynchronous shared memory, processes of an arbitrary finite type `P` (the paper's `{1,…,n}`).
* Every step of a process performs exactly one shared-memory operation (or, for `rem`/`cs`, the
  invocation of `Enter()`/`Exit()`), together with the local computation that follows it; the
  program counter `PC` designates the next operation and carries the local variables.
  Lines 6–7, 13, 17, 19–21, 27, 32, 37, 39, 43–45, 49, 50 are local and merged into the
  preceding step. The recursive calls of `Move_Token()` (lines 43, 49) are tail calls: they are
  a jump back to line 34 with the same return address (`Ret`).
* `A[c]` holds `Slot.empty` (0), `Slot.claimed q` (the id `q > 0`) or `Slot.skipped` (−1).
* A crash of a process outside the remainder section resets its local state (its program
  counter) and starts `Recover()` (line 15); the shared memory is unaffected. A crash in the
  remainder section has no effect (the paper calls `Recover()` iff the process crashes outside
  the remainder section).
* An execution is determined by its schedule `e : ℕ → Ev P` (step or crash of a process); every
  schedule is admissible (the step relation is total and deterministic).
* *Ghost state* (`Ghost`, never read by the algorithm) records the owners of tickets, the latest
  ticket `cur p` of each process and the bookkeeping needed for the potential arguments
  (Lemmas 2.2–2.3, 2.10).
-/

namespace Podc.RecoverableMutexRMR

/-- Contents of an entry `A[c]` of the queue: `0`, a process id, or `−1`. -/
inductive Slot (P : Type) where
  /-- `0`: nobody claimed this ticket yet. -/
  | empty
  /-- process `q` claimed the ticket (line 24). -/
  | claimed (q : P)
  /-- `−1`: the ticket was skipped (line 46). -/
  | skipped
  deriving DecidableEq

/-- Return address of a `Move_Token()` call: line 30 of `Waiting_Room()` (with the ticket `w`
read at line 23) or line 12 of `Exit()`. -/
inductive Ret where
  | wr (w : ℕ)
  | ex
  deriving DecidableEq

/-- Program counters (the next shared-memory operation) with the local variables. -/
inductive PC (P : Type) where
  /-- remainder section -/
  | rem
  /-- line 3: read `W[p]` -/
  | l3
  /-- line 4: `C.FAI()` -/
  | l4
  /-- line 5: `W[p].CAS((0,false),(c,false))` -/
  | l5 (c : ℕ)
  /-- line 23: read `W[p]` -/
  | w23
  /-- line 24: `A[w].CAS(0,p)` -/
  | w24 (w : ℕ)
  /-- line 25: read `A[w]` -/
  | w25 (w : ℕ)
  /-- line 26: `W[p].write(0,false)` -/
  | w26
  /-- line 28: `D.FAI()` -/
  | w28 (w : ℕ)
  /-- line 31: read `W[p]` (busy wait) -/
  | w31 (w : ℕ)
  /-- critical section -/
  | cs
  /-- line 9: `Exit[p].write(true)` -/
  | x9
  /-- line 10: `W[p].write(0,false)` -/
  | x10
  /-- line 12: `Exit[p].write(false)` -/
  | x12
  /-- line 15: `D.FAI()` -/
  | r15
  /-- line 16: read `Exit[p]` -/
  | r16
  /-- line 18: read `W[p]` -/
  | r18
  /-- line 34: read `Token` -/
  | m34 (r : Ret)
  /-- line 35: read `D` -/
  | m35 (r : Ret) (ℓ : ℕ)
  /-- line 36: read `C` -/
  | m36 (r : Ret) (ℓ d : ℕ)
  /-- line 38: read `A[ℓ+1]` -/
  | m38 (r : Ret) (ℓ c d : ℕ)
  /-- line 40: `W[q].CAS((ℓ+1,false),(ℓ+1,true))` -/
  | m40 (r : Ret) (ℓ : ℕ) (q : P)
  /-- line 41: read `W[q]` -/
  | m41 (r : Ret) (ℓ : ℕ) (q : P)
  /-- line 42: `Token.CAS(ℓ,ℓ+1)` -/
  | m42 (r : Ret) (ℓ : ℕ)
  /-- line 46: `A[ℓ+1].CAS(0,−1)` -/
  | m46 (r : Ret) (ℓ : ℕ)
  /-- line 47: read `A[ℓ+1]` -/
  | m47 (r : Ret) (ℓ : ℕ)
  /-- line 48: `Token.CAS(ℓ,ℓ+1)` -/
  | m48 (r : Ret) (ℓ : ℕ)
  deriving DecidableEq

/-- Where `Move_Token()` returns to. -/
def Ret.pc {P : Type} : Ret → PC P
  | .wr w => .w31 w
  | .ex => .x12

/-- Configurations: the shared variables and the program counters. -/
structure Cfg (P : Type) where
  /-- FAI object `C` -/
  C : ℕ
  /-- FAI object `D` -/
  D : ℕ
  /-- CAS object `Token` -/
  T : ℕ
  /-- the queue `A[1..∞]` (`A 0` is never accessed) -/
  A : ℕ → Slot P
  /-- `W[p] = (ticket, may enter)` -/
  W : P → ℕ × Bool
  /-- `Exit[p]` -/
  X : P → Bool
  /-- program counters (with local variables) -/
  pc : P → PC P

variable {P : Type} [DecidableEq P]

/-- The initial configuration: everybody in the remainder section. -/
def Cfg.init : Cfg P where
  C := 0
  D := 0
  T := 0
  A _ := .empty
  W _ := (0, false)
  X _ := false
  pc _ := .rem

/-- Change the program counter of `p`. -/
def Cfg.setPc (s : Cfg P) (p : P) (k : PC P) : Cfg P := { s with pc := Function.update s.pc p k }

/-- One step of process `p` (its next shared-memory operation). -/
def Cfg.step (s : Cfg P) (p : P) : Cfg P :=
  match s.pc p with
  | .rem => s.setPc p .l3
  | .l3 => s.setPc p (if s.W p = (0, false) then .l4 else .w23)
  | .l4 => { s with C := s.C + 1, pc := Function.update s.pc p (.l5 (s.C + 1)) }
  | .l5 c => { s with
      W := if s.W p = (0, false) then Function.update s.W p (c, false) else s.W
      pc := Function.update s.pc p .w23 }
  | .w23 => s.setPc p (.w24 (s.W p).1)
  | .w24 w => { s with
      A := if s.A w = .empty then Function.update s.A w (.claimed p) else s.A
      pc := Function.update s.pc p (.w25 w) }
  | .w25 w => s.setPc p (if s.A w = .claimed p then .w28 w else .w26)
  | .w26 => { s with W := Function.update s.W p (0, false), pc := Function.update s.pc p .l3 }
  | .w28 w => { s with D := s.D + 1, pc := Function.update s.pc p (.m34 (.wr w)) }
  | .w31 w => s.setPc p (if s.W p = (w, true) then .cs else .w31 w)
  | .cs => s.setPc p .x9
  | .x9 => { s with X := Function.update s.X p true, pc := Function.update s.pc p .x10 }
  | .x10 => { s with W := Function.update s.W p (0, false), pc := Function.update s.pc p (.m34 .ex) }
  | .x12 => { s with X := Function.update s.X p false, pc := Function.update s.pc p .rem }
  | .r15 => { s with D := s.D + 1, pc := Function.update s.pc p .r16 }
  | .r16 => s.setPc p (if s.X p = true then .x9 else .r18)
  | .r18 => s.setPc p (if (s.W p).2 = true then .cs else .l3)
  | .m34 r => s.setPc p (.m35 r s.T)
  | .m35 r ℓ => s.setPc p (.m36 r ℓ s.D)
  | .m36 r ℓ d => s.setPc p (if ℓ < s.C then .m38 r ℓ s.C d else r.pc)
  | .m38 r ℓ c d => s.setPc p
      (match s.A (ℓ + 1) with
        | .claimed q => .m40 r ℓ q
        | _ => if c ≤ d then .m46 r ℓ else r.pc)
  | .m40 r ℓ q => { s with
      W := if s.W q = (ℓ + 1, false) then Function.update s.W q (ℓ + 1, true) else s.W
      pc := Function.update s.pc p (.m41 r ℓ q) }
  | .m41 r ℓ q => s.setPc p (if s.W q ≠ (ℓ + 1, true) ∧ p = q then .m42 r ℓ else r.pc)
  | .m42 r ℓ =>
      if s.T = ℓ then { s with T := ℓ + 1, pc := Function.update s.pc p (.m34 r) }
      else s.setPc p r.pc
  | .m46 r ℓ => { s with
      A := if s.A (ℓ + 1) = .empty then Function.update s.A (ℓ + 1) .skipped else s.A
      pc := Function.update s.pc p (.m47 r ℓ) }
  | .m47 r ℓ => s.setPc p (if s.A (ℓ + 1) = .skipped then .m48 r ℓ else r.pc)
  | .m48 r ℓ =>
      if s.T = ℓ then { s with T := ℓ + 1, pc := Function.update s.pc p (.m34 r) }
      else s.setPc p r.pc

/-- A crash of `p`: outside the remainder section, its local state is lost and it starts
`Recover()`. -/
def Cfg.crash (s : Cfg P) (p : P) : Cfg P :=
  if s.pc p = .rem then s else s.setPc p .r15

/-- Events of a schedule. -/
inductive Ev (P : Type) where
  | step (p : P)
  | crash (p : P)
  deriving DecidableEq

/-- The effect of an event. -/
def Cfg.next (s : Cfg P) : Ev P → Cfg P
  | .step p => s.step p
  | .crash p => s.crash p

/-- The execution of a schedule `e`: `exec e t` is the configuration after `t` events. -/
def exec (e : ℕ → Ev P) : ℕ → Cfg P
  | 0 => Cfg.init
  | t + 1 => (exec e t).next (e t)

@[simp] lemma exec_zero (e : ℕ → Ev P) : exec e 0 = Cfg.init := rfl
@[simp] lemma exec_succ (e : ℕ → Ev P) (t : ℕ) : exec e (t + 1) = (exec e t).next (e t) := rfl

/-! ### Sections of the mutual exclusion protocol -/

/-- `p` is in the critical section. -/
def Cfg.InCS (s : Cfg P) (p : P) : Prop := s.pc p = .cs

/-- `p` is in the remainder section. -/
def Cfg.InRem (s : Cfg P) (p : P) : Prop := s.pc p = .rem

/-- `p` is executing `Recover()`. -/
def PC.IsRecover {P : Type} : PC P → Prop
  | .r15 | .r16 | .r18 => True
  | _ => False

/-- `p` is executing `Exit()` (including the `Move_Token()` call of line 11). -/
def PC.IsExit {P : Type} : PC P → Prop
  | .x9 | .x10 | .x12 => True
  | .m34 .ex | .m35 .ex _ | .m36 .ex _ _ | .m38 .ex _ _ _ | .m40 .ex _ _ | .m41 .ex _ _
  | .m42 .ex _ | .m46 .ex _ | .m47 .ex _ | .m48 .ex _ => True
  | _ => False

/-- `p` is executing `Enter()` (including `Waiting_Room()` and its `Move_Token()` call). -/
def PC.IsEnter {P : Type} (k : PC P) : Prop :=
  k ≠ .rem ∧ k ≠ .cs ∧ ¬ k.IsRecover ∧ ¬ k.IsExit

/-! ### Ghost state -/

/-- Ghost variables (not read by the algorithm). -/
structure Ghost (P : Type) where
  /-- `own c`: the process that obtained ticket `c` at line 4 -/
  own : ℕ → Option P
  /-- the latest ticket of `p` (`c_{p,t}` of the paper; `0` if none) -/
  cur : P → ℕ
  /-- `p` has not incremented `D` (line 15 or 28) since it obtained `cur p` -/
  pend : P → Bool
  /-- `p` executed line 15 since it obtained `cur p` or since its last line 28 -/
  cr : P → Bool
  /-- tickets abandoned after a crash before they were claimed -/
  lost : Finset ℕ
  /-- number of crashes outside the remainder section so far -/
  ncr : ℕ

/-- Initial ghost state. -/
def Ghost.init : Ghost P where
  own _ := none
  cur _ := 0
  pend _ := false
  cr _ := false
  lost := ∅
  ncr := 0

/-- Ghost update for an event in configuration `s`. -/
def Ghost.next (s : Cfg P) (g : Ghost P) : Ev P → Ghost P
  | .crash p => if s.pc p = .rem then g else { g with ncr := g.ncr + 1 }
  | .step p =>
    match s.pc p with
    | .l4 => { g with
        own := Function.update g.own (s.C + 1) (some p)
        cur := Function.update g.cur p (s.C + 1)
        pend := Function.update g.pend p true
        cr := Function.update g.cr p false
        lost := if g.cr p = true ∧ s.A (g.cur p) = .empty then insert (g.cur p) g.lost else g.lost }
    | .w28 _ => { g with pend := Function.update g.pend p false, cr := Function.update g.cr p false }
    | .r15 => { g with pend := Function.update g.pend p false, cr := Function.update g.cr p true }
    | _ => g

/-- The ghost state along the execution of `e`. -/
def ghost (e : ℕ → Ev P) : ℕ → Ghost P
  | 0 => Ghost.init
  | t + 1 => (ghost e t).next (exec e t) (e t)

@[simp] lemma ghost_zero (e : ℕ → Ev P) : ghost e 0 = Ghost.init := rfl
@[simp] lemma ghost_succ (e : ℕ → Ev P) (t : ℕ) :
    ghost e (t + 1) = (ghost e t).next (exec e t) (e t) := rfl

end Podc.RecoverableMutexRMR
