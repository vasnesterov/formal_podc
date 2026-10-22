import Podc.Computability.Distributed.SharedMemory.WriteStrongLin

/-!
# Algorithm 1 (the game) over linearizable registers, against a strong adversary

Hadzilacos, Hu and Toueg, *On Register Linearizability and Termination*, PODC 2021, Section 3.

## The model

* `n` processes `Fin n`: the *hosts* `p₀`, `p₁` and the *players* `p₂, …, p_{n-1}`; three
  shared registers `R1`, `R2`, `C` (`Reg`) over the value type `Val` (`⊥`, pairs `[i, j]`,
  numbers, coin bits). Initial values (unspecified in the paper): `R1 = C = ⊥`, `R2 = 0`.
* **Registers are abstract and only linearizable.** A register operation is an invocation event
  `inv p x o` followed later by a response event `ret p x v`; between them other processes take
  steps. The responses are chosen by the adversary, subject to the requirement that the history of
  every register is linearizable (`LinRegs`) — CSLib's `IsLinearization` on the projection
  `hist x α` of the execution to register `x` (Herlihy–Wing linearizability; pending operations may
  or may not be linearized). This is the most permissive behaviour of a linearizable register
  implementation.
* **Processes** run the code of Algorithm 1 (`code`), one register operation or coin flip at a
  time; `procRun p α` replays the events of `p` in `α` (`none` if they do not follow the code).
  After returning (local state `done`), a process may keep taking `noop` steps (footnote 3).
* **Strong adversary.** The adversary is a function `σ : List (Ev n) → Ev n` choosing the next
  event from the whole execution so far (in particular from all previous coin flips). When it
  schedules a coin flip of `p₀`, the outcome is the next coin of the random sequence
  `ω : ℕ → Bool` (`genRun σ ω`); the value proposed by `σ` is ignored.

The theorems (Theorem 6: with merely linearizable registers some adversary keeps every process in
the game forever, for every coin sequence; Theorem 7: if `R1` is write strongly-linearizable the
game ends with probability 1) are stated and proved in `Theorem6.lean` / `Theorem7.lean`.
-/

namespace Podc.RegisterLinTermination.Game

open Cslib.SharedMemory

/-- Register values: `⊥`, pairs `[i, j]` (`i = false` is `0`, `i = true` is `1`), numbers (`R2`)
and coin bits (`C`). -/
inductive Val where
  | bot
  | pair (i : Bool) (j : ℕ)
  | num (k : ℕ)
  | bit (b : Bool)
  deriving DecidableEq

/-- The three shared registers. -/
inductive Reg where
  | r1
  | r2
  | c
  deriving DecidableEq

/-- Initial values of the registers. -/
def initVal : Reg → Val
  | .r1 => .bot
  | .r2 => .num 0
  | .c => .bot

/-- The register object `x` (CSLib sequential specification). -/
abbrev RegObj (x : Reg) : ObjSpec := register Val (initVal x)

/-- Events of an execution. -/
inductive Ev (n : ℕ) where
  /-- `p` invokes operation `o` on register `x`. -/
  | inv (p : Fin n) (x : Reg) (o : RWOp Val)
  /-- `p` receives the response `v` of its pending operation on register `x`. -/
  | ret (p : Fin n) (x : Reg) (v : Val)
  /-- `p` flips a coin with outcome `b`. -/
  | flip (p : Fin n) (b : Bool)
  /-- `p` takes a step after having returned. -/
  | noop (p : Fin n)
  deriving DecidableEq

/-- The process taking the event. -/
def Ev.proc {n : ℕ} : Ev n → Fin n
  | .inv p _ _ => p
  | .ret p _ _ => p
  | .flip p _ => p
  | .noop p => p

/-- Local states (program counters with the round `j` and local variables) of Algorithm 1.
Hosts: `h1` line 3, `h2` line 6, `h3` line 7, `h4` line 10, `h5` line 11. Players: `q1` line 19,
`q2` line 20, `q3` line 21, `q4` line 22, `q5` line 23, `q6` line 31, `q7` line 32, `q8` line 34.
`done`: returned (lines 16, 36). -/
inductive Loc where
  | h1 (j : ℕ)
  | h2 (j : ℕ)
  | h3 (j : ℕ) (b : Bool)
  | h4 (j : ℕ)
  | h5 (j : ℕ)
  | q1 (j : ℕ)
  | q2 (j : ℕ)
  | q3 (j : ℕ)
  | q4 (j : ℕ) (u₁ : Val)
  | q5 (j : ℕ) (u₁ u₂ : Val)
  | q6 (j : ℕ)
  | q7 (j : ℕ)
  | q8 (j : ℕ) (k : ℕ)
  | done

/-- What a process does next. -/
inductive Act where
  /-- invoke `o` on register `x`; continue with `k v` after the response `v` -/
  | invoke (x : Reg) (o : RWOp Val) (k : Val → Loc)
  /-- flip a coin; continue with `k b` -/
  | flip (k : Bool → Loc)
  /-- returned -/
  | done

/-- Numeric value of a register value (`R2` only ever holds numbers). -/
def Val.toNat : Val → ℕ
  | .num k => k
  | _ => 0

/-- The test of lines 24 and 27: `c ≠ ⊥`, `u₁ = [c, j]`, `u₂ = [1 - c, j]` (then also
`u₁, u₂ ≠ ⊥`). -/
def passes (j : ℕ) (u₁ u₂ c : Val) : Bool :=
  match c with
  | .bit b => decide (u₁ = .pair b j ∧ u₂ = .pair (!b) j)
  | _ => false

/-- The code of Algorithm 1 for process `p` (hosts `p.val < 2`, `[i, j]` with `i = p.val`). -/
def code (n : ℕ) (p : Fin n) : Loc → Act
  | .h1 j => .invoke .r1 (.write (.pair (decide (p.val = 1)) j))
      (fun _ => if p.val = 0 then .h2 j else .h4 j)
  | .h2 j => .flip (fun b => .h3 j b)
  | .h3 j b => .invoke .c (.write (.bit b)) (fun _ => .h4 j)
  | .h4 j => .invoke .r2 (.write (.num 0)) (fun _ => .h5 j)
  | .h5 j => .invoke .r2 .read (fun v => if v.toNat < n - 2 then .done else .h1 (j + 1))
  | .q1 j => .invoke .r1 (.write .bot) (fun _ => .q2 j)
  | .q2 j => .invoke .c (.write .bot) (fun _ => .q3 j)
  | .q3 j => .invoke .r1 .read (fun u₁ => .q4 j u₁)
  | .q4 j u₁ => .invoke .r1 .read (fun u₂ => .q5 j u₁ u₂)
  | .q5 j u₁ u₂ => .invoke .c .read (fun c => if passes j u₁ u₂ c then .q6 j else .done)
  | .q6 j => .invoke .r2 (.write (.num 0)) (fun _ => .q7 j)
  | .q7 j => .invoke .r2 .read (fun v => .q8 j (v.toNat + 1))
  | .q8 j k => .invoke .r2 (.write (.num k)) (fun _ => .q1 (j + 1))
  | .done => .done

/-- Initial local state: round `1`. -/
def initLoc {n : ℕ} (p : Fin n) : Loc := if p.val < 2 then .h1 1 else .q1 1

/-- Execution mode of a process: ready in local state `l`, or waiting for the response of an
operation on register `x`. -/
inductive Mode where
  | run (l : Loc)
  | wait (x : Reg) (k : Val → Loc)

/-- One event of process `p` (assumed to be `p`'s). -/
def pstep (n : ℕ) (p : Fin n) : Mode → Ev n → Option Mode
  | .run l, .inv _ x o => match code n p l with
    | .invoke x' o' k => if x = x' ∧ o = o' then some (.wait x k) else none
    | _ => none
  | .run l, .flip _ b => match code n p l with
    | .flip k => some (.run (k b))
    | _ => none
  | .run l, .noop _ => match code n p l with
    | .done => some (.run l)
    | _ => none
  | .wait x k, .ret _ x' v => if x = x' then some (.run (k v)) else none
  | _, _ => none

/-- Replay the events of `p` in `α`. -/
def procRun {n : ℕ} (p : Fin n) (α : List (Ev n)) : Option Mode :=
  (α.filter (fun e => decide (e.proc = p))).foldl
    (fun m e => m.bind (fun m => pstep n p m e)) (some (.run (initLoc p)))

/-- `α` follows the code of Algorithm 1 (with any coin outcomes). -/
def Valid {n : ℕ} (α : List (Ev n)) : Prop := ∀ p, (procRun p α).isSome

/-- The projection of an event to register `x`. -/
def Ev.toLabel {n : ℕ} (x : Reg) : Ev n → Option (Label (Fin n) (RegObj x))
  | .inv p y o => if y = x then some (.inv p o) else none
  | .ret p y v => if y = x then some (.ret p v) else none
  | _ => none

/-- The history of register `x` in `α`. -/
def hist {n : ℕ} (x : Reg) (α : List (Ev n)) : List (Label (Fin n) (RegObj x)) :=
  α.filterMap (Ev.toLabel x)

/-- The histories of all three registers are linearizable. -/
def LinRegs {n : ℕ} (α : List (Ev n)) : Prop :=
  ∀ x, ∃ L : List (OpId (Fin n) × RWOp Val), IsLinearization (hist x α) L

/-- The round of a local state (`0` for `done`). -/
def Loc.round : Loc → ℕ
  | .h1 j | .h2 j | .h3 j _ | .h4 j | .h5 j => j
  | .q1 j | .q2 j | .q3 j | .q4 j _ | .q5 j _ _ | .q6 j | .q7 j | .q8 j _ => j
  | .done => 0

/-- The round of a mode. -/
def Mode.round : Mode → ℕ
  | .run l => l.round
  | .wait _ k => (k .bot).round

/-- `p` has entered round `j` in `α` (executed line 1 or 17 with round `j`). -/
def Entered {n : ℕ} (p : Fin n) (j : ℕ) (α : List (Ev n)) : Prop :=
  ∃ β, β <+: α ∧ (procRun p β = some (.run (.h1 j)) ∨ procRun p β = some (.run (.q1 j)))

/-- `p` has returned in `α`. -/
def Returned {n : ℕ} (p : Fin n) (α : List (Ev n)) : Prop := procRun p α = some (.run .done)

/-! ## Strong adversaries -/

/-- Number of coin flips in `α`. -/
def flipCount {n : ℕ} (α : List (Ev n)) : ℕ :=
  α.countP (fun e => match e with | .flip _ _ => true | _ => false)

/-- The event actually taken when the adversary proposes `e` after `α`: coin flips get the next
coin of `ω`. -/
def coinify {n : ℕ} (ω : ℕ → Bool) (α : List (Ev n)) : Ev n → Ev n
  | .flip p _ => .flip p (ω (flipCount α))
  | e => e

/-- The first `m` events of the execution generated by the strong adversary `σ` with coins `ω`. -/
def genRun {n : ℕ} (σ : List (Ev n) → Ev n) (ω : ℕ → Bool) : ℕ → List (Ev n)
  | 0 => []
  | m + 1 => genRun σ ω m ++ [coinify ω (genRun σ ω m) (σ (genRun σ ω m))]

end Podc.RegisterLinTermination.Game
