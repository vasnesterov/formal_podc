import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Logic.Function.Basic

/-!
# The algorithm family `A_f` of Hendler (PODC 2016), Section 4 — a concrete step model

We model Algorithm 1 ("Pseudo-code for reader-writer algorithm `A_f`") of
D. Hendler, *On the Complexity of Reader-Writer Locks*, PODC 2016, as a deterministic
interleaving transition system.

## Model

* **Asynchronous shared memory, no failures.** A configuration is a `State`; a step is taken by a
  single process chosen by the scheduler (`Who`), and every step performs at most one shared-memory
  access, exactly as in the pseudo-code. The scheduler is arbitrary (`Reachable` quantifies over
  all interleavings).
* **Shared objects.** `C[i]`, `W[i]` are counters with atomic `add` and `read` (as the paper
  assumes, line 1); `WSIG[i]` and `RSIG` are read/write/CAS registers holding pairs
  `(sequence number, tag)`.
* **One writer.** The writers' lock `WL` (lines 6, 27) only provides mutual exclusion among
  writers (Observation 4); with a single writer it is a no-op and is omitted. Consequently `WSEQ`
  (line 3) is only accessed by the writer and is kept as a writer-local copy `wseq`.
* **Groups.** Line 30 assigns reader `p` to group `⌊p/f(n)⌋` (the intended group is `⌊p/K⌋`,
  `K = ⌈n/f(n)⌉`). We allow an arbitrary static partition `grp : Fin n → Fin G` into `G = f(n)`
  groups, which covers both.
* **Variants.** Two lines of the paper are parameters:
  - `ReadOrder` — the evaluation order of the two reads in line 51
    (`if C[i].read() = W[i].read()`): `cw` (literal, left to right: `C` first) or `wc`
    (`W` first, the repaired version);
  - `Line47` — line 47 reads `else if op = WAIT` (`op`, literal: the opcode read in line 32 of the
    entry section) or `else if op' = WAIT` (`op'`, the opcode read in line 41; intended).
* **Program counters.** `pc = cs` means "in the critical section"; the step taken from `cs`
  executes the first line of the exit section (line 25 for the writer, line 40 for a reader).
  The step taken from `rem` starts a passage (no memory access). Line 51 is split in two steps
  `l51a` / `l51b` (two reads); `ret36` records whether `HelpWCS` was called from line 35 (then it
  returns to line 36) or from line 48 (then the passage ends).
-/

namespace Podc.RWLockRMRTradeoff.Alg

/-- Tags stored in `WSIG[i]` (line 4): `⊥`, `PROCEED`, `WAIT`, `CS`. -/
inductive WTag
  | bot | proceed | wait | cs
  deriving DecidableEq, Repr

/-- Opcodes stored in `RSIG` (line 4): `NOP`, `PREENTRY`, `WAIT`. -/
inductive ROp
  | nop | preentry | wait
  deriving DecidableEq, Repr

/-- Evaluation order of the two reads in line 51. -/
inductive ReadOrder
  /-- literal left-to-right order: `C[i].read()` first, then `W[i].read()` -/
  | cw
  /-- repaired order: `W[i].read()` first, then `C[i].read()` -/
  | wc
  deriving DecidableEq, Repr

/-- The variable tested in line 47. -/
inductive Line47
  /-- literal: `else if op = WAIT` (`op` was read in line 32) -/
  | op
  /-- repaired: `else if op' = WAIT` (`op'` was read in line 41) -/
  | op'
  deriving DecidableEq, Repr

/-- The value returned by the first read of line 51, given the values of `C[i]` and `W[i]`. -/
def ReadOrder.first : ReadOrder → ℕ → ℕ → ℕ
  | .cw, c, _ => c
  | .wc, _, w => w

/-- The value returned by the second read of line 51, given the values of `C[i]` and `W[i]`. -/
def ReadOrder.second : ReadOrder → ℕ → ℕ → ℕ
  | .cw, _, w => w
  | .wc, c, _ => c

/-- The opcode tested in line 47, given `op` (line 32) and `op'` (line 41). -/
def Line47.tested : Line47 → ROp → ROp → ROp
  | .op, o, _ => o
  | .op', _, o' => o'

/-- Writer program counter (`G` = number of groups `f(n)`); `i` is the loop index. -/
inductive WPc (G : ℕ)
  | rem
  | l8 (i : Fin G)
  | l11
  | l13 (i : Fin G)
  | l14 (i : Fin G)
  | l16 (i : Fin G)
  | l18
  | l20 (i : Fin G)
  | l21 (i : Fin G)
  /-- in the critical section; the next step executes line 25 -/
  | cs
  | l26
  deriving DecidableEq, Repr

/-- Reader program counter. -/
inductive RPc
  | rem | l31 | l32 | l34 | l51a | l51b | l52 | l36 | l37
  /-- in the critical section; the next step executes line 40 -/
  | cs
  | l41 | l43 | l44
  deriving DecidableEq, Repr

/-- Local state of a reader. -/
structure RLocal where
  pc : RPc
  /-- `seq`, `op`: read from `RSIG` in line 32 -/
  seq : ℕ
  op : ROp
  /-- `seq'`, `op'`: read from `RSIG` in line 41 -/
  seq' : ℕ
  op' : ROp
  /-- argument of the current `HelpWCS` call -/
  hseq : ℕ
  /-- `HelpWCS` was called from line 35 (`true`) or line 48 (`false`) -/
  ret36 : Bool
  /-- value returned by the first read of line 51 -/
  tmp : ℕ
  deriving DecidableEq, Repr

/-- Initial local state of a reader. -/
def RLocal.init : RLocal := ⟨.rem, 0, .nop, 0, .nop, 0, false, 0⟩

/-- Local state of the (single) writer. -/
structure WLocal (G : ℕ) where
  pc : WPc G
  /-- the writer's copy of `WSEQ` (line 3) -/
  wseq : ℕ
  deriving DecidableEq, Repr

/-- A configuration of `A_f` with `n` readers, `G` groups and one writer. -/
structure State (n G : ℕ) where
  C : Fin G → ℕ
  W : Fin G → ℕ
  wsig : Fin G → ℕ × WTag
  rsig : ℕ × ROp
  w : WLocal G
  r : Fin n → RLocal

/-- Parameters of the model: the two variants and the group assignment. -/
structure Cfg (n G : ℕ) where
  order : ReadOrder
  l47 : Line47
  grp : Fin n → Fin G

variable {n G : ℕ}

/-- The initial configuration (lines 1, 3, 4). -/
def init : State n G :=
  ⟨fun _ => 0, fun _ => 0, fun _ => (0, .bot), (0, .nop), ⟨.rem, 0⟩, fun _ => RLocal.init⟩

/-- First loop index (`none` if there are no groups). -/
def firstIdx (G : ℕ) : Option (Fin G) := if h : 0 < G then some ⟨0, h⟩ else none

/-- Next loop index (`none` at the end of the loop). -/
def nextIdx (i : Fin G) : Option (Fin G) := if h : i.1 + 1 < G then some ⟨i.1 + 1, h⟩ else none

/-- Move to loop body `body i` for the given index, or to `after` when the loop is finished. -/
def loopTo (k : Option (Fin G)) (body : Fin G → WPc G) (after : WPc G) : WPc G :=
  match k with
  | some i => body i
  | none => after

/-- One step of the writer (lines 5–28). -/
def wstep (s : State n G) : State n G :=
  let ws := s.w.wseq
  match s.w.pc with
  | .rem => { s with w := ⟨loopTo (firstIdx G) .l8 .l11, ws⟩ }
  | .l8 i => { s with wsig := Function.update s.wsig i (ws, .bot),
                      w := ⟨loopTo (nextIdx i) .l8 .l11, ws⟩ }
  | .l11 => { s with rsig := (ws, .preentry), w := ⟨loopTo (firstIdx G) .l13 .l18, ws⟩ }
  | .l13 i => { s with w := ⟨if 0 < s.C i then .l14 i else .l16 i, ws⟩ }
  | .l14 i => if s.wsig i = (ws, .proceed) then { s with w := ⟨.l16 i, ws⟩ } else s
  | .l16 i => { s with wsig := Function.update s.wsig i (ws, .wait),
                       w := ⟨loopTo (nextIdx i) .l13 .l18, ws⟩ }
  | .l18 => { s with rsig := (ws, .wait), w := ⟨loopTo (firstIdx G) .l20 .cs, ws⟩ }
  | .l20 i => { s with w := ⟨if 0 < s.C i then .l21 i else loopTo (nextIdx i) .l20 .cs, ws⟩ }
  | .l21 i => if s.wsig i = (ws, .cs) then { s with w := ⟨loopTo (nextIdx i) .l20 .cs, ws⟩ }
      else s
  | .cs => { s with w := ⟨.l26, ws + 1⟩ }
  | .l26 => { s with rsig := (ws, .nop), w := ⟨.rem, ws⟩ }

/-- `CAS(x, a, b)`: the new value of a register holding `x`. -/
def cas {α : Type} [DecidableEq α] (x a b : α) : α := if x = a then b else x

/-- One step of reader `p` (lines 29–54). -/
def rstep (cfg : Cfg n G) (p : Fin n) (s : State n G) : State n G :=
  let g := cfg.grp p
  let l := s.r p
  let set (l' : RLocal) (s' : State n G) : State n G := { s' with r := Function.update s.r p l' }
  match l.pc with
  | .rem => set { l with pc := .l31 } s
  | .l31 => set { l with pc := .l32 } { s with C := Function.update s.C g (s.C g + 1) }
  | .l32 =>
      set { l with pc := (if s.rsig.2 = .wait then .l34 else .cs), seq := s.rsig.1, op := s.rsig.2 } s
  | .l34 => set { l with pc := .l51a, hseq := l.seq, ret36 := true }
      { s with W := Function.update s.W g (s.W g + 1) }
  | .l51a => set { l with pc := .l51b, tmp := cfg.order.first (s.C g) (s.W g) } s
  | .l51b =>
      set { l with
        pc := if cfg.order.second (s.C g) (s.W g) = l.tmp then .l52
          else if l.ret36 then .l36 else .rem } s
  | .l52 => set { l with pc := if l.ret36 then .l36 else .rem }
      { s with wsig := Function.update s.wsig g (cas (s.wsig g) (l.hseq, .wait) (l.hseq, .cs)) }
  | .l36 => if s.rsig ≠ (l.seq, .wait) then set { l with pc := .l37 } s else s
  | .l37 => set { l with pc := .cs } { s with W := Function.update s.W g (s.W g - 1) }
  | .cs => set { l with pc := .l41 } { s with C := Function.update s.C g (s.C g - 1) }
  | .l41 =>
      set { l with
        seq' := s.rsig.1, op' := s.rsig.2, hseq := s.rsig.1, ret36 := false,
        pc := if s.rsig.2 = .preentry then .l43 else if cfg.l47.tested l.op s.rsig.2 = .wait then .l51a else .rem } s
  | .l43 => set { l with pc := if s.C g = 0 then .l44 else .rem } s
  | .l44 => set { l with pc := .rem }
      { s with wsig := Function.update s.wsig g (cas (s.wsig g) (l.seq', .bot) (l.seq', .proceed)) }

/-- Who takes the next step. -/
inductive Who (n : ℕ)
  | writer
  | reader (p : Fin n)
  deriving DecidableEq, Repr

/-- The step of process `who`. -/
def step (cfg : Cfg n G) : Who n → State n G → State n G
  | .writer => wstep
  | .reader p => rstep cfg p

/-- Configurations reachable from `init` under an arbitrary scheduler. -/
inductive Reachable (cfg : Cfg n G) : State n G → Prop
  | init : Reachable cfg init
  | step {s : State n G} (who : Who n) : Reachable cfg s → Reachable cfg (step cfg who s)

/-- Run a finite schedule. -/
def run (cfg : Cfg n G) (sched : List (Who n)) (s : State n G) : State n G :=
  sched.foldl (fun s who => step cfg who s) s

/-- The infinite execution from `s` under the schedule `σ`: configuration after `k` steps. -/
def exec (cfg : Cfg n G) (σ : ℕ → Who n) (s : State n G) : ℕ → State n G
  | 0 => s
  | k + 1 => step cfg (σ k) (exec cfg σ s k)

theorem reachable_run (cfg : Cfg n G) {s : State n G} (hs : Reachable cfg s)
    (sched : List (Who n)) : Reachable cfg (run cfg sched s) := by
  induction sched generalizing s with
  | nil => exact hs
  | cons who l ih => exact ih (hs.step who)

theorem reachable_exec (cfg : Cfg n G) {s : State n G} (hs : Reachable cfg s)
    (σ : ℕ → Who n) (k : ℕ) : Reachable cfg (exec cfg σ s k) := by
  induction k with
  | zero => exact hs
  | succ k ih => exact ih.step _

/-- The writer is in the critical section. -/
def State.writerInCS (s : State n G) : Prop := s.w.pc = .cs

/-- Reader `p` is in the critical section. -/
def State.readerInCS (s : State n G) (p : Fin n) : Prop := (s.r p).pc = .cs

/-- **Mutual Exclusion** (Section 2.1) for the single-writer model: never a writer and a reader
in the critical section simultaneously. (Readers may share the CS; writers exclude each other via
`WL`, Observation 4.) -/
def MutualExclusion (cfg : Cfg n G) : Prop :=
  ∀ s, Reachable cfg s → s.writerInCS → ∀ p, ¬ s.readerInCS p

end Podc.RWLockRMRTradeoff.Alg
