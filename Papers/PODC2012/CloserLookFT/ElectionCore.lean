import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fintype.Card
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The almost-wait-free symmetric election algorithm (Section 2.1), as a transition system

Taubenfeld, *A closer look at fault tolerance*, PODC 2012 (full version of 22 Feb 2017),
Section 2.1. Process `p`'s program:

```
function election (e: object name) return:value in {0, 1};
1  e.turn := p;
2  for level := 1 to ⌈log n⌉ do
3    repeat
4      if e.done = 1 then return(0) fi;
5      if e.turn ≠ p then
6        for j := 1 to level − 1 do if e.V[j] = p then e.V[j] := 0 fi od;
7        return(0) fi
8    until e.V[level] = 0;
9    e.V[level] := p;
10   if e.turn ≠ p then
11     for j := 1 to level do if e.V[j] = p then e.V[j] := 0 fi od;
12     return(0) fi
13 od;
14 e.done := 1; return(1).
```

This file models one election object as a transition system over the shared registers
`turn`, `done`, `V[·]` (`EMem`) and the local states of the processes (`ELoc`); every step of a
process accesses exactly one register atomically. The CSLib `Impl` wrapper is in
`Election.lean`.

Modelling choices:
* levels are `0`-based: the paper's level `k` is our level `k - 1`, `V[k]` is `V (k - 1)`; the
  number of levels is a parameter `L` (the paper takes `L = ⌈log₂ n⌉`);
* the value `0` of a register is `none`, identifiers are elements of an arbitrary type `P` that
  are only compared for equality (the algorithm is *symmetric*);
* a `for` loop that clears `V[0..b-1]` is the sequence of states `clr k b j` (read `V[j]`) and
  `clw k b j` (write `V[j] := 0`), the `return(0)` after it is folded into the last step;
* the returned states `out r a w c` record ghost information about the process's past
  (`a` levels passed, registers `V[0..w-1]` written, registers below `c` cleared); the algorithm
  never reads it.
-/

namespace Podc.CloserLookFT

/-- The shared registers of one election object: `turn`, `done` and the array `V`
(`none` = the value `0`). -/
structure EMem (P : Type) where
  /-- `e.turn` -/
  turn : Option P
  /-- `e.done` -/
  done : Bool
  /-- `e.V[k + 1]` is `V k` -/
  V : ℕ → Option P

/-- The initial memory: all registers `0`. -/
def EMem.init (P : Type) : EMem P := ⟨none, false, fun _ => none⟩

/-- Local states (program counters) of a process. Levels are `0`-based. -/
inductive ELoc where
  /-- not invoked yet -/
  | idle
  /-- line 1: about to write `turn := p` -/
  | start
  /-- line 4 at level `k`: about to read `done` -/
  | rdone (k : ℕ)
  /-- line 5 at level `k`: about to read `turn` -/
  | rturn (k : ℕ)
  /-- line 8 at level `k`: about to read `V[k]` -/
  | rv (k : ℕ)
  /-- line 9 at level `k`: about to write `V[k] := p` -/
  | wv (k : ℕ)
  /-- line 10 at level `k`: about to read `turn` -/
  | rturn2 (k : ℕ)
  /-- lines 6/11 (level `k`): clearing `V[0..b-1]`, about to read `V[j]` -/
  | clr (k b j : ℕ)
  /-- lines 6/11 (level `k`): clearing `V[0..b-1]`, about to write `V[j] := 0` -/
  | clw (k b j : ℕ)
  /-- line 14: about to write `done := 1` -/
  | wdone
  /-- returned `r` (ghost: passed `a` levels, wrote `V[0..w-1]`, cleared below `c`) -/
  | out (r : Bool) (a w c : ℕ)
  deriving DecidableEq

variable {P : Type} [DecidableEq P]

/-- The state after finishing index `j - 1` of the clearing loop for `V[0..b-1]` at level `k`. -/
def nextClr (k b j : ℕ) : ELoc := if j < b then .clr k b j else .out false k b b

/-- One atomic step of process `p` (with `L` levels) in local state `l` and memory `m`. -/
def estep (L : ℕ) (p : P) (m : EMem P) : ELoc → EMem P × ELoc
  | .idle => (m, .idle)
  | .start => ({ m with turn := some p }, if 0 < L then .rdone 0 else .wdone)
  | .rdone k => (m, if m.done then .out false k k 0 else .rturn k)
  | .rturn k => (m, if m.turn = some p then .rv k else nextClr k k 0)
  | .rv k => (m, if m.V k = none then .wv k else .rdone k)
  | .wv k => ({ m with V := Function.update m.V k (some p) }, .rturn2 k)
  | .rturn2 k => (m, if m.turn = some p then (if k + 1 < L then .rdone (k + 1) else .wdone)
      else nextClr k (k + 1) 0)
  | .clr k b j => (m, if m.V j = some p then .clw k b j else nextClr k b (j + 1))
  | .clw k b j => ({ m with V := Function.update m.V j none }, nextClr k b (j + 1))
  | .wdone => ({ m with done := true }, .out true L L 0)
  | .out r a w c => (m, .out r a w c)

/-- A global state of one election object: memory and local states. -/
structure ESys (P : Type) where
  /-- the shared registers -/
  m : EMem P
  /-- the local states -/
  loc : P → ELoc

/-- The initial state: all registers `0`, all processes idle. -/
def ESys.init (P : Type) : ESys P := ⟨EMem.init P, fun _ => .idle⟩

/-- Process `p` takes one step. -/
def ESys.step (L : ℕ) (p : P) (s : ESys P) : ESys P :=
  ⟨(estep L p s.m (s.loc p)).1, Function.update s.loc p (estep L p s.m (s.loc p)).2⟩

/-- Process `p` invokes `election` (only effective if `p` is idle). -/
def ESys.invoke (p : P) (s : ESys P) : ESys P :=
  if s.loc p = .idle then ⟨s.m, Function.update s.loc p .start⟩ else s

/-- Reachable states (any interleaving of invocations and steps; crashes are processes that
stop taking steps, so they need no separate transition). -/
inductive EReach (L : ℕ) : ESys P → Prop
  | init : EReach L (ESys.init P)
  | step {s} (p : P) : EReach L s → EReach L (s.step L p)
  | invoke {s} (p : P) : EReach L s → EReach L (s.invoke p)

namespace ELoc

/-- Number of levels passed (ghost). -/
def passed (L : ℕ) : ELoc → ℕ
  | idle | start => 0
  | rdone k | rturn k | rv k | wv k | rturn2 k => k
  | clr k _ _ | clw k _ _ => k
  | wdone => L
  | out _ a _ _ => a

/-- The registers `V[0..written-1]` have been written by the process (ghost). -/
def written (L : ℕ) : ELoc → ℕ
  | idle | start => 0
  | rdone k | rturn k | rv k | wv k => k
  | rturn2 k => k + 1
  | clr _ b _ | clw _ b _ => b
  | wdone => L
  | out _ _ w _ => w

/-- Registers below `lo` no longer hold the process's identifier. -/
def lo : ELoc → ℕ
  | clr _ _ j | clw _ _ j => j
  | out _ _ _ c => c
  | _ => 0

/-- The process is about to write `0` into `V[i]`. -/
def clwAt : ELoc → ℕ → Prop
  | clw _ _ j, i => j = i
  | _, _ => False

instance (l : ELoc) (i : ℕ) : Decidable (l.clwAt i) := by
  cases l <;> simp only [clwAt] <;> infer_instance

/-- The process has written `turn` (it is not idle and not about to execute line 1). -/
def Started (l : ELoc) : Prop := l ≠ idle ∧ l ≠ start

/-- The process is elected: it is at line 14 or has returned `1`. -/
def Elected : ELoc → Prop
  | wdone => True
  | out true _ _ _ => True
  | _ => False

/-- Well-formedness of local states. -/
def WF (L : ℕ) : ELoc → Prop
  | idle | start | wdone => True
  | rdone k | rturn k | rv k | wv k | rturn2 k => k < L
  | clr k b j | clw k b j => k < L ∧ (b = k ∨ b = k + 1) ∧ j < b
  | out r a w c => a ≤ w ∧ w ≤ L ∧ c ≤ w ∧ (r = true → a = L ∧ w = L ∧ c = 0)

end ELoc

end Podc.CloserLookFT
