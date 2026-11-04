import Mathlib

/-!
# The k-Bakery of Danek (PODC 2010): model

Robert Danek. *The k-Bakery: Local-Spin k-Exclusion Using Non-atomic Reads and Writes.*
PODC 2010, Figure 2 (= Figures 5.3 and 5.5 of Danek's PhD thesis, Toronto 2010).

```
shared: Want[1..N][1..N] ∈ ℕ ∪ {∞} (init ∞); Ticket[1..N] ∈ ℕ (init 0); Capture[1..N][1..N] ∈ ℕ (init 0)
12 loop
13   NCS
14   foreach i ∈ {1..N} \ {p} do Want[p][i] := Ticket[p]
15   Ticket[p] := 1 + max(Ticket[1], ..., Ticket[N])
16   foreach i ∈ {1..N} \ {p} do Want[p][i] := Ticket[p]
17   captured := false                                            (shaded)
18   predecessor_set := {1..N} \ {p}
19   while |predecessor_set| ≥ k ∧ ¬captured do
20     foreach i ∈ predecessor_set do
21       if (Ticket[p], p) < (Want[i][p], i) then predecessor_set := predecessor_set \ {i}
22     foreach i ∈ {1..N} do if Ticket[p] < Capture[i][p] then captured := true   (shaded)
23   foreach i ∈ {1..N} do Capture[p][i] := Ticket[p]             (shaded)
24   CS
25   foreach i ∈ {1..N} do Want[p][i] := ∞
26 end loop
```

## Model

* Asynchronous shared memory with atomic reads and writes; processes form a finite linearly
  ordered type `P` (the paper's `{1, …, N}`; the order breaks ties between equal tickets).
* `fife = false` is the unshaded algorithm (Theorem 8), `fife = true` the full algorithm
  (Theorem 9). Without the shaded lines `captured` stays `false`.
* Every step of a process performs at most one shared-memory access, followed by the local
  computation up to the next access. The program counter `PC` carries the local variables
  (`rem` = the indices a `foreach` still has to visit, `acc` = the maximum read so far at line 15,
  `pred` = `predecessor_set`, `cap` = `captured`). A `foreach` visits the indices in an
  **arbitrary** order (chosen by the adversary at every step). When a `foreach` has nothing
  left to visit, one local step moves on (this also merges the local lines 17–18).
* Process `p` reads its own variable `Ticket[p]` at lines 14, 16, 21, 22, 23 in the same step as
  the accompanying write/read of another variable: `p` is the only writer of `Ticket[p]`, so
  this does not change the behaviour (it only removes `p`'s re-reads of its own ticket from the
  RMR count, which the thesis bounds by one RMR per passage).
* An execution is a schedule: at every time some process takes a step (the adversary also
  chooses the `foreach` index). A process *crashes* if it takes finitely many steps and stops
  outside the NCS. A process in the NCS that is scheduled leaves the NCS; one that is never
  scheduled again stays there forever (this is not a crash). The CS is a single location; a
  process in the CS that is scheduled leaves it.
* RMRs: in the DSM model `Ticket[p]`, `Want[i][p]`, `Capture[i][p]` live in `p`'s module; in the
  (write-through, write-invalidate) CC model, `cached` records the valid cached copies: a read
  is an RMR iff the reader has no valid copy (afterwards it has one), every write is an RMR and
  invalidates all other processes' copies. `cached` is part of the cost model only; the
  algorithm never reads it.
-/

namespace Podc.KBakery

open Finset

/-- Program counters together with the private variables of a process. -/
inductive PC (P : Type) where
  /-- line 13, non-critical section -/
  | ncs
  /-- line 14: `Want[p][i] := Ticket[p]` for the `i ∈ rem` still to write -/
  | d14 (rem : Finset P)
  /-- line 15: read `Ticket[i]` for `i ∈ rem`; `acc` = maximum read so far; when `rem = ∅`,
  write `Ticket[p] := acc + 1` -/
  | d15 (acc : ℕ) (rem : Finset P)
  /-- line 16: `Want[p][i] := Ticket[p]` for the `i ∈ rem` still to write -/
  | d16 (rem : Finset P)
  /-- line 19: loop test -/
  | head (pred : Finset P) (cap : Bool)
  /-- lines 20–21: still to examine `rem ⊆ pred` -/
  | scan (pred rem : Finset P)
  /-- line 22: still to read `Capture[i][p]` for `i ∈ rem` -/
  | chk (pred rem : Finset P) (cap : Bool)
  /-- line 23: still to write `Capture[p][i]` for `i ∈ rem` -/
  | cap23 (rem : Finset P)
  /-- line 24, critical section -/
  | cs
  /-- line 25: still to write `Want[p][i] := ∞` for `i ∈ rem` -/
  | ex (rem : Finset P)
  deriving DecidableEq

/-- Shared variables (used for RMR accounting). -/
inductive Var (P : Type) where
  | want (i j : P)
  | ticket (i : P)
  | capture (i j : P)
  deriving DecidableEq

/-- The process in whose memory module a variable lives (DSM model). -/
def Var.owner {P : Type} : Var P → P
  | .want _ j => j
  | .ticket i => i
  | .capture _ j => j

/-- Configurations. -/
structure Cfg (P : Type) where
  /-- `want q p = Want[q][p]` (`⊤ = ∞`) -/
  want : P → P → WithTop ℕ
  /-- `Ticket` -/
  ticket : P → ℕ
  /-- `capture q p = Capture[q][p]` -/
  capture : P → P → ℕ
  /-- program counters with private variables -/
  pc : P → PC P
  /-- CC cost model: `cached p x` iff `p` holds a valid cached copy of `x` -/
  cached : P → Var P → Bool

variable {P : Type} [LinearOrder P] [Fintype P]

/-- The initial configuration. -/
def Cfg.init : Cfg P where
  want _ _ := ⊤
  ticket _ := 0
  capture _ _ := 0
  pc _ := .ncs
  cached _ _ := false

/-- `(v, r) < (w, q)` in the lexicographic order on (ticket, process id). -/
def lexLt (v : ℕ) (r : P) (w : ℕ) (q : P) : Prop := v < w ∨ (v = w ∧ r < q)

/-- `(v, r) < (w, q)` with `w ∈ ℕ ∪ {∞}` (line 21). -/
def wantGood (v : ℕ) (r : P) (w : WithTop ℕ) (q : P) : Prop :=
  (v : WithTop ℕ) < w ∨ ((v : WithTop ℕ) = w ∧ r < q)

instance (v : ℕ) (r : P) (w : WithTop ℕ) (q : P) : Decidable (wantGood v r w q) := by
  unfold wantGood; infer_instance

/-- The indices a `foreach` still has to visit (empty for the other locations). -/
def PC.rem : PC P → Finset P
  | .d14 rem | .d15 _ rem | .d16 rem | .scan _ rem | .chk _ rem _ | .cap23 rem | .ex rem => rem
  | _ => ∅

/-- The shared access performed by the step of `p` that visits index `i` (`some (isWrite, x)`). -/
def access (s : Cfg P) (p i : P) : Option (Bool × Var P) :=
  match s.pc p with
  | .ncs => none
  | .d14 rem => if i ∈ rem then some (true, .want p i) else none
  | .d15 _ rem => if i ∈ rem then some (false, .ticket i) else some (true, .ticket p)
  | .d16 rem => if i ∈ rem then some (true, .want p i) else none
  | .head _ _ => none
  | .scan _ rem => if i ∈ rem then some (false, .want i p) else none
  | .chk _ rem _ => if i ∈ rem then some (false, .capture i p) else none
  | .cap23 rem => if i ∈ rem then some (true, .capture p i) else none
  | .cs => none
  | .ex rem => if i ∈ rem then some (true, .want p i) else none

/-- Cache update of the CC model for an access by `p`. -/
def updCache (c : P → Var P → Bool) (p : P) : Option (Bool × Var P) → P → Var P → Bool
  | none => c
  | some (false, x) => fun q y => if q = p ∧ y = x then true else c q y
  | some (true, x) => fun q y => if q ≠ p ∧ y = x then false else c q y

/-- Is the step an RMR in the CC model? -/
def rmrCC (s : Cfg P) (p i : P) : Bool :=
  match access s p i with
  | none => false
  | some (true, _) => true
  | some (false, x) => !s.cached p x

/-- Is the step an RMR in the DSM model? -/
def rmrDSM (s : Cfg P) (p i : P) : Bool :=
  match access s p i with
  | none => false
  | some (_, x) => decide (x.owner ≠ p)

/-- Set the program counter of `p`. -/
def Cfg.setPc (s : Cfg P) (p : P) (c : PC P) : Cfg P :=
  { s with pc := Function.update s.pc p c }

/-- Memory and control effect of a step of `p` visiting index `i` (cache untouched). -/
def core (fife : Bool) (k : ℕ) (s : Cfg P) (p i : P) : Cfg P :=
  match s.pc p with
  | .ncs => s.setPc p (.d14 (univ.erase p))
  | .d14 rem =>
    if i ∈ rem then
      { s with want := Function.update s.want p (Function.update (s.want p) i (s.ticket p)),
               pc := Function.update s.pc p (.d14 (rem.erase i)) }
    else s.setPc p (.d15 0 univ)
  | .d15 acc rem =>
    if i ∈ rem then s.setPc p (.d15 (max acc (s.ticket i)) (rem.erase i))
    else { s with ticket := Function.update s.ticket p (acc + 1),
                  pc := Function.update s.pc p (.d16 (univ.erase p)) }
  | .d16 rem =>
    if i ∈ rem then
      { s with want := Function.update s.want p (Function.update (s.want p) i (s.ticket p)),
               pc := Function.update s.pc p (.d16 (rem.erase i)) }
    else s.setPc p (.head (univ.erase p) false)
  | .head pred cap =>
    if k ≤ pred.card ∧ cap = false then s.setPc p (.scan pred pred)
    else s.setPc p (if fife then .cap23 univ else .cs)
  | .scan pred rem =>
    if i ∈ rem then
      s.setPc p (.scan (if wantGood (s.ticket p) p (s.want i p) i then pred.erase i else pred)
        (rem.erase i))
    else s.setPc p (if fife then .chk pred univ false else .head pred false)
  | .chk pred rem cap =>
    if i ∈ rem then s.setPc p (.chk pred (rem.erase i) (cap || decide (s.ticket p < s.capture i p)))
    else s.setPc p (.head pred cap)
  | .cap23 rem =>
    if i ∈ rem then
      { s with capture := Function.update s.capture p (Function.update (s.capture p) i (s.ticket p)),
               pc := Function.update s.pc p (.cap23 (rem.erase i)) }
    else s.setPc p .cs
  | .cs => s.setPc p (.ex univ)
  | .ex rem =>
    if i ∈ rem then
      { s with want := Function.update s.want p (Function.update (s.want p) i ⊤),
               pc := Function.update s.pc p (.ex (rem.erase i)) }
    else s.setPc p .ncs

/-- One step of process `p`, visiting index `i` if its current `foreach` is not finished. -/
def stepAt (fife : Bool) (k : ℕ) (s : Cfg P) (p i : P) : Cfg P :=
  { core fife k s p i with cached := updCache s.cached p (access s p i) }

/-- The adversary's choice `i` is admissible: it is one of the indices still to visit, unless
there are none. -/
def Admissible (s : Cfg P) (p i : P) : Prop := i ∈ (s.pc p).rem ∨ (s.pc p).rem = ∅

/-- Executions: a schedule of processes and `foreach` choices, and the resulting configurations. -/
structure Run (fife : Bool) (k : ℕ) (P : Type) [LinearOrder P] [Fintype P] where
  /-- configuration at time `t` -/
  s : ℕ → Cfg P
  /-- the process taking step `t` -/
  sched : ℕ → P
  /-- the index chosen by the adversary at step `t` -/
  choice : ℕ → P
  init : s 0 = Cfg.init
  adm : ∀ t, Admissible (s t) (sched t) (choice t)
  step : ∀ t, s (t + 1) = stepAt fife k (s t) (sched t) (choice t)

/-- Reachable configurations. -/
inductive Reachable (fife : Bool) (k : ℕ) : Cfg P → Prop
  | init : Reachable fife k Cfg.init
  | step {s : Cfg P} {p i : P} : Reachable fife k s → Admissible s p i →
      Reachable fife k (stepAt fife k s p i)

/-! ### Regions -/

/-- Doorway: lines 14–15. -/
def PC.InDoorway : PC P → Prop
  | .d14 _ | .d15 _ _ => True
  | _ => False

/-- Waiting room: lines 16–23 (after the doorway, before the CS). -/
def PC.InWaiting : PC P → Prop
  | .d16 _ | .head _ _ | .scan _ _ | .chk _ _ _ | .cap23 _ => True
  | _ => False

/-- Trying protocol: lines 14–23. -/
def PC.InTrying (c : PC P) : Prop := c.InDoorway ∨ c.InWaiting

/-- The critical section. -/
def PC.InCS (c : PC P) : Prop := c = .cs

/-- The process holds a ticket of its current passage (lines 16–24). -/
def PC.Post15 : PC P → Prop
  | .d16 _ | .head _ _ | .scan _ _ | .chk _ _ _ | .cap23 _ | .cs => True
  | _ => False

instance (c : PC P) : Decidable c.InDoorway := by unfold PC.InDoorway; split <;> infer_instance
instance (c : PC P) : Decidable c.InWaiting := by unfold PC.InWaiting; split <;> infer_instance
instance (c : PC P) : Decidable c.InTrying := by unfold PC.InTrying; infer_instance
instance (c : PC P) : Decidable c.Post15 := by unfold PC.Post15; split <;> infer_instance

/-- Crashed processes of a run: they take finitely many steps and stop outside the NCS. -/
def Run.Crashed {fife : Bool} {k : ℕ} (r : Run fife k P) (q : P) : Prop :=
  ∃ T, ∀ t ≥ T, r.sched t ≠ q ∧ (r.s t).pc q ≠ .ncs

end Podc.KBakery
