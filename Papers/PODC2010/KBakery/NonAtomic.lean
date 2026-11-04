import Mathlib

/-!
# Figure 3 (non-atomic reads and writes) violates k-exclusion

We model the algorithm of Figure 3 of the paper (Figure 5.6 of the thesis) with **non-atomic**
(Lamport-safe) single-writer registers, as the paper prescribes ("atomic (non-atomic) reads and
writes of variables in this paper behave the same as reads and writes of multireader single-writer
atomic (safe) registers"; "if a non-atomic read and write access the same variable concurrently,
then the read returns an arbitrary value").

## Model (a sub-model of the paper's, which suffices for a counterexample)

* Every register (`Want[i][j][b]`, `Ticket[i]`, `Capture[i][j][b]`) holds a value in `ℕ ∪ {∞}`.
* A write takes two steps of the writer: *begin* (the register becomes busy) and *end* (the new
  value is stored, the register is no longer busy). A read is one step: if the register is not
  busy it returns the stored value; if a write is in progress it returns an arbitrary value chosen
  by the adversary. (Every execution of this model is an execution of the interval model of
  safe registers: zero-length reads overlapping a write may return anything, the others return the
  last written value.)
* A process reads its own `Ticket[p]` and `Capture[p][i][1]` (lines 30–33, 38, 41, 44, 45) without
  a separate step: it is the only writer and never reads them while writing them, so such reads
  always return the stored value.
* The `foreach` loops visit indices in the order of a fixed list `ord` of all processes (the
  paper leaves the order unspecified, so this is one of the allowed implementations; the
  counterexample uses `ord = [0, 1, 2]`).
* An execution is a list of events `(p, d)`: process `p` takes its next step; `d = some v` supplies
  the value of a read that overlaps a write (`none` otherwise). `exec` returns `none` on an
  ill-formed event, so `exec … = some s` certifies a legal execution.

`counterexample` exhibits, for `N = 3` processes and `k = 1`, a legal execution ending with two
processes in the critical section.

**The flaw.** `Ticket` is a safe register, so a process choosing its ticket while another
process `r` rewrites `Ticket[r]` may read `0`, choose a ticket smaller than an *old* capture value
`Capture[r][p]` that `r` wrote in an earlier passage, and immediately detect a (stale) capture.
-/

namespace Podc.KBakery.NonAtomic

/-- Shared registers. -/
inductive Reg (P : Type) where
  | want (i j : P) (b : Bool)
  | ticket (i : P)
  | cap (i j : P) (b : Bool)
  deriving DecidableEq

/-- What to do after a sequence of writes. -/
inductive Cont (P : Type) where
  /-- line 31 -/
  | choose
  /-- line 34: enter the loop -/
  | loop
  /-- lines 43–45, still to visit `rem` -/
  | capt (rem : List P)
  /-- line 46 -/
  | cs
  /-- back to the NCS -/
  | ncs
  deriving DecidableEq

/-- Program counters with local variables. -/
inductive PC (P : Type) where
  | ncs
  /-- pending writes; `started` = the first write has begun -/
  | writes (ws : List (Reg P × WithTop ℕ)) (started : Bool) (k : Cont P)
  /-- line 31: reading `Ticket[i]` for `i ∈ rem`, maximum so far `acc` -/
  | choose (acc : ℕ) (rem : List P)
  /-- lines 37–39: `second = false`: read `Want[i][p][2]` of the head `i` of `rem`;
  `second = true`: read `Want[i][p][1]` -/
  | scan (pred : Finset P) (rem : List P) (second : Bool)
  /-- lines 40–42 -/
  | chk (pred : Finset P) (rem : List P) (second cap : Bool)
  /-- line 44: read `Ticket[i]` of the head `i` of `rem` -/
  | capt (rem : List P)
  /-- line 46 -/
  | cs
  deriving DecidableEq

/-- Configurations. -/
structure Cfg (P : Type) where
  mem : Reg P → WithTop ℕ
  busy : Reg P → Bool
  pc : P → PC P

variable {P : Type} [DecidableEq P] [LinearOrder P] [Fintype P]

/-- Initial configuration: `Want = ∞`, `Ticket = 0`, `Capture = 0`. -/
def Cfg.init : Cfg P where
  mem r := match r with
    | .want _ _ _ => ⊤
    | _ => 0
  busy _ := false
  pc _ := .ncs

/-- The value of a read of `r`: the stored value if `r` is not busy (and no value is supplied),
the supplied arbitrary value if `r` is busy. -/
def readVal (s : Cfg P) (r : Reg P) (d : Option (WithTop ℕ)) : Option (WithTop ℕ) :=
  if s.busy r then d else if d = none then some (s.mem r) else none

/-- The stored ticket of `p` as a natural number (tickets are finite). -/
def tk (s : Cfg P) (p : P) : ℕ := WithTop.untopD 0 (s.mem (.ticket p))

/-- `(a, p) < (w, q)` lexicographically, `w ∈ ℕ ∪ {∞}`. -/
def pairLt (a : ℕ) (p : P) (w : WithTop ℕ) (q : P) : Bool :=
  decide ((a : WithTop ℕ) < w) || (decide ((a : WithTop ℕ) = w) && decide (p < q))

/-- The writes `Want[p][i][1] := v; Want[p][i][2] := v` for `i` in `is`. -/
def wantWrites (p : P) (is : List P) (v : WithTop ℕ) : List (Reg P × WithTop ℕ) :=
  is.flatMap fun i => [(.want p i false, v), (.want p i true, v)]

/-- Continue after the pending writes are done. -/
def contPC (ord : List P) (k : ℕ) (p : P) : Cont P → PC P
  | .choose => .choose 0 ord
  | .loop =>
    -- lines 34–36: `predecessor_set := {1..N} \ {p}`, `captured := false`, loop test
    let pred := Finset.univ.erase p
    if k ≤ pred.card then .scan pred (ord.filter (· ∈ pred)) false else .capt ord
  | .capt rem => .capt rem
  | .cs => .cs
  | .ncs => .ncs

/-- The location after a pass of lines 37–42 (loop test of line 36). -/
def loopTest (ord : List P) (k : ℕ) (pred : Finset P) (cap : Bool) : PC P :=
  if k ≤ pred.card ∧ cap = false then .scan pred (ord.filter (· ∈ pred)) false else .capt ord

/-- Set the program counter of `p`. -/
def Cfg.setPc (s : Cfg P) (p : P) (c : PC P) : Cfg P := { s with pc := Function.update s.pc p c }

/-- One step of process `p`; `d` supplies the value of a read overlapping a write. `none` if the
event is ill-formed. -/
def step (ord : List P) (k : ℕ) (s : Cfg P) (p : P) (d : Option (WithTop ℕ)) : Option (Cfg P) :=
  match s.pc p with
  | .ncs =>
    -- lines 29–30: announce the ticket of the previous passage
    if d = none then
      some (s.setPc p (.writes (wantWrites p (ord.filter (· ≠ p)) (s.mem (.ticket p))) false
        .choose))
    else none
  | .writes [] _ c => if d = none then some (s.setPc p (contPC ord k p c)) else none
  | .writes ((r, v) :: ws) false c =>
    if d = none then
      some { s with busy := Function.update s.busy r true,
                    pc := Function.update s.pc p (.writes ((r, v) :: ws) true c) }
    else none
  | .writes ((r, v) :: ws) true c =>
    if d = none then
      some { s with mem := Function.update s.mem r v, busy := Function.update s.busy r false,
                    pc := Function.update s.pc p (.writes ws false c) }
    else none
  | .choose acc [] =>
    -- line 31: write `Ticket[p] := 1 + max`, then lines 32–33
    if d = none then
      some (s.setPc p (.writes ((.ticket p, ((acc + 1 : ℕ) : WithTop ℕ)) ::
        wantWrites p (ord.filter (· ≠ p)) ((acc + 1 : ℕ) : WithTop ℕ)) false .loop))
    else none
  | .choose acc (i :: rem) =>
    if i = p then
      if d = none then some (s.setPc p (.choose (max acc (tk s p)) rem)) else none
    else
      (readVal s (.ticket i) d).bind fun v =>
        some (s.setPc p (.choose (max acc (WithTop.untopD 0 v)) rem))
  | .scan pred [] _ => if d = none then
      some (s.setPc p (.chk pred ord false false)) else none
  | .scan pred (i :: rem) false =>
    (readVal s (.want i p true) d).bind fun v =>
      -- line 38
      if pairLt (tk s p) p v i then some (s.setPc p (.scan pred (i :: rem) true))
      else some (s.setPc p (.scan pred rem false))
  | .scan pred (i :: rem) true =>
    (readVal s (.want i p false) d).bind fun v =>
      -- line 39
      if pairLt (tk s p) p v i then some (s.setPc p (.scan (pred.erase i) rem false))
      else some (s.setPc p (.scan pred rem false))
  | .chk pred [] _ cap => if d = none then some (s.setPc p (loopTest ord k pred cap)) else none
  | .chk pred (i :: rem) false cap =>
    (readVal s (.cap i p true) d).bind fun v =>
      -- line 41
      if ((tk s p : ℕ) : WithTop ℕ) < v then some (s.setPc p (.chk pred (i :: rem) true cap))
      else some (s.setPc p (.chk pred rem false cap))
  | .chk pred (i :: rem) true cap =>
    (readVal s (.cap i p false) d).bind fun v =>
      -- line 42
      if ((tk s p : ℕ) : WithTop ℕ) < v then some (s.setPc p (.chk pred rem false true))
      else some (s.setPc p (.chk pred rem false cap))
  | .capt [] => if d = none then some (s.setPc p .cs) else none
  | .capt (i :: rem) =>
    -- line 44: `Capture[p][i][1] ≤ Ticket[i]` (own register read directly)
    let readT := if i = p then (if d = none then some (s.mem (.ticket p)) else none)
      else readVal s (.ticket i) d
    readT.bind fun v =>
      if s.mem (.cap p i false) ≤ v then
        -- line 45
        some (s.setPc p (.writes [(.cap p i false, s.mem (.ticket p)),
          (.cap p i true, s.mem (.ticket p))] false (.capt rem)))
      else some (s.setPc p (.capt rem))
  | .cs =>
    -- lines 47–48
    if d = none then some (s.setPc p (.writes (wantWrites p ord ⊤) false .ncs)) else none

/-- Run a list of events. -/
def exec (ord : List P) (k : ℕ) : Cfg P → List (P × Option (WithTop ℕ)) → Option (Cfg P)
  | s, [] => some s
  | s, (p, d) :: es => (step ord k s p d).bind fun s' => exec ord k s' es

/-- `n` steps of `p` without overlapping reads. -/
def seg (p : P) (n : ℕ) : List (P × Option (WithTop ℕ)) := List.replicate n (p, none)

/-- The counterexample execution for processes `0, 1, 2` (`y, p, r` in the README), `k = 1`:
1. `y` (= 0) starts its first passage and begins writing `Ticket[y] := 1`; meanwhile `r` (= 2)
   chooses its ticket and reads the overlapping write of `Ticket[y]` as `100`, so `r`'s ticket
   is `101`.
2. `y` finishes its passage (its ticket 1 is the smallest); then `r` finishes its passage and at
   line 45 captures `y` and `p` (= 1) with `Capture[r][·] := 101`.
3. `r` starts a second passage and begins writing `Ticket[r] := 102` (and stops there).
4. `y` starts its second passage; its read of `Ticket[r]` overlaps `r`'s write and returns `0`,
   so `y`'s ticket is `2`; `y` enters the CS (all other announcements are larger).
5. `p` starts its first passage; its read of `Ticket[r]` returns `0`, so `p`'s ticket is `3`;
   `p` cannot remove `y` (whose pair `(2, y)` is smaller) but finds the stale capture
   `Capture[r][p] = 101 > 3` and enters the CS as well. -/
def badTrace : List (Fin 3 × Option (WithTop ℕ)) :=
  seg 0 15 ++ seg 2 10 ++ [(2, some 100)] ++ seg 2 14 ++
  seg 0 52 ++ seg 2 57 ++
  seg 0 12 ++ [(0, some 0)] ++ seg 0 29 ++ [(0, some 0)] ++ seg 0 1 ++
  seg 1 12 ++ [(1, some 0)] ++ seg 1 33 ++ [(1, some 0)] ++ seg 1 6

/-- **Theorem 10 is false**: the non-atomic algorithm of Figure 3 violates k-exclusion. With
`N = 3` and `k = 1`, `badTrace` is a legal execution after which processes `0` and `1` are both
in the critical section. -/
theorem counterexample :
    (exec [0, 1, 2] 1 Cfg.init badTrace).map (fun s => (s.pc 0, s.pc 1)) = some (PC.cs, PC.cs) := by
  decide +kernel

end Podc.KBakery.NonAtomic
