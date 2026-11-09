import Papers.PODC2026.RandomizedWaitFreeLocks.Trace

/-!
# Algorithm 2 (abortable `Lock`): the model

Algorithm 2 of Aeini, Bencivenga, Giakkoupis, Woelfel, *Simple and Efficient Randomized Wait-Free
Locks* (PODC 2026), Section 3.2, as a transition system for the safety analysis of Section 4.2.1.

## Model

* Asynchronous shared memory, arbitrary set `P` of processes, one atomic shared-memory step per
  transition (Section 2.1); the scheduler, the invocations and the abort signals are chosen by
  the adversary (an *arbitrary* action list, so the safety results hold for every adversary).
* Descriptors: `D` is the type of non-dummy descriptors; a descriptor value stored in shared
  memory is an `Option D`, with `none` the *dummy* descriptor (`isDone() = True`,
  `stat = exec`; executing it is a no-op whose two steps emit `tau`).
* Shared objects: the FAID `C`, the array `R : ℕ → Option D`, the CAS object `L`, the CAS field
  `stat d` of every descriptor and the `isDone` register `done d` (set by the last step of
  `d.execute()`).
* `d.execute()` is two steps: its invocation (event `exS d`, ghost `started d`) and its response
  (event `exE d`, sets `done d`). The steps of the thunk itself are irrelevant for safety and
  are not modelled.
* Ghost state: `started`, `used` (the descriptor was passed to some `Lock()` call), `clock`
  (incremented by *every* step, including no-op steps), `call p`/`callIdx p` (the pending
  `Lock()` call of `p` and the clock value at its invocation).
* Actions (`Act`): `invoke p d` (allowed iff `p` is idle and `d` is unused; the descriptor
  requirement of Section 2.2 — then `stat d = wait` automatically). The invocation step *is* the
  first shared-memory step of the call, i.e. line 11 of the first `HelpAndPromote()` of line 22
  (the `L.Read()`); it emits `inv p d`. `abort p` sets `p`'s `abort_sig` (only during a call).
  `sched p j` performs the next shared-memory step of `p` (one line); `j` is the index sampled at
  line 30 (written at line 31).
* Randomness is replaced by adversarial choice: the index `g` of line 30 is the action
  parameter `j`. This is a sound over-approximation for safety (every probabilistic execution is
  one of these executions). Line 16 reads `C` and stores `⌊log₂ C⌋` with `Nat.log 2 0 = 0`
  (the paper leaves `log 0` undefined; `C = 0` is possible in the calls of line 22), and line 17
  reads `R[λ]`. All entries of `R` (an unbounded array here) initially hold the dummy.
* Lines: the `while` test of line 25 is two steps (`l25a` reads `D.isDone()`, `l25b` reads
  `D.stat`); the local `abort_sig` test of line 26 is evaluated in the step that performs the
  next shared-memory operation (line 27 or line 31; the sampling of line 30 is local);
  line 33 (`C.FAD()`) and line 34 (`D.isDone()`, the response, event `resp p D (done D)`) are two
  steps. Within `HelpAndPromote()`: lines 11, 12, 13, 14 (two steps), 15, 16, 17, 18 (reads
  `d.stat` and computes `w'` by lines 18–20), 21.
* Invalid actions (e.g. scheduling an idle process): configuration unchanged except `clock + 1`,
  event `tau`. The coin argument of `step` is unused.
-/

namespace Podc.RandomizedWaitFreeLocks.Alg2

/-- Values of the `stat` field of a descriptor. -/
inductive Stat | wait | exec | susp
  deriving DecidableEq

/-- The six `HelpAndPromote()` call sites of `Lock()` (return addresses). -/
inductive Ret | r22a | r22b | r24 | r28 | r32a | r32b
  deriving DecidableEq

/-- Lines of `HelpAndPromote()` (line 14 is split in the invocation and the response of
`w.execute()`). -/
inductive HLine | l11 | l12 | l13 | l14s | l14e | l15 | l16 | l17 | l18 | l21
  deriving DecidableEq

/-- Program counter: the next shared-memory step of a process. -/
inductive PC
  | idle
  | hap (r : Ret) (l : HLine)
  | l23 | l25a | l25b | l26 | l33 | l34
  deriving DecidableEq

/-- Configurations of Algorithm 2. -/
structure Cfg (P D : Type*) where
  /-- FAID `C`. -/
  C : ℕ
  /-- The array `R` (`none` = dummy). -/
  R : ℕ → Option D
  /-- CAS object `L` (`none` = dummy). -/
  L : Option D
  /-- The `stat` field of each descriptor. -/
  stat : D → Stat
  /-- The `isDone` register of each descriptor. -/
  done : D → Bool
  /-- Ghost: some `execute()` of the descriptor has been invoked. -/
  started : D → Bool
  /-- Ghost: the descriptor has been passed to a `Lock()` call. -/
  used : D → Bool
  /-- Ghost: number of steps so far. -/
  clock : ℕ
  /-- Program counters. -/
  pc : P → PC
  /-- Ghost: the pending `Lock()` call (its descriptor argument `D`). -/
  call : P → Option D
  /-- Ghost: clock value at the invocation of the pending call. -/
  callIdx : P → ℕ
  /-- `abort_sig`. -/
  abort : P → Bool
  /-- Local `w` of `HelpAndPromote()` (line 11). -/
  w : P → Option D
  /-- Local `s` (line 15). -/
  s : P → Stat
  /-- Local `λ` (line 16). -/
  lam : P → ℕ
  /-- Local `d` (line 17). -/
  d : P → Option D
  /-- Local `w'` (lines 18–20). -/
  w2 : P → Option D

/-- Actions of the adversary. -/
inductive Act (P D : Type*)
  | invoke (p : P) (d : D)
  | abort (p : P)
  | sched (p : P) (j : ℕ)

variable {P D : Type*} [DecidableEq P] [DecidableEq D]

open Function

/-- `stat` of a possibly dummy descriptor. -/
def statO (c : Cfg P D) : Option D → Stat
  | none => .exec
  | some x => c.stat x

/-- `isDone()` of a possibly dummy descriptor. -/
def doneO (c : Cfg P D) : Option D → Bool
  | none => true
  | some x => c.done x

/-- `stat` after `o.stat.CAS(old, new)`. -/
def casStat (st : D → Stat) (o : Option D) (old new : Stat) : D → Stat :=
  match o with
  | none => st
  | some x => if st x = old then update st x new else st

/-- Where a `HelpAndPromote()` call returns to. -/
def Ret.next : Ret → PC
  | .r22a => .hap .r22b .l11
  | .r22b => .l23
  | .r24 => .l25a
  | .r28 => .l25a
  | .r32a => .hap .r32b .l11
  | .r32b => .l25a

/-- A no-op step. -/
def tick (c : Cfg P D) : Cfg P D := { c with clock := c.clock + 1 }

/-- The initial configuration. -/
def init : Cfg P D where
  C := 0
  R := fun _ => none
  L := none
  stat := fun _ => .wait
  done := fun _ => false
  started := fun _ => false
  used := fun _ => false
  clock := 0
  pc := fun _ => .idle
  call := fun _ => none
  callIdx := fun _ => 0
  abort := fun _ => false
  w := fun _ => none
  s := fun _ => .wait
  lam := fun _ => 0
  d := fun _ => none
  w2 := fun _ => none

/-- The step of process `p` at program counter `pc` (`j`: the index sampled at line 30). -/
def stepAt (c : Cfg P D) (p : P) (j : ℕ) : PC → Cfg P D × Ev P D
  | .idle => (tick c, .tau)
  -- line 11: w ← L.Read()
  | .hap r .l11 =>
    ({ c with
        clock := c.clock + 1, w := update c.w p c.L
        pc := update c.pc p (.hap r .l12) }, .tau)
  -- line 12: w.stat.CAS(wait, exec)
  | .hap r .l12 =>
    ({ c with
        clock := c.clock + 1, stat := casStat c.stat (c.w p) .wait .exec
        pc := update c.pc p (.hap r .l13) }, .tau)
  -- line 13: if w.stat.Read() = exec
  | .hap r .l13 =>
    ({ c with
        clock := c.clock + 1
        pc := update c.pc p (if statO c (c.w p) = .exec then .hap r .l14s else .hap r .l15) },
      .tau)
  -- line 14: invocation of w.execute()
  | .hap r .l14s =>
    match c.w p with
    | some x =>
      ({ c with
          clock := c.clock + 1, started := update c.started x true
          pc := update c.pc p (.hap r .l14e) }, .exS x)
    | none => ({ c with clock := c.clock + 1, pc := update c.pc p (.hap r .l14e) }, .tau)
  -- line 14: response of w.execute() (its last step sets the isDone register)
  | .hap r .l14e =>
    match c.w p with
    | some x =>
      ({ c with
          clock := c.clock + 1, done := update c.done x true
          pc := update c.pc p (.hap r .l15) }, .exE x)
    | none => ({ c with clock := c.clock + 1, pc := update c.pc p (.hap r .l15) }, .tau)
  -- line 15: s ← D.stat.Read()
  | .hap r .l15 =>
    ({ c with
        clock := c.clock + 1, s := update c.s p (statO c (c.call p))
        pc := update c.pc p (.hap r .l16) }, .tau)
  -- line 16: λ ← ⌊log C.Read()⌋
  | .hap r .l16 =>
    ({ c with
        clock := c.clock + 1, lam := update c.lam p (Nat.log 2 c.C)
        pc := update c.pc p (.hap r .l17) }, .tau)
  -- line 17: d ← R[λ].Read()
  | .hap r .l17 =>
    ({ c with
        clock := c.clock + 1, d := update c.d p (c.R (c.lam p))
        pc := update c.pc p (.hap r .l18) }, .tau)
  -- lines 18–20: read d.stat, choose w'
  | .hap r .l18 =>
    ({ c with
        clock := c.clock + 1
        w2 := update c.w2 p (if statO c (c.d p) = .wait then c.d p
          else if c.s p = .wait then c.call p else c.w p)
        pc := update c.pc p (.hap r .l21) }, .tau)
  -- line 21: L.CAS(w, w')
  | .hap r .l21 =>
    ({ c with
        clock := c.clock + 1, L := if c.L = c.w p then c.w2 p else c.L
        pc := update c.pc p r.next }, .tau)
  -- line 23: C.FAI()
  | .l23 =>
    ({ c with clock := c.clock + 1, C := c.C + 1, pc := update c.pc p (.hap .r24 .l11) }, .tau)
  -- line 25: D.isDone() = False
  | .l25a =>
    ({ c with
        clock := c.clock + 1
        pc := update c.pc p (if doneO c (c.call p) = true then .l33 else .l25b) }, .tau)
  -- line 25: D.stat.Read() ≠ susp
  | .l25b =>
    ({ c with
        clock := c.clock + 1
        pc := update c.pc p (if statO c (c.call p) = .susp then .l33 else .l26) }, .tau)
  -- line 26 (local test of abort_sig), then line 27 or lines 30–31
  | .l26 =>
    if c.abort p = true then
      ({ c with
          clock := c.clock + 1, stat := casStat c.stat (c.call p) .wait .susp
          pc := update c.pc p (.hap .r28 .l11) }, .tau)
    else
      ({ c with
          clock := c.clock + 1, R := update c.R j (c.call p)
          pc := update c.pc p (.hap .r32a .l11) }, .tau)
  -- line 33: C.FAD()
  | .l33 => ({ c with clock := c.clock + 1, C := c.C - 1, pc := update c.pc p .l34 }, .tau)
  -- line 34: return D.isDone()
  | .l34 =>
    match c.call p with
    | some x =>
      ({ c with
          clock := c.clock + 1, pc := update c.pc p .idle, call := update c.call p none },
        .resp p x (c.done x))
    | none => (tick c, .tau)

/-- The transition function (the coin is unused: random choices are adversarial). -/
def step (c : Cfg P D) : Act P D → Bool → Cfg P D × Ev P D
  | .invoke p x, _ =>
    if c.pc p = .idle ∧ c.used x = false then
      ({ c with
          clock := c.clock + 1, used := update c.used x true
          pc := update c.pc p (.hap .r22a .l12), call := update c.call p (some x)
          callIdx := update c.callIdx p c.clock, abort := update c.abort p false
          w := update c.w p c.L }, .inv p x)
    else (tick c, .tau)
  | .abort p, _ =>
    if (c.call p).isSome then
      ({ c with clock := c.clock + 1, abort := update c.abort p true }, .tau)
    else (tick c, .tau)
  | .sched p j, _ => stepAt c p j (c.pc p)

/-! ## The inductive invariant -/

/-- `x` has left `L` for good: it is suspended, or executed and done (the conclusion of
Lemma 4.11). -/
def Post (c : Cfg P D) (x : D) : Prop := c.stat x ≠ .wait ∧ (c.stat x = .exec → c.done x = true)

/-- What `p` knows about the descriptor `x = w` it read from `L` at line 11, per line of
`HelpAndPromote()`. -/
def HapInv (c : Cfg P D) : HLine → D → Prop
  | .l11, _ => True
  | .l12, x => c.L = some x ∨ Post c x
  | .l13, x => c.stat x ≠ .wait ∧ (c.L = some x ∨ (c.stat x = .exec → c.done x = true))
  | .l14s, x => c.stat x = .exec ∧ (c.L = some x ∨ c.done x = true)
  | .l14e, x => c.stat x = .exec ∧ c.started x = true ∧ (c.L = some x ∨ c.done x = true)
  | .l15, x => Post c x
  | .l16, x => Post c x
  | .l17, x => Post c x
  | .l18, x => Post c x
  | .l21, x => Post c x

/-- Global invariants. -/
structure Glob (c : Cfg P D) : Prop where
  L_used : ∀ x, c.L = some x → c.used x = true
  R_used : ∀ j x, c.R j = some x → c.used x = true
  unused : ∀ x, c.used x = false → c.stat x = .wait ∧ c.started x = false ∧ c.done x = false
  start_exec : ∀ x, c.started x = true → c.stat x = .exec
  done_start : ∀ x, c.done x = true → c.started x = true
  active_L : ∀ x, c.started x = true → c.done x = false → c.L = some x
  pending : ∀ x, c.used x = true → c.done x = false → c.stat x ≠ .susp → ∃ p, c.call p = some x
  call_inj : ∀ p q x, c.call p = some x → c.call q = some x → p = q
  abort_susp : ∀ p x, c.call p = some x → c.stat x = .susp → c.abort p = true

/-- Invariants of one process. -/
structure Loc (c : Cfg P D) (q : P) : Prop where
  idle_iff : c.pc q = .idle ↔ c.call q = none
  call_used : ∀ x, c.call q = some x → c.used x = true
  w_used : ∀ x, c.w q = some x → c.used x = true
  d_used : ∀ x, c.d q = some x → c.used x = true
  w2_used : ∀ x, c.w2 q = some x → c.used x = true
  hap : ∀ r l x, c.pc q = .hap r l → c.w q = some x → HapInv c l x
  fin : c.pc q = .l33 ∨ c.pc q = .l34 → ∃ x, c.call q = some x ∧ (c.done x = true ∨ c.stat x = .susp)

/-- The inductive invariant. -/
def Inv (c : Cfg P D) : Prop := Glob c ∧ ∀ q, Loc c q

/-- What every step guarantees about the shared state, as seen by the other processes. -/
structure EnvOK (c c' : Cfg P D) : Prop where
  stat : ∀ x, c.stat x ≠ .wait → c'.stat x = c.stat x
  done : ∀ x, c.done x = true → c'.done x = true
  started : ∀ x, c.started x = true → c'.started x = true
  used : ∀ x, c.used x = true → c'.used x = true
  L : c'.L = c.L ∨ ∀ y, c.L = some y → Post c y

end Podc.RandomizedWaitFreeLocks.Alg2
