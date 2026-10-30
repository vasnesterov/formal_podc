import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Relation

/-!
# Protected Memory Paxos (Algorithm 7 of Aguilera et al., PODC 2019): the model

"The Impact of RDMA on Agreement", Aguilera, Ben-David, Guerraoui, Marathe, Zablotchi,
PODC 2019 (arXiv 1905.12143v2), §5.1, Algorithm 7, and Appendix D.

This file is an asynchronous, interleaving model of Algorithm 7 (safety part only).

## Model

* `P` processes, `p1 : P` the initial leader; `M` memories (finite); `V` values; `inp : P → V`
  the inputs.
* Memory `i` holds one register `slot[i,p]` per process `p`, a triple `(minProp, accProp, value)`
  (`Slot`, with `accProp` and `value` merged into `acc : Option (ℕ × V)`; `minProp = 0` and
  `acc = none` encode `⊥`). Each memory has one region with exactly one writer, initially `p1`
  (`State.perm`). `getPermission(i)` gives the caller exclusive write permission (always legal).
  A write by a process without permission returns `nak` and has no effect.
* **Asynchrony.** Each process has one thread per memory (the parallel-for of lines 18–37).
  A memory operation (`Op`: getPermission, write, read-all-slots) is *invoked* by a thread,
  *takes effect* atomically at the memory later (`eff*` steps) and its *response is delivered*
  later still (`dlv*` steps). A process has at most one outstanding operation per memory
  (`Proc.link`). When an attempt ends (abort or decision) its threads are killed (`pc := off`),
  but an operation already invoked still takes effect later ("zombie"), and the next attempt's
  thread on that memory can only invoke after the zombie's response has been discarded
  (`discard`).
* Process and memory crashes are irrelevant for safety (a crashed agent is simply never
  scheduled). The failure detector `Ω` is arbitrary for safety: any process whose loop is not
  running may start a new attempt at any time (`start*`), including after it has decided (the
  loop of Algorithm 7 is `repeat forever`).
* **Ballots** (`propNr`) are positive naturals (`0` encodes `⊥`). The paper only says
  "propNr = a higher value than any proposal number seen before"; we use the standard Paxos
  convention: every attempt uses a *fresh* ballot (never used before by anybody, `State.used`)
  larger than the process's previous ballot; `p1`'s first attempt (which skips phase 1,
  line 19) uses ballot `1`, all other attempts use ballots `≥ 2`. (E.g. `(round, id)` pairs.)
* **Lines 24–26** are ambiguous in the pseudocode; we use the semantics fixed by the proof of
  Theorem D.2 and by Algorithm 12 (p. 17): the thread aborts if *any* slot read has
  `minProp > propNr`; otherwise it considers the slot with the highest `accProp` among the slots
  that hold a value (ties cannot occur, but we allow any maximal one).
* Atomicity: local computation is merged into the adjacent memory step: a response delivery
  also performs the local code up to the next memory operation (and invokes it); lines 24–33
  (including the `atomic` block and line 6 of `startPhase2`) are one step; passing the barrier
  (line 8) and invoking the line-35 write are one step; the line-35 `ack` that completes a
  majority also performs the decision (lines 37–39).
* **Line 21** is a parameter (`Variant`): `literal` writes `(propNr, ⊥, ⊥)` as in the paper;
  `repaired` writes `(propNr, a, w)` where `(a, w)` is the last phase-2 pair the process issued
  (`Proc.lastIss`), keeping its own accepted value as in Disk Paxos.
* Ghost state: `used` (ballots used), `p2val b` (value with which the attempt of ballot `b`
  entered phase 2), `votes` (successful line-35 writes), `decs` (all decisions ever made).
-/

namespace Podc.RDMAAgreement.PMP

/-- A register `slot[i,p] = (minProp, accProp, value)`; `acc = some (accProp, value)`. -/
structure Slot (V : Type*) where
  mp : ℕ
  acc : Option (ℕ × V)

/-- Memory operations. `w1` is the phase-1 write (line 21), `w2 b v` the phase-2 write
`(b, b, v)` (line 35), `rd` reads all slots of the memory (line 23). -/
inductive Op (V : Type*)
  | perm
  | w1 (s : Slot V)
  | w2 (b : ℕ) (v : V)
  | rd

/-- Responses of memory operations. -/
inductive Resp (P V : Type*)
  | ack
  | nak
  | snap (f : P → Slot V)

/-- The state of the (unique) operation channel between a process and a memory. -/
inductive Link (P V : Type*)
  | idle
  | sent (o : Op V)
  | resp (r : Resp P V)

/-- Program counter of a thread (one per process and memory). `wX` = waiting for the response
of operation `X`; `ph2` = `p1`'s first attempt, about to issue the line-35 write. -/
inductive PC
  | off | init | wPerm | wW1 | wRd | barrier | ph2 | wW2 | fin
  deriving DecidableEq

/-- Local state of a process: shared variables of its threads, plus the threads. -/
structure Proc (P M V : Type*) where
  /-- the for loop (lines 18–37) is running -/
  active : Bool
  /-- the process has started at least one attempt -/
  started : Bool
  /-- the current attempt is `p1`'s first attempt (phase 1 skipped) -/
  noPh1 : Bool
  /-- `propNr` of the current (or last) attempt -/
  bal : ℕ
  curVal : V
  curMax : ℕ
  p2s : Bool
  ready : Finset M
  /-- memories whose line-35 write was acknowledged in this attempt -/
  done : Finset M
  /-- last phase-2 pair `(ballot, value)` issued (used by the repaired line 21) -/
  lastIss : Option (ℕ × V)
  pc : M → PC
  link : M → Link P V

/-- Global state. -/
structure State (P M V : Type*) where
  slot : M → P → Slot V
  perm : M → P
  pr : P → Proc P M V
  used : Finset ℕ
  p2val : ℕ → Option V
  votes : Set (M × P × ℕ × V)
  decs : List V

/-- Which line 21 is used. -/
inductive Variant
  | literal
  | repaired

/-- The `(accProp, value)` part written at line 21. -/
def line21 {V : Type*} : Variant → Option (ℕ × V) → Option (ℕ × V)
  | .literal, _ => none
  | .repaired, li => li

variable {P M V : Type*} [DecidableEq P] [DecidableEq M] [Fintype M]

/-- A majority of the memories. -/
def Maj (S : Finset M) : Prop := Fintype.card M < 2 * S.card

instance (S : Finset M) : Decidable (Maj S) := inferInstanceAs (Decidable (_ < _))

namespace Proc

/-- Update thread `m`: program counter and link. -/
def setT (x : Proc P M V) (m : M) (c : PC) (l : Link P V) : Proc P M V :=
  { x with pc := Function.update x.pc m c, link := Function.update x.link m l }

/-- Update the link of thread `m`. -/
def setL (x : Proc P M V) (m : M) (l : Link P V) : Proc P M V :=
  { x with link := Function.update x.link m l }

/-- End the loop: all threads are killed (their outstanding operations stay in flight). -/
def kill (x : Proc P M V) : Proc P M V :=
  { x with active := false, pc := fun _ => .off }

end Proc

/-- Initial state. -/
def initState (p1 : P) (inp : P → V) : State P M V where
  slot _ _ := ⟨0, none⟩
  perm _ := p1
  pr p :=
    { active := false, started := false, noPh1 := false, bal := 0, curVal := inp p, curMax := 0,
      p2s := false, ready := ∅, done := ∅, lastIss := none, pc := fun _ => .off,
      link := fun _ => .idle }
  used := ∅
  p2val _ := none
  votes := ∅
  decs := []

open Function in
/-- One atomic step of Algorithm 7 (variant `var` of line 21). -/
inductive Step (p1 : P) (inp : P → V) (var : Variant) : State P M V → State P M V → Prop
  /-- `p1` starts its first attempt (line 19: phase 1 is skipped). -/
  | startFirst (s : State P M V) (q : P) (hq : q = p1) (hs : (s.pr q).started = false)
      (hact : (s.pr q).active = false) (hb : 1 ∉ s.used) (hlt : (s.pr q).bal < 1) :
      Step p1 inp var s
        { s with
          pr := update s.pr q
            { s.pr q with
              active := true, started := true, noPh1 := true, bal := 1,
              curVal := inp q, curMax := 0, p2s := false, ready := ∅, done := ∅,
              pc := fun _ => .ph2 }
          used := insert 1 s.used
          p2val := update s.p2val 1 (some (inp q)) }
  /-- Any other attempt (lines 12–17), with a fresh ballot `b ≥ 2`. -/
  | startNext (s : State P M V) (q : P) (b : ℕ) (hnf : ¬(q = p1 ∧ (s.pr q).started = false))
      (hact : (s.pr q).active = false) (hb : b ∉ s.used) (hlt : (s.pr q).bal < b) (h2 : 2 ≤ b) :
      Step p1 inp var s
        { s with
          pr := update s.pr q
            { s.pr q with
              active := true, started := true, noPh1 := false, bal := b,
              curVal := inp q, curMax := 0, p2s := false, ready := ∅, done := ∅,
              pc := fun _ => .init }
          used := insert b s.used }
  /-- Line 20: invoke `getPermission(m)`. -/
  | invPerm (s : State P M V) (q : P) (m : M) (hpc : (s.pr q).pc m = .init)
      (hl : (s.pr q).link m = .idle) :
      Step p1 inp var s { s with pr := update s.pr q ((s.pr q).setT m .wPerm (.sent .perm)) }
  /-- `getPermission` takes effect. -/
  | effPerm (s : State P M V) (q : P) (m : M) (hl : (s.pr q).link m = .sent .perm) :
      Step p1 inp var s
        { s with
          perm := update s.perm m q
          pr := update s.pr q ((s.pr q).setL m (.resp .ack)) }
  /-- A line-21 write takes effect, with permission. -/
  | effW1 (s : State P M V) (q : P) (m : M) (sl : Slot V) (hl : (s.pr q).link m = .sent (.w1 sl))
      (hp : s.perm m = q) :
      Step p1 inp var s
        { s with
          slot := update s.slot m (update (s.slot m) q sl)
          pr := update s.pr q ((s.pr q).setL m (.resp .ack)) }
  /-- A line-21 write takes effect, without permission: `nak`. -/
  | effW1nak (s : State P M V) (q : P) (m : M) (sl : Slot V)
      (hl : (s.pr q).link m = .sent (.w1 sl)) (hp : s.perm m ≠ q) :
      Step p1 inp var s { s with pr := update s.pr q ((s.pr q).setL m (.resp .nak)) }
  /-- A line-35 write takes effect, with permission (a "vote"). -/
  | effW2 (s : State P M V) (q : P) (m : M) (b : ℕ) (v : V)
      (hl : (s.pr q).link m = .sent (.w2 b v)) (hp : s.perm m = q) :
      Step p1 inp var s
        { s with
          slot := update s.slot m (update (s.slot m) q ⟨b, some (b, v)⟩)
          pr := update s.pr q ((s.pr q).setL m (.resp .ack))
          votes := insert (m, q, b, v) s.votes }
  /-- A line-35 write takes effect, without permission: `nak`. -/
  | effW2nak (s : State P M V) (q : P) (m : M) (b : ℕ) (v : V)
      (hl : (s.pr q).link m = .sent (.w2 b v)) (hp : s.perm m ≠ q) :
      Step p1 inp var s { s with pr := update s.pr q ((s.pr q).setL m (.resp .nak)) }
  /-- A read of all slots of `m` takes effect. -/
  | effRd (s : State P M V) (q : P) (m : M) (hl : (s.pr q).link m = .sent .rd) :
      Step p1 inp var s
        { s with pr := update s.pr q ((s.pr q).setL m (.resp (.snap (s.slot m)))) }
  /-- Permission obtained; invoke the line-21 write. -/
  | dlvPerm (s : State P M V) (q : P) (m : M) (hpc : (s.pr q).pc m = .wPerm)
      (hl : (s.pr q).link m = .resp .ack) :
      Step p1 inp var s
        { s with pr := update s.pr q ((s.pr q).setT m .wW1
            (.sent (.w1 ⟨(s.pr q).bal, line21 var (s.pr q).lastIss⟩))) }
  /-- Line-21 write acknowledged; invoke the read (line 23). -/
  | dlvW1 (s : State P M V) (q : P) (m : M) (hpc : (s.pr q).pc m = .wW1)
      (hl : (s.pr q).link m = .resp .ack) :
      Step p1 inp var s { s with pr := update s.pr q ((s.pr q).setT m .wRd (.sent .rd)) }
  /-- Line-21 write failed: abort (line 22). -/
  | dlvW1nak (s : State P M V) (q : P) (m : M) (hpc : (s.pr q).pc m = .wW1)
      (hl : (s.pr q).link m = .resp .nak) :
      Step p1 inp var s { s with pr := update s.pr q (((s.pr q).setL m .idle).kill) }
  /-- Read returned a slot with a higher `minProp`: abort (line 26). -/
  | dlvRdAbort (s : State P M V) (q : P) (m : M) (f : P → Slot V) (hpc : (s.pr q).pc m = .wRd)
      (hl : (s.pr q).link m = .resp (.snap f)) (h : ∃ r, (s.pr q).bal < (f r).mp) :
      Step p1 inp var s { s with pr := update s.pr q (((s.pr q).setL m .idle).kill) }
  /-- Read returned no value: go to the barrier (lines 33, 6). -/
  | dlvRdNone (s : State P M V) (q : P) (m : M) (f : P → Slot V) (hpc : (s.pr q).pc m = .wRd)
      (hl : (s.pr q).link m = .resp (.snap f)) (hmp : ∀ r, (f r).mp ≤ (s.pr q).bal)
      (hn : ∀ r, (f r).acc = none) :
      Step p1 inp var s
        { s with
          pr := update s.pr q
            { (s.pr q).setT m .barrier .idle with ready := insert m (s.pr q).ready } }
  /-- Read returned values, the highest is not above `CurrentMaxProp`: barrier. -/
  | dlvRdKeep (s : State P M V) (q : P) (m : M) (f : P → Slot V) (r : P) (a : ℕ) (y : V)
      (hpc : (s.pr q).pc m = .wRd) (hl : (s.pr q).link m = .resp (.snap f))
      (hmp : ∀ r, (f r).mp ≤ (s.pr q).bal) (hr : (f r).acc = some (a, y))
      (hmax : ∀ r' a' y', (f r').acc = some (a', y') → a' ≤ a) (hle : a ≤ (s.pr q).curMax) :
      Step p1 inp var s
        { s with
          pr := update s.pr q
            { (s.pr q).setT m .barrier .idle with ready := insert m (s.pr q).ready } }
  /-- Read returned a higher value before phase 2 started: adopt it (lines 30–31), barrier. -/
  | dlvRdAdopt (s : State P M V) (q : P) (m : M) (f : P → Slot V) (r : P) (a : ℕ) (y : V)
      (hpc : (s.pr q).pc m = .wRd) (hl : (s.pr q).link m = .resp (.snap f))
      (hmp : ∀ r, (f r).mp ≤ (s.pr q).bal) (hr : (f r).acc = some (a, y))
      (hmax : ∀ r' a' y', (f r').acc = some (a', y') → a' ≤ a) (hgt : (s.pr q).curMax < a)
      (hp2 : (s.pr q).p2s = false) :
      Step p1 inp var s
        { s with
          pr := update s.pr q
            { (s.pr q).setT m .barrier .idle with
              ready := insert m (s.pr q).ready, curVal := y, curMax := a } }
  /-- A straggler read a higher value after phase 2 started: abort (line 29). -/
  | dlvRdLate (s : State P M V) (q : P) (m : M) (f : P → Slot V) (r : P) (a : ℕ) (y : V)
      (hpc : (s.pr q).pc m = .wRd) (hl : (s.pr q).link m = .resp (.snap f))
      (hmp : ∀ r, (f r).mp ≤ (s.pr q).bal) (hr : (f r).acc = some (a, y))
      (hmax : ∀ r' a' y', (f r').acc = some (a', y') → a' ≤ a) (hgt : (s.pr q).curMax < a)
      (hp2 : (s.pr q).p2s = true) :
      Step p1 inp var s { s with pr := update s.pr q (((s.pr q).setL m .idle).kill) }
  /-- First thread to pass the barrier: `Phase2Started := true` (line 8), invoke line 35. -/
  | passFirst (s : State P M V) (q : P) (m : M) (hpc : (s.pr q).pc m = .barrier)
      (hl : (s.pr q).link m = .idle) (hmaj : Maj (s.pr q).ready) (hp2 : (s.pr q).p2s = false) :
      Step p1 inp var s
        { s with
          pr := update s.pr q
            { (s.pr q).setT m .wW2 (.sent (.w2 (s.pr q).bal (s.pr q).curVal)) with
              p2s := true, lastIss := some ((s.pr q).bal, (s.pr q).curVal) }
          p2val := update s.p2val (s.pr q).bal (some (s.pr q).curVal) }
  /-- Later threads pass the barrier and invoke line 35. -/
  | passLate (s : State P M V) (q : P) (m : M) (hpc : (s.pr q).pc m = .barrier)
      (hl : (s.pr q).link m = .idle) (hmaj : Maj (s.pr q).ready) (hp2 : (s.pr q).p2s = true) :
      Step p1 inp var s
        { s with
          pr := update s.pr q
            { (s.pr q).setT m .wW2 (.sent (.w2 (s.pr q).bal (s.pr q).curVal)) with
              lastIss := some ((s.pr q).bal, (s.pr q).curVal) } }
  /-- `p1`'s first attempt: invoke line 35 directly. -/
  | issueFirst (s : State P M V) (q : P) (m : M) (hpc : (s.pr q).pc m = .ph2)
      (hl : (s.pr q).link m = .idle) :
      Step p1 inp var s
        { s with
          pr := update s.pr q
            { (s.pr q).setT m .wW2 (.sent (.w2 (s.pr q).bal (s.pr q).curVal)) with
              lastIss := some ((s.pr q).bal, (s.pr q).curVal) } }
  /-- Line-35 write acknowledged, no majority yet. -/
  | dlvW2 (s : State P M V) (q : P) (m : M) (hpc : (s.pr q).pc m = .wW2)
      (hl : (s.pr q).link m = .resp .ack) (hmaj : ¬ Maj (insert m (s.pr q).done)) :
      Step p1 inp var s
        { s with
          pr := update s.pr q
            { (s.pr q).setT m .fin .idle with done := insert m (s.pr q).done } }
  /-- Line-35 write acknowledged by a majority: the loop ends, decide `CurrentVal` (39). -/
  | dlvW2Decide (s : State P M V) (q : P) (m : M) (hpc : (s.pr q).pc m = .wW2)
      (hl : (s.pr q).link m = .resp .ack) (hmaj : Maj (insert m (s.pr q).done)) :
      Step p1 inp var s
        { s with
          pr := update s.pr q
            ({ (s.pr q).setT m .fin .idle with done := insert m (s.pr q).done }).kill
          decs := (s.pr q).curVal :: s.decs }
  /-- Line-35 write failed: abort (line 36). -/
  | dlvW2nak (s : State P M V) (q : P) (m : M) (hpc : (s.pr q).pc m = .wW2)
      (hl : (s.pr q).link m = .resp .nak) :
      Step p1 inp var s { s with pr := update s.pr q (((s.pr q).setL m .idle).kill) }
  /-- The response of a killed thread's ("zombie") operation is discarded. -/
  | discard (s : State P M V) (q : P) (m : M) (r : Resp P V)
      (hpc : (s.pr q).pc m ≠ .wPerm ∧ (s.pr q).pc m ≠ .wW1 ∧ (s.pr q).pc m ≠ .wRd ∧
        (s.pr q).pc m ≠ .wW2)
      (hl : (s.pr q).link m = .resp r) :
      Step p1 inp var s { s with pr := update s.pr q ((s.pr q).setL m .idle) }

/-- Reachable states of Algorithm 7 (variant `var`). -/
def Reachable (p1 : P) (inp : P → V) (var : Variant) (s : State P M V) : Prop :=
  Relation.ReflTransGen (Step p1 inp var) (initState p1 inp) s

end Podc.RDMAAgreement.PMP
