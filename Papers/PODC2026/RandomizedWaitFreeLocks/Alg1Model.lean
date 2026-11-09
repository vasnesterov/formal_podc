import Papers.PODC2026.RandomizedWaitFreeLocks.Trace

/-!
# Algorithm 1 (constant-space randomized TryLock): the model

```
Shared: FAID C (= 0), register R, CAS object L (R, L = dummy descriptor, isDone() = True)

HelpAndPromote()                    TryLock(D)
1  w ← L.Read()                     5  b ← C.FAI() + 1
2  w.execute()                      6  with probability 1/(7 b log²(b+1)) do R.Write(D)
3  d ← R.Read()                     7  for i ∈ {1,2} do HelpAndPromote()
4  L.CAS(w, d)                      8  if L.Read() = D then D.execute()
                                    9  C.FAD()
                                    10 return D.isDone()
```

**Model.** Asynchronous shared memory; one atomic step per time point; processes `P` (any
number, possibly infinite); descriptors `D`, the dummy descriptor is `none : Option D`
(its thunk does nothing and is never reported as an event; `isDone = true`).
Every descriptor has a unique owner `own : D → P`, the only process that may call `TryLock`
on it, and it may do so again only if no earlier `TryLock` on it returned `True`.

* Steps are chosen by an adversary (`Act`): `invoke p δ` starts `TryLock(δ)` of an idle
  process `p` (this step is the `C.FAI()` of line 5, the call's first shared-memory step);
  `sched p` lets `p` execute its next line.  Each step also receives a coin (`Bool`), used only
  at line 6 (`true` = write).  The probability of the coin is attached in `Alg1Prob.lean`; the
  safety results hold for every sequence of coins.
* Line 6 with coin `false` is a step without shared-memory access (the paper fuses it with the
  read of line 1; separating them gives the adversary more interleavings, so all our results
  apply to the paper's model).
* `w.execute()` is two steps: its invocation (`exS w`) and its response (`exE w`), which sets
  the `isDone` register of `w`; the thunk's own steps touch only other memory and are omitted
  (any number of other steps may be interleaved between the two).
* Invalid actions only advance the clock.

Ghost state (does not influence the algorithm): the clock `T`, the times of the last write to
`R` and of the last change of `L`, the time `eT δ` at which `δ` first became the value of `L`
(`0` = never), the set `act` of processes between lines 5 and 9, `started`, `retT δ` (some
`TryLock(δ)` returned `True`), `failed p k` (the `k`-th call of `p` returned `False`), and per
process the times of its line 5, line 6, line 1 and line 3 steps, its call counter and the
index of the invocation event of its current call.
-/

namespace Podc.RandomizedWaitFreeLocks.Alg1

/-- Program counter: the line a process executes next (`i = false/true`: first/second
`HelpAndPromote()` call of line 7). -/
inductive PC where
  | idle
  | wr
  | rdL (i : Bool)
  | exS (i : Bool)
  | exE (i : Bool)
  | rdR (i : Bool)
  | cas (i : Bool)
  | rd8
  | exS8
  | exE8
  | fad
  | ret
  deriving DecidableEq

namespace PC

/-- Inside one of the two `HelpAndPromote()` calls (lines 1–4). -/
def hap : PC → Bool
  | rdL _ | exS _ | exE _ | rdR _ | cas _ => true
  | _ => false

/-- Inside the second `HelpAndPromote()` call. -/
def hap2 : PC → Bool
  | rdL true | exS true | exE true | rdR true | cas true => true
  | _ => false

/-- Lines 2–4 (after reading `w`). -/
def h24 : PC → Bool
  | exS _ | exE _ | rdR _ | cas _ => true
  | _ => false

/-- Lines 2–4 of the second `HelpAndPromote()` call. -/
def h24₂ : PC → Bool
  | exS true | exE true | rdR true | cas true => true
  | _ => false

/-- Lines 8–10. -/
def post : PC → Bool
  | rd8 | exS8 | exE8 | fad | ret => true
  | _ => false

/-- Between lines 5 and 9 (`C` counts the process). -/
def inAct : PC → Bool
  | idle | ret => false
  | _ => true

/-- At line 4. -/
def isCas : PC → Bool
  | cas _ => true
  | _ => false

end PC

/-- Local state of a process (`D = none` iff the process is idle). -/
structure Loc (D : Type*) where
  pc : PC
  /-- own descriptor of the current call -/
  dsc : Option D
  /-- observed contention -/
  b : ℕ
  w : Option D
  d : Option D
  /-- ghost: time of line 5 -/
  fT : ℕ
  /-- ghost: time of line 6 -/
  l6 : ℕ
  /-- ghost: time of line 1 of the current `HelpAndPromote()` -/
  a : ℕ
  /-- ghost: time of line 3 of the current `HelpAndPromote()` -/
  rb : ℕ
  /-- ghost: number of `TryLock` calls invoked so far -/
  call : ℕ
  /-- ghost: index of the invocation event of the current call -/
  cidx : ℕ

/-- Initial local state. -/
def Loc.init (D : Type*) : Loc D :=
  ⟨.idle, none, 0, none, none, 0, 0, 0, 0, 0, 0⟩

/-- Configurations (shared memory, local states, ghost state). -/
structure Cfg (P D : Type*) where
  L : Option D
  R : Option D
  C : ℕ
  done : D → Bool
  loc : P → Loc D
  /-- ghost: clock (number of steps taken) -/
  T : ℕ
  /-- ghost: time of the last write to `R` -/
  lastW : ℕ
  /-- ghost: time of the last change of `L` -/
  lastChg : ℕ
  /-- ghost: time at which the descriptor became the value of `L` (`0` = never) -/
  eT : D → ℕ
  started : D → Bool
  /-- ghost: processes between lines 5 and 9 -/
  act : Finset P
  /-- ghost: some `TryLock(δ)` returned `True` -/
  retT : D → Bool
  /-- ghost: the `k`-th call of `p` returned `False` -/
  failed : P → ℕ → Bool

/-- Adversary actions. -/
inductive Act (P D : Type*) where
  | invoke (p : P) (δ : D)
  | sched (p : P)

variable {P D : Type*} [DecidableEq P] [DecidableEq D]

/-- The initial configuration. -/
def init : Cfg P D :=
  ⟨none, none, 0, fun _ => false, fun _ => Loc.init D, 0, 0, 0, fun _ => 0, fun _ => false, ∅,
    fun _ => false, fun _ _ => false⟩

namespace Cfg

/-- Replace the local state of `p`. -/
def upd (c : Cfg P D) (p : P) (l : Loc D) : Cfg P D := { c with loc := Function.update c.loc p l }

/-- Advance the clock. -/
def tick (c : Cfg P D) : Cfg P D := { c with T := c.T + 1 }

/-- `eT` lifted to `Option D` (the dummy is in `L` from time `0`). -/
def eTo (c : Cfg P D) : Option D → ℕ
  | none => 0
  | some δ => c.eT δ

/-- The descriptor has been the value of `L` at some point. -/
def everL (c : Cfg P D) : Option D → Prop
  | none => True
  | some δ => c.eT δ ≠ 0

end Cfg

variable (own : D → P)

/-- One step: the adversary's action, the coin, and the emitted event. -/
def step (c : Cfg P D) : Act P D → Bool → Cfg P D × Ev P D
  | .invoke p δ, _ =>
    if (c.loc p).pc = .idle ∧ own δ = p ∧ c.retT δ = false then
      ({ (c.tick.upd p
            { (c.loc p) with
              pc := .wr, dsc := some δ, b := c.C + 1, fT := c.T + 1,
              call := (c.loc p).call + 1, cidx := c.T }) with
          C := c.C + 1, act := insert p c.act }, .inv p δ)
    else (c.tick, .tau)
  | .sched p, coin =>
    let l := c.loc p
    let n := c.T + 1
    match l.pc with
    | .idle => (c.tick, .tau)
    | .wr =>
      if coin then
        ({ (c.tick.upd p { l with pc := .rdL false, l6 := n }) with R := l.dsc, lastW := n }, .tau)
      else (c.tick.upd p { l with pc := .rdL false, l6 := n }, .tau)
    | .rdL i => (c.tick.upd p { l with pc := .exS i, w := c.L, a := n }, .tau)
    | .exS i =>
      match l.w with
      | some ω =>
        ({ (c.tick.upd p { l with pc := .exE i }) with started := Function.update c.started ω true },
          .exS ω)
      | none => (c.tick.upd p { l with pc := .exE i }, .tau)
    | .exE i =>
      match l.w with
      | some ω =>
        ({ (c.tick.upd p { l with pc := .rdR i }) with done := Function.update c.done ω true },
          .exE ω)
      | none => (c.tick.upd p { l with pc := .rdR i }, .tau)
    | .rdR i => (c.tick.upd p { l with pc := .cas i, d := c.R, rb := n }, .tau)
    | .cas i =>
      let nxt := if i then PC.rd8 else PC.rdL true
      if c.L = l.w ∧ l.d ≠ l.w then
        ({ (c.tick.upd p { l with pc := nxt }) with
            L := l.d, lastChg := n,
            eT := match l.d with
              | some δ => Function.update c.eT δ n
              | none => c.eT }, .tau)
      else (c.tick.upd p { l with pc := nxt }, .tau)
    | .rd8 =>
      if c.L = l.dsc then (c.tick.upd p { l with pc := .exS8 }, .tau)
      else (c.tick.upd p { l with pc := .fad }, .tau)
    | .exS8 =>
      match l.dsc with
      | some δ =>
        ({ (c.tick.upd p { l with pc := .exE8 }) with started := Function.update c.started δ true },
          .exS δ)
      | none => (c.tick, .tau)
    | .exE8 =>
      match l.dsc with
      | some δ =>
        ({ (c.tick.upd p { l with pc := .fad }) with done := Function.update c.done δ true },
          .exE δ)
      | none => (c.tick, .tau)
    | .fad =>
      ({ (c.tick.upd p { l with pc := .ret }) with C := c.C - 1, act := c.act.erase p }, .tau)
    | .ret =>
      match l.dsc with
      | some δ =>
        if c.done δ then
          ({ (c.tick.upd p { l with pc := .idle, dsc := none }) with
              retT := Function.update c.retT δ true }, .resp p δ true)
        else
          ({ (c.tick.upd p { l with pc := .idle, dsc := none }) with
              failed := Function.update c.failed p
                (Function.update (c.failed p) l.call true) }, .resp p δ false)
      | none => (c.tick, .tau)

/-- Reachable configurations of Algorithm 1. -/
abbrev Reach (c : Cfg P D) : Prop := Reachable init (step own) c

end Podc.RandomizedWaitFreeLocks.Alg1
