/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2019.ReconfigurableCommit.Spec

/-!
# The atomic commit protocol of Figure 1 (Bravo–Gotsman, PODC 2019, §3)

A transition-system model of the message-passing protocol of Figure 1 of
*M. Bravo, A. Gotsman. Reconfigurable Atomic Transaction Commit* (arXiv 1906.01365v1).

**Model.**
* Asynchronous message passing. Every ordered pair of processes has a channel `net src dst`
  (a list, oldest first). A `deliver src dst i` step removes the `i`-th message of the channel and
  runs its handler, provided the handler's precondition (`pre:`) holds; otherwise the step is
  disabled and the message stays in the channel. Reliable FIFO channels are the special case
  `i = 0` (`Action.IsFIFO`); the safety proof allows any `i` (so it also covers non-FIFO
  channels), the counterexamples only use `i = 0`.
* Crash-stop failures need no modelling for safety: a crashed process simply takes no further
  steps, and every finite execution with crashes is a finite execution of this system.
* The configuration service (CS) is a reliable shared object `cs s` (the list of configurations of
  shard `s`, indexed by epoch). `CONFIG_CHANGE` messages from the CS are modelled by the step
  `configChange`, which lets a process adopt any stored configuration of another shard with a
  higher epoch (this over-approximates the CS's notifications).
* Clients are not processes: `certify(t, l)` is a step at the coordinator `p` (any replica
  process), and the response `decide(t, d)` is recorded in the history when the first
  `DECISION(t, d)` message is sent to `client(t)` (line 27).
* The arrays `txn`, `payload`, `vote` are always written together (lines 10–16, 24, 66), so they
  are stored as one array `ent` of triples. Arrays carry their length `len` (the largest slot
  ever written), which makes `max{k | phase[k] ≠ start}` (line 59) computable.
* Line 24 writes slot `k` (the figure says `next`, an evident typo: a follower's `next` is
  never maintained).
* Line 56 is printed as `when received NEW_CONFIG(new_epoch, M)`, with the state variable
  `new_epoch` in the message pattern and an unbound `e` at line 58. By the paper's convention
  (lines 45, 51; App. C lines 141, 148, whose "checks" are exactly such patterns) this is a
  match: the handler fires only if the message epoch equals the current `new_epoch`, which is
  "the check in line 56" cited in the proof of Invariant 3. `Params.fixNewConfig = true` adds
  the weaker precondition `e ≥ new_epoch`; every step of the paper's protocol (with `=`) is
  then a step of this model, so the safety theorem covers it. `fixNewConfig = false` is the
  binder reading (`NEW_CONFIG(e, M)`, no check), which is unsafe (`theorem_4_1_false_printed`).
* `compute_membership` (line 48) is any set `M` containing the new leader, consisting of shard
  members that responded to this probing or fresh processes (never members of a configuration of
  the shard), as the paper prescribes; additionally `M` has at least two members (`f ≥ 1`: at least
  one follower). With a single member the coordinator's wait at line 26 is vacuous.

Auxiliary (ghost) variables that never influence transitions: `hist` (the TCS history), `sent`
(every message ever sent), `started s e` (the leader of epoch `e` of shard `s` has processed
`NEW_CONFIG`), `elog s e` (the arrays `txn, payload, vote` of the leader of epoch `e` while it
leads `e`; each entry is tagged with the epoch in which it was created), `base s e` (the same at
the moment the leader started `e`), and `vinfo s e k` (when the leader of `e` computed the vote of
slot `k` at line 12: the slots whose payloads formed `L₁`, `L₂`, and the length of the history).
-/

namespace Podc.ReconfigurableCommit

/-- Process status. -/
inductive Status
  | leader
  | follower
  | reconfiguring
  deriving DecidableEq, Repr

/-- Transaction phase. -/
inductive Phase
  | start
  | prepared
  | decided
  deriving DecidableEq, Repr

/-- A configuration of a shard: members and leader (the epoch is its index in the CS). -/
structure Config (P : Type) where
  members : Finset P
  leader : P
  deriving DecidableEq

/-- The arrays of a process: `ent k = (txn[k], payload[k], vote[k])`, `dec`, `phase`, and the
length `len` (all slots `> len` are untouched). -/
structure Arrays (T Pl : Type) where
  ent : ℕ → Option (T × Pl × Dec)
  dec : ℕ → Option Dec
  phase : ℕ → Phase
  len : ℕ

namespace Arrays

variable {T Pl : Type}

/-- Initial (empty) arrays. -/
def empty : Arrays T Pl := ⟨fun _ => none, fun _ => none, fun _ => .start, 0⟩

/-- `max{k | phase[k] ≠ start}` (line 59), `0` if there is none. -/
def maxSlot (a : Arrays T Pl) : ℕ := Nat.findGreatest (fun k => a.phase k ≠ .start) a.len

/-- A slot `k` with `txn[k] = t`, if any (line 6). -/
def findSlot [DecidableEq T] (a : Arrays T Pl) (t : T) : Option ℕ :=
  (List.range (a.len + 1)).find? fun k => decide ((a.ent k).map (·.1) = some t)

end Arrays

/-- Protocol messages (Figure 1). `prepare t none` is `PREPARE(t, ⊥)`. -/
inductive Msg (T Pl S P : Type)
  | prepare (t : T) (l : Option Pl)
  | prepareAck (e : ℕ) (s : S) (k : ℕ) (t : T) (l : Pl) (d : Dec)
  | accept (e k : ℕ) (t : T) (l : Pl) (d : Dec)
  | acceptAck (s : S) (e k : ℕ) (t : T) (d : Dec)
  | decision (e k : ℕ) (d : Dec)
  | probe (e : ℕ)
  | probeAck (init : Bool) (e : ℕ) (s : S)
  | newConfig (e : ℕ) (M : Finset P)
  | newState (e : ℕ) (M : Finset P) (a : Arrays T Pl)

/-- Local state of a process (Figure 1). `acceptAcks` and `probeAcks` buffer the received
`ACCEPT_ACK(s, e, k, t, d)` (with their sender) and `PROBE_ACK(b, e, s)` messages, on which the
handlers at lines 26, 45 and 51 wait. -/
structure LState (T Pl S P : Type) where
  status : Status
  epoch : S → ℕ
  members : S → Finset P
  leader : S → P
  next : ℕ
  arr : Arrays T Pl
  initialized : Bool
  newEpoch : ℕ
  probing : Bool
  probedEpoch : ℕ
  probedMembers : Finset P
  reconEpoch : ℕ
  reconShard : S
  acceptAcks : List (P × S × ℕ × ℕ × T × Dec)
  probeAcks : List (P × Bool × ℕ × S)

/-- Parameters: sharding data, shard-local certification functions, the shard `home p` of each
process (replica groups of different shards are disjoint), the initial configuration (epoch `0`)
of each shard, and whether the `NEW_CONFIG` handler checks `e ≥ new_epoch`. -/
structure Params (T Pl S P : Type) where
  σ : Sharding T Pl S
  fs : S → Finset Pl → Pl → Dec
  gs : S → Finset Pl → Pl → Dec
  home : P → S
  init : S → Config P
  fixNewConfig : Bool

/-- A log entry `(txn, payload, vote)`. -/
abbrev Entry (T Pl : Type) := T × Pl × Dec

/-- Global state. `hist`, `sent`, `started`, `elog`, `base`, `vinfo` are ghost variables. -/
structure State (T Pl S P : Type) where
  loc : P → LState T Pl S P
  net : P → P → List (Msg T Pl S P)
  cs : S → List (Config P)
  hist : History T Pl
  sent : P → P → List (Msg T Pl S P)
  started : S → ℕ → Bool
  elog : S → ℕ → ℕ → Option (Entry T Pl × ℕ)
  base : S → ℕ → ℕ → Option (Entry T Pl × ℕ)
  vinfo : S → ℕ → ℕ → Option (Finset ℕ × Finset ℕ × ℕ)

/-- Steps. `deliver src dst i` delivers the `i`-th message of channel `src → dst`. -/
inductive Action (T Pl S P : Type)
  | certify (p : P) (t : T) (l : Pl)
  | deliver (src dst : P) (i : ℕ)
  | decide (p : P) (t : T) (ks : S → ℕ) (ds : S → Dec)
  | reconfigure (p : P) (s : S)
  | probeDone (p q : P) (M : Finset P)
  | probeSkip (p q : P)
  | configChange (p : P) (s : S) (e : ℕ)
  | retry (p : P) (k : ℕ)

/-- Deliveries respect FIFO order (only the oldest message of a channel is delivered). -/
def Action.IsFIFO {T Pl S P : Type} : Action T Pl S P → Prop
  | .deliver _ _ i => i = 0
  | _ => True

variable {T Pl S P : Type} [DecidableEq T] [DecidableEq Pl] [DecidableEq S] [DecidableEq P]
  [Fintype S]

instance (σ : Sharding T Pl S) (t : T) (l : Pl) : Decidable (σ.ValidPayload t l) :=
  inferInstanceAs (Decidable (∀ s, s ∉ σ.shards t → σ.proj l s = σ.eps))

namespace State

/-- Send, from `src`, the message `out b` (if any) to every process `b`. -/
def send (st : State T Pl S P) (src : P) (out : P → Option (Msg T Pl S P)) : State T Pl S P :=
  { st with
    net := fun a b => if a = src then (match out b with
      | some m => st.net a b ++ [m]
      | none => st.net a b) else st.net a b
    sent := fun a b => if a = src then (match out b with
      | some m => st.sent a b ++ [m]
      | none => st.sent a b) else st.sent a b }

/-- Send `m` from `src` to the single process `q`. -/
def send1 (st : State T Pl S P) (src q : P) (m : Msg T Pl S P) : State T Pl S P :=
  st.send src fun b => if b = q then some m else none

/-- Send `m` from `src` to every process in `M`. -/
def sendAll (st : State T Pl S P) (src : P) (M : Finset P) (m : Msg T Pl S P) :
    State T Pl S P :=
  st.send src fun b => if b ∈ M then some m else none

/-- Replace the local state of `p`. -/
def setLoc (st : State T Pl S P) (p : P) (ls : LState T Pl S P) : State T Pl S P :=
  { st with loc := Function.update st.loc p ls }

end State

/-- `t` has been certified in `h`. -/
def certified (h : History T Pl) (t : T) : Bool :=
  h.any fun
    | .certify t' _ => decide (t' = t)
    | .decide _ _ => false

/-- `t` has been decided in `h`. -/
def decided (h : History T Pl) (t : T) : Bool :=
  h.any fun
    | .decide t' _ => decide (t' = t)
    | .certify _ _ => false

variable (Pa : Params T Pl S P)

/-- Payloads `{payload[k] | k < n ∧ cond k}` for the vote computation (line 12). -/
def payloadsWhere (a : Arrays T Pl) (n : ℕ) (cond : ℕ → Bool) : Finset Pl :=
  ((List.range n).filterMap fun k => if cond k then (a.ent k).map (·.2.1) else none).toFinset

/-- Slots `{k < n | cond k, slot k filled}` (ghost, for `vinfo`). -/
def slotsWhere (a : Arrays T Pl) (n : ℕ) (cond : ℕ → Bool) : Finset ℕ :=
  (Finset.range n).filter fun k => cond k = true ∧ (a.ent k).isSome = true

/-- Update a ghost function at `(s, e, k)`. -/
def upd3 {α : Type} (g : S → ℕ → ℕ → α) (s : S) (e k : ℕ) (v : α) : S → ℕ → ℕ → α :=
  fun s' e' k' => if s' = s ∧ e' = e ∧ k' = k then v else g s' e' k'

/-- Update a ghost function at `(s, e)`. -/
def upd2 {α : Type} (g : S → ℕ → α) (s : S) (e : ℕ) (v : α) : S → ℕ → α :=
  fun s' e' => if s' = s ∧ e' = e then v else g s' e'

/-- Condition defining `L₁` (line 12): decided with decision `commit`. -/
def condL1 (a : Arrays T Pl) (k : ℕ) : Bool :=
  decide (a.phase k = .decided ∧ a.dec k = some .commit)

/-- Condition defining `L₂` (line 12): prepared with vote `commit`. -/
def condL2 (a : Arrays T Pl) (k : ℕ) : Bool :=
  decide (a.phase k = .prepared ∧ (a.ent k).map (·.2.2) = some .commit)

/-- The handler of message `m` from `q` at process `p` (the message is already removed from the
channel); `none` if its precondition fails. -/
def handle (st : State T Pl S P) (q p : P) : Msg T Pl S P → Option (State T Pl S P)
  -- lines 4–17
  | .prepare t lo =>
    let ls := st.loc p
    let s₀ := Pa.home p
    if ls.status = .leader then
      match ls.arr.findSlot t with
      | some k =>
        match ls.arr.ent k with
        | some (_, l', d') => some (st.send1 p q (.prepareAck (ls.epoch s₀) s₀ k t l' d'))
        | none => none
      | none =>
        let n := ls.next + 1
        let a := ls.arr
        let L₁ := payloadsWhere a n (condL1 a)
        let L₂ := payloadsWhere a n (condL2 a)
        let ld : Pl × Dec × Option (Finset ℕ × Finset ℕ × ℕ) := match lo with
          | some l => (l, (Pa.fs s₀ L₁ l).meet (Pa.gs s₀ L₂ l),
              some (slotsWhere a n (condL1 a), slotsWhere a n (condL2 a), st.hist.length))
          | none => (Pa.σ.eps, .abort, none)
        let a' : Arrays T Pl :=
          { a with ent := Function.update a.ent n (some (t, ld.1, ld.2.1)),
                   phase := Function.update a.phase n .prepared,
                   len := max a.len n }
        let e := ls.epoch s₀
        let st' := st.setLoc p { ls with next := n, arr := a' }
        let st' := { st' with
          elog := upd3 st.elog s₀ e n (some ((t, ld.1, ld.2.1), e))
          vinfo := upd3 st.vinfo s₀ e n ld.2.2 }
        some (st'.send1 p q (.prepareAck e s₀ n t ld.1 ld.2.1))
    else none
  -- lines 18–20
  | .prepareAck e s k t l d =>
    let ls := st.loc p
    if ls.epoch s = e then
      some (st.sendAll p (ls.members s \ {ls.leader s}) (.accept e k t l d))
    else none
  -- lines 21–25 (line 24 writes slot `k`)
  | .accept e k t l d =>
    let ls := st.loc p
    let s₀ := Pa.home p
    if ls.status = .follower ∧ ls.epoch s₀ = e then
      let a := ls.arr
      let a' : Arrays T Pl := if a.phase k = .start then
          { a with ent := Function.update a.ent k (some (t, l, d)),
                   phase := Function.update a.phase k .prepared,
                   len := max a.len k }
        else a
      some ((st.setLoc p { ls with arr := a' }).send1 p q (.acceptAck s₀ e k t d))
    else none
  -- buffered for line 26
  | .acceptAck s e k t d =>
    let ls := st.loc p
    some (st.setLoc p { ls with acceptAcks := (q, s, e, k, t, d) :: ls.acceptAcks })
  -- lines 30–32
  | .decision e k d =>
    let ls := st.loc p
    let s₀ := Pa.home p
    if (ls.status = .leader ∨ ls.status = .follower) ∧ e ≤ ls.epoch s₀ then
      let a := ls.arr
      let a' : Arrays T Pl :=
        { a with dec := Function.update a.dec k (some d),
                 phase := Function.update a.phase k .decided,
                 len := max a.len k }
      some (st.setLoc p { ls with arr := a' })
    else none
  -- lines 40–44
  | .probe e =>
    let ls := st.loc p
    if ls.newEpoch ≤ e then
      some ((st.setLoc p { ls with status := .reconfiguring, newEpoch := e }).send1 p q
        (.probeAck ls.initialized e (Pa.home p)))
    else none
  -- buffered for lines 45, 51
  | .probeAck b e s =>
    let ls := st.loc p
    some (st.setLoc p { ls with probeAcks := (q, b, e, s) :: ls.probeAcks })
  -- lines 56–60 (the check `e ≥ new_epoch` only if `fixNewConfig`)
  | .newConfig e M =>
    let ls := st.loc p
    let s₀ := Pa.home p
    if Pa.fixNewConfig = false ∨ ls.newEpoch ≤ e then
      let ls' := { ls with
        status := .leader
        epoch := Function.update ls.epoch s₀ e
        members := Function.update ls.members s₀ M
        leader := Function.update ls.leader s₀ p
        next := ls.arr.maxSlot }
      let st' := st.setLoc p ls'
      -- ghost: the new epoch's log is the leader's arrays, entries keeping their origin tags
      let lg : ℕ → Option (Entry T Pl × ℕ) := fun k =>
        if (ls.arr.ent k).isSome then st.elog s₀ (ls.epoch s₀) k else none
      let st' := { st' with
        started := upd2 st.started s₀ e true
        elog := fun s' e' => if s' = s₀ ∧ e' = e then lg else st.elog s' e'
        base := fun s' e' => if s' = s₀ ∧ e' = e then lg else st.base s' e' }
      some (st'.sendAll p (M \ {p}) (.newState e M ls.arr))
    else none
  -- lines 61–66
  | .newState e M a =>
    let ls := st.loc p
    let s₀ := Pa.home p
    if ls.newEpoch ≤ e then
      some (st.setLoc p { ls with
        initialized := true
        status := .follower
        epoch := Function.update ls.epoch s₀ e
        members := Function.update ls.members s₀ M
        leader := Function.update ls.leader s₀ q
        arr := a })
    else none

/-- The meet `⊓_{s ∈ shards(t)} dₛ`. -/
def meetOver (sh : Finset S) (ds : S → Dec) : Dec :=
  if ∀ s ∈ sh, ds s = .commit then .commit else .abort

/-- `r` responded to the current probing of `ls` (a buffered `PROBE_ACK(_, recon_epoch,
recon_shard)` from `r`). -/
def responded (ls : LState T Pl S P) (r : P) : Bool :=
  ls.probeAcks.any fun x => decide (x.1 = r ∧ x.2.2.1 = ls.reconEpoch ∧ x.2.2.2 = ls.reconShard)

/-- One step of the protocol; `none` if the action is not enabled. -/
def step (st : State T Pl S P) : Action T Pl S P → Option (State T Pl S P)
  -- lines 1–3: the coordinator `p` sends `PREPARE(t, l | s)` to `leader[s]`, `s ∈ shards(t)`
  | .certify p t l =>
    if certified st.hist t = false ∧ Pa.σ.ValidPayload t l then
      let ls := st.loc p
      let st' := { st with hist := st.hist ++ [Event.certify t l] }
      some (st'.send p fun b =>
        if Pa.home b ∈ Pa.σ.shards t ∧ ls.leader (Pa.home b) = b then
          some (.prepare t (some (Pa.σ.proj l (Pa.home b)))) else none)
    else none
  | .deliver src dst i =>
    match (st.net src dst)[i]? with
    | some m =>
      let net' := Function.update st.net src
        (Function.update (st.net src) dst ((st.net src dst).eraseIdx i))
      handle Pa { st with net := net' } src dst m
    | none => none
  -- lines 26–29
  | .decide p t ks ds =>
    let ls := st.loc p
    if ∀ s ∈ Pa.σ.shards t, ∀ r ∈ ls.members s \ {ls.leader s},
        (r, s, ls.epoch s, ks s, t, ds s) ∈ ls.acceptAcks then
      let d := meetOver (Pa.σ.shards t) ds
      let st' := if decided st.hist t then st else { st with hist := st.hist ++ [.decide t d] }
      some (st'.send p fun b =>
        if Pa.home b ∈ Pa.σ.shards t ∧ b ∈ ls.members (Pa.home b) then
          some (.decision (ls.epoch (Pa.home b)) (ks (Pa.home b)) d) else none)
    else none
  -- lines 33–39
  | .reconfigure p s =>
    let ls := st.loc p
    match ls.probing, (st.cs s).getLast? with
    | false, some c =>
      let pe := (st.cs s).length - 1
      let ls' : LState T Pl S P := { ls with
        probing := true
        probedEpoch := pe
        probedMembers := c.members
        reconEpoch := pe + 1
        reconShard := s }
      some ((st.setLoc p ls').sendAll p c.members (.probe (pe + 1)))
    | _, _ => none
  -- lines 45–50 (`M` is the result of `compute_membership`)
  | .probeDone p q M =>
    let ls := st.loc p
    let s := ls.reconShard
    if ls.probing = true ∧ (q, true, ls.reconEpoch, s) ∈ ls.probeAcks ∧ q ∈ M ∧ 2 ≤ M.card ∧
        ∀ r ∈ M, Pa.home r = s ∧ (responded ls r = true ∨ ∀ c ∈ st.cs s, r ∉ c.members) then
      let st' := st.setLoc p { ls with probing := false }
      if (st.cs s).length = ls.reconEpoch then
        let st' := { st' with cs := Function.update st.cs s (st.cs s ++ [Config.mk M q]) }
        some (st'.send1 p q (.newConfig ls.reconEpoch M))
      else some st'
    else none
  -- lines 51–55
  | .probeSkip p q =>
    let ls := st.loc p
    let s := ls.reconShard
    if ls.probing = true ∧ (q, false, ls.reconEpoch, s) ∈ ls.probeAcks ∧
        q ∈ ls.probedMembers ∧
        (ls.probeAcks.any fun x => decide (x.2 = (true, ls.reconEpoch, s))) = false then
      match (st.cs s)[ls.probedEpoch - 1]? with
      | some c =>
        let ls' : LState T Pl S P := { ls with
          probedEpoch := ls.probedEpoch - 1
          probedMembers := c.members }
        some ((st.setLoc p ls').sendAll p c.members (.probe ls.reconEpoch))
      | none => none
    else none
  -- lines 67–69 (CONFIG_CHANGE from the CS)
  | .configChange p s e =>
    let ls := st.loc p
    match (st.cs s)[e]? with
    | some c =>
      if s ≠ Pa.home p ∧ ls.epoch s < e then
        let ls' : LState T Pl S P := { ls with
          epoch := Function.update ls.epoch s e
          members := Function.update ls.members s c.members
          leader := Function.update ls.leader s c.leader }
        some (st.setLoc p ls')
      else none
    | none => none
  -- lines 70–73
  | .retry p k =>
    let ls := st.loc p
    match ls.arr.ent k with
    | some (t, _, _) =>
      if ls.arr.phase k = .prepared then
        some (st.send p fun b =>
          if Pa.home b ∈ Pa.σ.shards t ∧ ls.leader (Pa.home b) = b then
            some (.prepare t none) else none)
      else none
    | none => none

/-- The initial state: every shard is in its initial configuration (epoch `0`), whose members are
initialized; all other processes are uninitialized (fresh). -/
def initState : State T Pl S P where
  loc p :=
    { status := if (Pa.init (Pa.home p)).leader = p then .leader
        else if p ∈ (Pa.init (Pa.home p)).members then .follower else .reconfiguring
      epoch := fun _ => 0
      members := fun s => (Pa.init s).members
      leader := fun s => (Pa.init s).leader
      next := 0
      arr := .empty
      initialized := decide (p ∈ (Pa.init (Pa.home p)).members)
      newEpoch := 0
      probing := false
      probedEpoch := 0
      probedMembers := ∅
      reconEpoch := 0
      reconShard := Pa.home p
      acceptAcks := []
      probeAcks := [] }
  net _ _ := []
  cs s := [Pa.init s]
  hist := []
  sent _ _ := []
  started _ e := decide (e = 0)
  elog _ _ _ := none
  base _ _ _ := none
  vinfo _ _ _ := none

/-- Run a list of actions from a state. -/
def run : State T Pl S P → List (Action T Pl S P) → Option (State T Pl S P)
  | st, [] => some st
  | st, a :: as => (step Pa st a).bind fun st' => run st' as

/-- One step of the transition system. -/
def Step (st st' : State T Pl S P) : Prop := ∃ a, step Pa st a = some st'

/-- Reachable states. -/
def Reachable (st : State T Pl S P) : Prop := Relation.ReflTransGen (Step Pa) (initState Pa) st

theorem reachable_of_run {acts : List (Action T Pl S P)} {st₀ st : State T Pl S P}
    (h₀ : Reachable Pa st₀) (h : run Pa st₀ acts = some st) : Reachable Pa st := by
  induction acts generalizing st₀ with
  | nil => cases h; exact h₀
  | cons a as ih =>
    simp only [run, Option.bind_eq_some_iff] at h
    obtain ⟨st', h1, h2⟩ := h
    exact ih (h₀.tail ⟨a, h1⟩) h2

/-- Well-formed initial configurations: the leader is a member, members belong to the shard, and
there is at least one follower. -/
def ValidInit : Prop :=
  ∀ s, (Pa.init s).leader ∈ (Pa.init s).members ∧ (∀ p ∈ (Pa.init s).members, Pa.home p = s) ∧
    2 ≤ (Pa.init s).members.card

end Podc.ReconfigurableCommit
