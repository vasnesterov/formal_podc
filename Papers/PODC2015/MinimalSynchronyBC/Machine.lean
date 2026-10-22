import Cslib.Computability.Distributed.Byzantine.PartialSync.Model

/-!
# Figures 1–4 as a partially synchronous algorithm

The consensus algorithm of Figure 4, with its building blocks CB-broadcast (Figure 1),
adopt-commit (Figure 2) and eventual agreement (Figure 3), written as an `Algorithm` of CSLib's
partially synchronous Byzantine model `Cslib.Byzantine.PartialSync`: processes `Fin n`,
authenticated point-to-point channels, discrete time, every correct process takes one step per
tick; a run fixes the faulty set, what faulty processes send, and the delivery time of every
batch of messages. The per-channel timing assumption of the paper (an eventual
`⟨t+1⟩bisource`) is expressed on runs (`Cslib.Byzantine.PartialSync.Run.BisourceValid`).

**Reliable broadcast is a primitive**, as in the paper (which only uses its properties): an
RB-broadcast of `v` in instance `k` is the message `rb k v` sent to all; a process RB-delivers the
*first* `rb k _` message of each sender (RB-Unicity). For correct senders this gives
RB-Validity and RB-Termination-1/2 on reliable channels; for faulty senders the properties are
constraints on what they send (`RBAdmissible`).

A correct process keeps (`St`) all received messages with their senders, its program counter
(`PC`: where the main thread of Figure 4 waits), its estimate `est`, the value `val` ea-proposed
in the current round, the rounds for which it sent `EA_COORD`/`EA_RELAY`, its running timers,
logs of its EA and AC returns, its decision, and its outbox for the current tick. One step:

1. receive the inbox (appended to `rcv` in sender order) and advance the timers by one tick;
2. lines 11–14 of Figure 3 (`coordSt`): if it is `coord r` and received `EA_PROP2[r]` from a
   process of `F r`, broadcast `EA_COORD[r](w)` once, `w` from the first such message;
3. lines 15–19 (`relaySt`): on `EA_COORD[r](v)` from `coord r`, or on expiry of `timer[r]`,
   broadcast `EA_RELAY[r]` once (`v`, resp. `⊥`) and disable the timer;
4. line 9 of Figure 4 (`decideSt`): decide `v` once `DECIDE(v)` was RB-delivered from `t + 1`
   processes;
5. the main thread (`mainSt`), run until it blocks (at most `fuel` transitions per tick).

All "pick any" choices of the paper are resolved by arrival order: CB returns the value of
`cb_valid` whose first `rb` message arrived first; the `n − t` messages of a wait statement are the
first `n − t` qualifying ones; the most frequent value is the first one with maximal count. In the
counterexamples every such choice is forced (only one candidate).

`Params.eaRound = some r` runs the EA object alone (Figure 3, round `r`, the input is `val`); after
returning, the process stops (`PC.done`). `Params.eaRound = none` runs Figure 4.
-/

namespace MinimalSynchronyBC

open Cslib.Byzantine.PartialSync

/-- Reliable-broadcast instances. -/
inductive Key where
  /-- `CB[0]` of Figure 4 (`VALID` values). -/
  | valid
  /-- `CB[r]` of round `r` of the EA object (`EA_PROP1`). -/
  | eaProp1 (r : ℕ)
  /-- The CB instance inside `AC_OBJECT[r]` (`AC_PROP`). -/
  | acProp (r : ℕ)
  /-- The `AC_EST` messages of `AC_OBJECT[r]`. -/
  | acEst (r : ℕ)
  /-- The `DECIDE` message RB-broadcast in round `r`. -/
  | decide (r : ℕ)
  deriving DecidableEq

/-- Messages. -/
inductive Msg (V : Type) where
  /-- An RB-broadcast message of instance `k`. -/
  | rb (k : Key) (v : V)
  /-- `EA_PROP2[r](v)`. -/
  | prop2 (r : ℕ) (v : V)
  /-- `EA_COORD[r](v)`. -/
  | coord (r : ℕ) (v : V)
  /-- `EA_RELAY[r](v)` (`none` is `⊥`). -/
  | relay (r : ℕ) (v : Option V)
  deriving DecidableEq

/-- Where the main thread waits. -/
inductive PC where
  /-- Figure 4 line 1 (`CB[0]`, Figure 1 line 2). -/
  | cb0
  /-- Figure 3 line 1 (`CB[r]`). -/
  | eaCB (r : ℕ)
  /-- Figure 3 line 3. -/
  | eaW3 (r : ℕ)
  /-- Figure 3 line 6. -/
  | eaW6 (r : ℕ)
  /-- Figure 2 line 1 (CB of `AC_OBJECT[r]`). -/
  | acCB (r : ℕ)
  /-- Figure 2 line 3. -/
  | acW3 (r : ℕ)
  /-- EA object alone: returned. -/
  | done
  deriving DecidableEq

/-- Parameters: resilience `t`, coordinators `coord r`, the sets `F r`, timer values
(`timeout r = r` in the paper), the mode, and the number of main-thread transitions per tick. -/
structure Params (n : ℕ) where
  t : ℕ
  coord : ℕ → Fin n
  F : ℕ → Finset (Fin n)
  timeout : ℕ → ℕ := id
  eaRound : Option ℕ := none
  fuel : ℕ := 8
  /-- `true`: a **repair** (not in the paper): a process returning at line 4 also sets
  `timer[r]` (line 5), so that it relays in round `r`. `false`: the paper's algorithm. -/
  fixTimer : Bool := false

/-- Local state of a process. -/
structure St (n : ℕ) (V : Type) where
  inp : V
  pc : PC
  est : V
  val : V
  rcv : List (Fin n × Msg V) := []
  coordSent : List ℕ := []
  relaySent : List ℕ := []
  /-- Running timers: (round, remaining ticks). -/
  timers : List (ℕ × ℕ) := []
  /-- EA returns: (round, value). -/
  eaRet : List (ℕ × V) := []
  /-- AC returns: (round, committed?, value). -/
  acRet : List (ℕ × Bool × V) := []
  dec : Option V := none
  out : List (Msg V) := []
  deriving DecidableEq

variable {n : ℕ} {V : Type} [DecidableEq V]

/-! ### Reading the received messages -/

/-- Keep the first entry of every sender. -/
def firstPerSender {α : Type} : List (Fin n × α) → List (Fin n × α)
  | [] => []
  | e :: l => e :: (firstPerSender l).filter fun e' => e'.1 ≠ e.1

/-- The RB-delivered messages of instance `k`: first `rb k _` of each sender, in arrival order. -/
def rbDel (rcv : List (Fin n × Msg V)) (k : Key) : List (Fin n × V) :=
  firstPerSender <| rcv.filterMap fun e => match e.2 with
    | .rb k' v => if k' = k then some (e.1, v) else none
    | _ => none

/-- Number of processes from which `v` was RB-delivered in instance `k`. -/
def rbCount (rcv : List (Fin n × Msg V)) (k : Key) (v : V) : ℕ :=
  ((rbDel rcv k).filter fun e => e.2 = v).length

/-- `cb_valid` of the CB instance `k` (Figure 1 line 4): the values RB-delivered from `t + 1`
processes, in the order of their first delivery. -/
def cbValid (t : ℕ) (rcv : List (Fin n × Msg V)) (k : Key) : List V :=
  ((rbDel rcv k).map Prod.snd).dedup.filter fun v => t + 1 ≤ rbCount rcv k v

/-- The first `EA_PROP2[r]` message of every sender. -/
def prop2Del (rcv : List (Fin n × Msg V)) (r : ℕ) : List (Fin n × V) :=
  firstPerSender <| rcv.filterMap fun e => match e.2 with
    | .prop2 r' v => if r' = r then some (e.1, v) else none
    | _ => none

/-- The first `EA_RELAY[r]` message of every sender. -/
def relayDel (rcv : List (Fin n × Msg V)) (r : ℕ) : List (Fin n × Option V) :=
  firstPerSender <| rcv.filterMap fun e => match e.2 with
    | .relay r' v => if r' = r then some (e.1, v) else none
    | _ => none

/-- Number of occurrences of `v` in a list. -/
def cnt (l : List V) (v : V) : ℕ := (l.filter fun x => x = v).length

/-- The most frequent value of a list (the first one with maximal count), `d` if empty. -/
def mostFrequent (l : List V) (d : V) : V :=
  l.foldl (fun b x => if cnt l b < cnt l x then x else b) (l.headD d)

section Stages

variable (prm : Params n)

/-- Start round `r` of the EA object with value `x` (Figure 3 line 1: `CB[r].CB_broadcast`). -/
def startEA (s : St n V) (r : ℕ) (x : V) : St n V :=
  { s with val := x, pc := .eaCB r, out := s.out ++ [.rb (.eaProp1 r) x] }

/-- The EA object returns `v` in round `r`: Figure 4 lines 5–6 (or stop, for the EA object
alone). -/
def eaReturn (s : St n V) (r : ℕ) (v : V) : St n V :=
  let s := { s with eaRet := s.eaRet ++ [(r, v)] }
  match prm.eaRound with
  | some _ => { s with pc := .done }
  | none =>
    let e := if v ∈ cbValid prm.t s.rcv .valid then v else s.est
    { s with est := e, pc := .acCB r, out := s.out ++ [.rb (.acProp r) e] }

/-- One transition of the main thread, `none` if it is blocked. -/
def mainStep (s : St n V) : Option (St n V) :=
  if s.dec.isSome then none else
  match s.pc with
  | .cb0 => match (cbValid prm.t s.rcv .valid).head? with
    | some v => some (startEA { s with est := v } 1 v)
    | none => none
  | .eaCB r => match (cbValid prm.t s.rcv (.eaProp1 r)).head? with
    | some a => some { s with pc := .eaW3 r, out := s.out ++ [.prop2 r a] }
    | none => none
  | .eaW3 r =>
    let L := (prop2Del s.rcv r).filter fun e => e.2 ∈ cbValid prm.t s.rcv (.eaProp1 r)
    if n - prm.t ≤ L.length then
      let Q := (L.take (n - prm.t)).map Prod.snd
      match Q.head? with
      | some v =>
        if Q.all (· = v) then
          some (eaReturn prm (if prm.fixTimer then
            { s with timers := s.timers ++ [(r, prm.timeout r)] } else s) r v)
        else some { s with pc := .eaW6 r, timers := s.timers ++ [(r, prm.timeout r)] }
      | none => some { s with pc := .eaW6 r, timers := s.timers ++ [(r, prm.timeout r)] }
    else none
  | .eaW6 r =>
    let Rl := relayDel s.rcv r
    if n - prm.t ≤ Rl.length then
      match Rl.findSome? (fun e => if e.1 ∈ prm.F r then e.2 else none) with
      | some v => some (eaReturn prm s r v)
      | none => some (eaReturn prm s r s.val)
    else none
  | .acCB r => match (cbValid prm.t s.rcv (.acProp r)).head? with
    | some e => some { s with pc := .acW3 r, out := s.out ++ [.rb (.acEst r) e] }
    | none => none
  | .acW3 r =>
    let L := (rbDel s.rcv (.acEst r)).filter fun e => e.2 ∈ cbValid prm.t s.rcv (.acProp r)
    if n - prm.t ≤ L.length then
      let Q := (L.take (n - prm.t)).map Prod.snd
      let w := mostFrequent Q s.est
      let c := Q.all (· = w)
      let s := { s with est := w, acRet := s.acRet ++ [(r, c, w)],
                        out := s.out ++ (if c then [.rb (.decide r) w] else []) }
      some (startEA s (r + 1) w)
    else none
  | .done => none

/-- Run the main thread for at most `k` transitions. -/
def mainSt : ℕ → St n V → St n V
  | 0, s => s
  | k + 1, s => match mainStep prm s with
    | some s' => mainSt k s'
    | none => s

/-- Lines 11–14 of Figure 3: the coordinator of round `r` champions the value of the first
`EA_PROP2[r]` message received from a process of `F r`. -/
def coordSt (p : Fin n) (s : St n V) : St n V :=
  let cands := s.rcv.filterMap fun e => match e.2 with
    | .prop2 r w => if e.1 ∈ prm.F r ∧ prm.coord r = p then some (r, w) else none
    | _ => none
  cands.foldl (fun s e => if e.1 ∈ s.coordSent then s
    else { s with coordSent := s.coordSent ++ [e.1], out := s.out ++ [.coord e.1 e.2] }) s

/-- Lines 15–19 of Figure 3: relay the coordinator's value, or `⊥` when the timer expired. -/
def relaySt (s : St n V) : St n V :=
  let cands := s.rcv.filterMap fun e => match e.2 with
    | .coord r v => if e.1 = prm.coord r then some (r, some v) else none
    | _ => none
  let exp := (s.timers.filter fun e => e.2 = 0).map fun e => (e.1, (none : Option V))
  (cands ++ exp).foldl (fun s e => if e.1 ∈ s.relaySent then s
    else { s with relaySent := s.relaySent ++ [e.1], timers := s.timers.filter (·.1 ≠ e.1),
                  out := s.out ++ [.relay e.1 e.2] })
    { s with timers := s.timers.filter fun e => e.2 ≠ 0 }

/-- Senders from which `DECIDE(v)` was RB-delivered (in some round). -/
def decSenders (rcv : List (Fin n × Msg V)) (v : V) : List (Fin n) :=
  (rcv.filterMap fun e => match e.2 with
    | .rb (.decide r) _ => if (rbDel rcv (.decide r)).contains (e.1, v) then some e.1 else none
    | _ => none).dedup

/-- Line 9 of Figure 4. -/
def decideSt (s : St n V) : St n V :=
  match s.dec with
  | some _ => s
  | none =>
    let cands := s.rcv.filterMap fun e => match e.2 with
      | .rb (.decide _) v => some v
      | _ => none
    match cands.find? (fun v => prm.t + 1 ≤ (decSenders s.rcv v).length) with
    | some v => { s with dec := some v }
    | none => s

/-- One step of a correct process. -/
def step (p : Fin n) (s : St n V) (ib : Fin n → List (Msg V)) : St n V :=
  let s := { s with rcv := s.rcv ++ (List.finRange n).flatMap (fun q => (ib q).map fun m => (q, m)),
                    out := [], timers := s.timers.map fun e => (e.1, e.2 - 1) }
  mainSt prm prm.fuel (decideSt prm (relaySt prm (coordSt prm p s)))

/-- Initial state: Figure 4 line 1 (`CB[0].CB_broadcast VALID(v)`), or Figure 3 line 1 for the
EA object alone. -/
def init (x : V) : St n V :=
  match prm.eaRound with
  | some r => { inp := x, pc := .eaCB r, est := x, val := x, out := [.rb (.eaProp1 r) x] }
  | none => { inp := x, pc := .cb0, est := x, val := x, out := [.rb .valid x] }

end Stages

/-- **The algorithm of Figure 4** (with Figures 1–3), or the EA object of Figure 3 alone. -/
def alg (prm : Params n) : Algorithm (Fin n) (Msg V) (St n V) V V where
  init _ x := init prm x
  step := step prm
  send _ s _ := s.out
  decide _ s := s.dec

/-- `p` returns `v` from `EA_propose(r, -)` by time `τ`. -/
def EAReturns (prm : Params n) (R : Run (Fin n) (Msg V) V) (p : Fin n) (r : ℕ) (v : V)
    (τ : ℕ) : Prop :=
  (r, v) ∈ (R.st (alg prm) τ p).eaRet

/-- Reliable broadcast by faulty processes: each instance carries a single value, sent to every
correct process at the same time, and not lost. Together with the first-message rule this gives
RB-Unicity, RB-Validity and RB-Termination-1/2 for faulty senders. -/
def RBAdmissible (R : Run (Fin n) (Msg V) V) : Prop :=
  ∀ q ∈ R.faulty, ∀ k v τ p, p ∉ R.faulty → Msg.rb k v ∈ R.byz q τ p →
    (∀ τ' p' v', p' ∉ R.faulty → Msg.rb k v' ∈ R.byz q τ' p' → v' = v) ∧
    ∀ p' ∉ R.faulty, Msg.rb k v ∈ R.byz q τ p' ∧ τ ≤ R.dl q τ p'

end MinimalSynchronyBC
