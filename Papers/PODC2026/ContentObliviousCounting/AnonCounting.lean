import Podc.ContentOblivious.Compose

/-!
# Counting in an anonymous oriented ring with a leader (Section 5, Algorithms 1–4)

Chalopin, Chang, Di Luna, Zhou, *Efficient Counting and Simulation in Content-Oblivious Rings*,
PODC 2026 (arXiv 2603.28260), Section 5.

## Model

Oriented ring `Podc.ContentOblivious.oriented n` on `ZMod n` (`n ≥ 1`, including the self-loop
`n = 1` and the double link `n = 2`); `Port1 = true` is the clockwise port, linked to `Port0 = false`
of the clockwise neighbour. Asynchronous, fully defective (content-oblivious) channels, adversarial
scheduler, no failures, deterministic anonymous nodes. The only input is the leader flag (`true` at
exactly one node). See `Podc/ContentOblivious/Model.lean`.

## Encoding of the pseudo-code

Each blocking `receive` of Algorithms 1–4 is a program counter (`PC`); a port-specific receive is
`ready` only on that port, "receive a message on port `q`" is ready on both ports. Each reception
executes the code up to the next `receive`. The local variables `phase`, `counted`, `relayed` of
`NonLeader`, the global variable `myPhase` (`none` = never written, e.g. at the original leader),
`count` of `Leader`, and the list `L` of `RcvCount` (field `bits`; `SndCount` keeps there the bits
still to be sent) are record fields.

Ambiguities of the pseudo-code, fixed here:
* `SndCount` sends the binary digits of `count` least significant first (`Nat.digits 2`), so
  `count = 0` sends no data bits; `RcvCount` returns `Nat.ofDigits 2 L`.
* `SndCount`'s `return n`: the last leader terminates after `SndCount` (state `doneL`), with output
  `n = i(i-1)/2 + count + 1`, where `i` is its phase.
* A reception by a `NonLeader` at line 2 with `q = 1` executes lines 13–14 and then either becomes the
  new leader (lines 15–16) or waits at line 20.
* The leader's initial record has `counted = true`, `relayed = 0` (unused by `Leader`; `NonLeader`
  re-initialises them when the leader steps down, line 17 of Algorithm 2).
-/

namespace Podc.ContentOblivious.AnonCounting

open Podc.ContentOblivious

/-- Program counters: one per blocking `receive` of Algorithms 1–4 (plus the two final states). -/
inductive PC where
  /-- Algorithm 1, line 2: `receive a message on port q` (main loop of `NonLeader`). -/
  | main
  /-- Algorithm 1, line 10: `receive a message on port 1` (relaying a probe back). -/
  | relay
  /-- Algorithm 1, line 16: `receive a message on port 0` (new leader awaiting confirmation). -/
  | newLeader
  /-- Algorithm 1, line 20: `receive a message on port q` (after relaying a CCW pulse). -/
  | wait2
  /-- Algorithm 2, line 4: `receive a message on port q` (awaiting the probe's return). -/
  | probe
  /-- Algorithm 2, line 9: `receive three messages on port 1`; `k` received so far. -/
  | fin (k : ℕ)
  /-- Algorithm 2, line 13: `receive a message on port 1` (transfer pulse). -/
  | tr1
  /-- Algorithm 2, line 14: `receive a message on port 0` (confirmation pulse). -/
  | tr2
  /-- Algorithm 3, line 4 or 7: receive two messages for the current bit; `got` received so far. -/
  | sndBit (got : ℕ)
  /-- Algorithm 3, line 9: `receive a message on port 0`. -/
  | sndEnd1
  /-- Algorithm 3, line 11: `receive a message on port 1`. -/
  | sndEnd2
  /-- Algorithm 4, line 3: `receive a message on port q`. -/
  | rcvQ
  /-- Algorithm 4, line 5: `receive a message on port u`, after receiving on port `q`. -/
  | rcvU (q : Bool)
  /-- The (last) leader has returned from `SndCount`. -/
  | doneL
  /-- A non-leader has returned from `RcvCount`. -/
  | doneN
  deriving DecidableEq

/-- Local state of a node. -/
structure St where
  pc : PC
  /-- `phase` (argument of `NonLeader` / `Leader`). -/
  phase : ℕ
  /-- `counted` (argument of `NonLeader`). -/
  counted : Bool
  /-- `relayed` (argument of `NonLeader`). -/
  relayed : ℕ
  /-- The global variable `myPhase`; `none` while undefined. -/
  myPhase : Option ℕ
  /-- `count` (local variable of `Leader`). -/
  count : ℕ
  /-- `RcvCount`: the list `L` received so far; `SndCount`: the bits still to be sent. -/
  bits : List ℕ
  deriving DecidableEq

/-- Pulses sent: `a` on `Port0` (`false`) and `b` on `Port1` (`true`). -/
def out (a b : ℕ) : Bool → ℕ := fun p => if p then b else a

@[simp] lemma out_false (a b : ℕ) : out a b false = a := rfl
@[simp] lemma out_true (a b : ℕ) : out a b true = b := rfl

/-- Start sending the bits `l` (Algorithm 3, line 1 / next iteration, or lines 8 when `l = []`). -/
def sndStart (s : St) (l : List ℕ) : St × (Bool → ℕ) :=
  match l with
  | [] => ({ s with pc := .sndEnd1, bits := [] }, out 0 1)
  | b :: r => ({ s with pc := .sndBit 0, bits := b :: r }, if b = 0 then out 2 0 else out 0 2)

/-- Reaction to the reception of a pulse on port `q`. -/
def recv (s : St) (q : Bool) : St × (Bool → ℕ) :=
  match s.pc with
  | .main =>
    if q = false then
      if s.counted = false then
        -- lines 3–6: first time counted, pong back
        ({ s with counted := true, myPhase := some s.phase }, out 1 0)
      else
        -- lines 7–9
        ({ s with relayed := s.relayed + 1, pc := .relay }, out 0 1)
    else
      -- lines 12–14
      if s.myPhase = some s.phase ∧ s.relayed = 0 then
        ({ s with pc := .newLeader }, out 1 1)  -- line 15
      else ({ s with pc := .wait2 }, out 1 0)
  | .relay => ({ s with pc := .main }, out 1 0)  -- line 11
  | .newLeader =>
    -- lines 17–18, then Algorithm 2 lines 1–3
    ({ s with pc := .probe, phase := s.phase + 1, count := 0 }, out 0 1)
  | .wait2 =>
    if q = false then ({ s with pc := .main, phase := s.phase + 1 }, out 0 1)  -- lines 21–24
    else ({ s with pc := .rcvQ, bits := [] }, out 1 0)  -- lines 25–27
  | .probe =>
    if q then
      -- lines 5–6 and 11, then line 3 or line 12
      if s.count + 1 = s.phase then ({ s with count := s.count + 1, pc := .tr1 }, out 1 0)
      else ({ s with count := s.count + 1 }, out 0 1)
    else ({ s with pc := .fin 0 }, out 3 0)  -- line 8
  | .fin k =>
    if k + 1 < 3 then ({ s with pc := .fin (k + 1) }, out 0 0)
    else sndStart s (Nat.digits 2 s.count)  -- line 10
  | .tr1 => ({ s with pc := .tr2 }, out 0 0)
  | .tr2 =>
    -- lines 15–17: NonLeader(phase + 1, true, 0)
    ({ s with pc := .main, phase := s.phase + 1, counted := true, relayed := 0, count := 0 },
      out 0 1)
  | .sndBit got =>
    if got = 0 then ({ s with pc := .sndBit 1 }, out 0 0) else sndStart s s.bits.tail
  | .sndEnd1 => ({ s with pc := .sndEnd2 }, out 1 0)  -- line 10
  | .sndEnd2 => ({ s with pc := .doneL }, out 0 0)  -- line 12
  | .rcvQ => ({ s with pc := .rcvU q }, if q then out 1 0 else out 0 1)  -- line 4
  | .rcvU q₀ =>
    let o := if q then out 1 0 else out 0 1  -- line 6
    match q₀, q with
    | true, true => ({ s with pc := .rcvQ, bits := s.bits ++ [0] }, o)
    | false, false => ({ s with pc := .rcvQ, bits := s.bits ++ [1] }, o)
    | false, true => ({ s with pc := .doneN }, o)
    | true, false => ({ s with pc := .rcvQ }, o)
  | .doneL => (s, out 0 0)
  | .doneN => (s, out 0 0)

/-- Ports on which a node is willing to read. -/
def ready (s : St) (q : Bool) : Bool :=
  match s.pc with
  | .main | .wait2 | .probe | .rcvQ | .rcvU _ => true
  | .relay | .fin _ | .tr1 | .sndEnd2 => q
  | .newLeader | .tr2 | .sndEnd1 => !q
  | .sndBit _ => if s.bits.head? = some 0 then q else !q
  | .doneL | .doneN => false

/-- Terminated states. -/
def terminated (s : St) : Bool :=
  match s.pc with
  | .doneL | .doneN => true
  | _ => false

/-- Initial state of the leader: `Leader(phase = 1)` has sent its first probe (line 3). -/
def leaderInit : St := ⟨.probe, 1, true, 0, none, 0, []⟩

/-- Initial state of a non-leader: `NonLeader(phase = 1, counted = false, relayed = 0)`. -/
def nonLeaderInit : St := ⟨.main, 1, false, 0, none, 0, []⟩

/-- The paper's `i(i-1)/2`: number of nodes probed in phases `1, …, i - 1`. -/
def tri : ℕ → ℕ
  | 0 => 0
  | j + 1 => tri j + j

/-- The ring size computed by a node in phase `i` with `count` (paper, "Ring size"). -/
def ringSize (i count : ℕ) : ℕ := i * (i - 1) / 2 + count + 1

/-- The **corrected** distance formula. `i` = final phase, `N` = ring size, `mp` = `myPhase`,
`k` = `relayed - 1` (non-leaders) or `relayed` (the last leader). -/
def corrDist (i N : ℕ) (mp : Option ℕ) (k : ℕ) : ℕ :=
  match mp with
  | none => 0
  | some m => if m < i then m * (m + 1) / 2 - k else N - k - 1

/-- The distance formula **as stated in the paper** (p. 9); undefined (`none`) if `myPhase` is. -/
def paperDist (i N : ℕ) (mp : Option ℕ) (k : ℕ) : Option ℕ :=
  match mp with
  | none => none
  | some m => some (if m < i then m * (m + 1) / 2 - k - 1 else N - k - 1)

/-- The `k` of the paper's distance formula: `relayed` for the last leader, `relayed - 1` for every
other process. -/
def kOf (s : St) : ℕ := if s.pc = .doneL then s.relayed else s.relayed - 1

/-- The `count` known to a terminated node: its own (last leader) or the received one. -/
def countOf (s : St) : ℕ := if s.pc = .doneL then s.count else Nat.ofDigits 2 s.bits

/-- Output of a terminated node: (ring size, clockwise distance from the leader). -/
def result (s : St) : Option (ℕ × ℕ) :=
  if terminated s then
    let N := ringSize s.phase (countOf s)
    some (N, corrDist s.phase N s.myPhase (kOf s))
  else none

/-- The paper's distance output of a terminated node. -/
def paperResult (s : St) : Option ℕ :=
  if terminated s then paperDist s.phase (ringSize s.phase (countOf s)) s.myPhase (kOf s)
  else none

/-- **The counting algorithm of Section 5** (Algorithms 1–4) as a procedure with input "is the
leader" and result (ring size, clockwise distance from the leader). -/
def anonCount : Proc Bool (ℕ × ℕ) where
  State := St
  init b := if b then (leaderInit, out 0 1) else (nonLeaderInit, out 0 0)
  recv := recv
  ready := ready
  terminated := terminated
  result := result
  terminated_eq s := by
    unfold result; split <;> simp_all

/-- Input assignment: the leader flag, `true` exactly at `ℓ`. -/
def leaderInput {n : ℕ} (ℓ : ZMod n) : ZMod n → Bool := fun v => decide (v = ℓ)

end Podc.ContentOblivious.AnonCounting
