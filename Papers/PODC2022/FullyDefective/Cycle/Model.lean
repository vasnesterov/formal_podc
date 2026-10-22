import Mathlib

/-!
# Algorithm 1 of [CCGS22]: the content-oblivious simulator on a simple cycle (ring layer)

K. Censor-Hillel, S. Cohen, R. Gelles, G. Sela. *Distributed Computations in Fully-Defective
Networks.* PODC 2022 (full version arXiv:2205.11148).

This file models the *ring layer* of Algorithm 1: the content-oblivious broadcast mechanism
(token phase, Algorithm 1(a), and unary data phase, Algorithm 1(b)) on an oriented cycle
`ZMod n`. The simulated protocol `π` is abstracted away: the queue `Q_u` of each node receives
arbitrary positive payloads (`push`, an environment step that may happen at any time), and a node
"decodes" one payload per epoch into its `log`. The composition with an actual protocol `π`
is in `Cycle/Simulation.lean`.

## The network

Node `u` is joined to `u + 1` (its clockwise neighbour) and to `u - 1` (its counterclockwise
neighbour); for `n = 1` this is a self-loop and for `n = 2` a double link, the algorithm works
verbatim there too. Messages are pulses (fully-defective channels: the content of every message
may be corrupted, so content is ignored), hence a channel is a counter. We keep, for every node,
the number of clockwise (`cw`) and counterclockwise (`ccw`) pulses it has sent and received:
the clockwise pulses in transit to `u` are `cwS (u - 1) - cwR u`, the counterclockwise ones
`ccwS (u + 1) - ccwR u`. Channels are not FIFO, which is irrelevant for indistinguishable pulses.

## The algorithm (one state per program point)

* `idle` — line 1 (waiting for a non-empty queue or a clockwise `request` pulse);
* `waitReq` — line 3 (own `request` sent, waiting for one);
* `ready` — line 8 (waiting for a `token` (ccw) or the first `data` (cw) pulse);
* `fwd c` — line 25 (non-holder in the data phase, `c` data pulses received and forwarded);
* `send d r` — line 21 (token holder, sent its `d` data pulses, `r` of them came back);
* `waitEnd d` — line 23 (token holder, `end` pulse sent).

A node only reads a pulse from a direction it is waiting for (`cwReady`, `ccwReady`): pulses from
the other direction stay in the incoming buffer, as in the pseudo-code's `wait until` statements.

The meanings (`request`, `token`, `data`, `end`) are never stored in pulses: a node interprets a
pulse by its direction and its own state only.

## Ghost state

`Config.ds` (the payloads of the epochs started so far, in order) and `Config.hold` (the node that
captured the token last, initially `T₀`) are ghost variables for the analysis; transitions never
read them.
-/

namespace Podc.FullyDefective.Cycle

/-- Program points of Algorithm 1 (see the module docstring). -/
inductive Phase where
  /-- Line 1. -/
  | idle
  /-- Line 3. -/
  | waitReq
  /-- Line 8. -/
  | ready
  /-- Line 25: non-holder in the data phase, `c` data pulses received. -/
  | fwd (c : ℕ)
  /-- Line 21: holder, sent `d` data pulses, `r` came back. -/
  | send (d r : ℕ)
  /-- Line 23: holder, waiting for its `end` pulse. -/
  | waitEnd (d : ℕ)
  deriving DecidableEq

/-- Local state of a node: program point, `isTokenHolder`, queue `Q_u` of payloads (unary
lengths of encoded messages), and the decoded payloads (one per completed epoch). -/
structure Node where
  /-- Program point. -/
  ph : Phase
  /-- `isTokenHolder_u`. -/
  tok : Bool
  /-- The queue `Q_u`. -/
  q : List ℕ
  /-- The payloads decoded so far, one per completed epoch. -/
  log : List ℕ

/-- A global configuration of the ring layer. -/
structure Config (n : ℕ) where
  /-- Local states. -/
  node : ZMod n → Node
  /-- Clockwise pulses sent by `u` (to `u + 1`). -/
  cwS : ZMod n → ℕ
  /-- Clockwise pulses received by `u` (from `u - 1`). -/
  cwR : ZMod n → ℕ
  /-- Counterclockwise pulses sent by `u` (to `u - 1`). -/
  ccwS : ZMod n → ℕ
  /-- Counterclockwise pulses received by `u` (from `u + 1`). -/
  ccwR : ZMod n → ℕ
  /-- Ghost: payloads of the epochs started so far. -/
  ds : List ℕ
  /-- Ghost: the last node that set `isTokenHolder ← True` (initially `T₀`). -/
  hold : ZMod n

/-- Whether a node at program point `p` reads clockwise pulses. -/
def Phase.cwReady : Phase → Bool
  | .waitEnd _ => false
  | _ => true

/-- Whether a node at program point `p` reads counterclockwise pulses. -/
def Phase.ccwReady : Phase → Bool
  | .ready | .fwd _ | .waitEnd _ => true
  | _ => false

/-- Reaction to reading a clockwise pulse: new local state, number of clockwise and of
counterclockwise pulses sent. -/
def onCW (s : Node) : Node × ℕ × ℕ :=
  match s.ph with
  -- lines 1–2 (a `request` arrived) and 4–6 (release the token if holding it)
  | .idle => (⟨.ready, false, s.q, s.log⟩, 1, if s.tok then 1 else 0)
  -- line 3 and lines 4–6
  | .waitReq => (⟨.ready, false, s.q, s.log⟩, 0, if s.tok then 1 else 0)
  -- line 8: the first `data` pulse, forwarded (line 25)
  | .ready => (⟨.fwd 1, s.tok, s.q, s.log⟩, 1, 0)
  -- line 25
  | .fwd c => (⟨.fwd (c + 1), s.tok, s.q, s.log⟩, 1, 0)
  -- lines 21–22
  | .send d r =>
    if r + 1 < d then (⟨.send d (r + 1), s.tok, s.q, s.log⟩, 0, 0)
    else (⟨.waitEnd d, s.tok, s.q, s.log⟩, 0, 1)
  | .waitEnd _ => (s, 0, 0)

/-- Reaction to reading a counterclockwise pulse: new local state, number of clockwise and of
counterclockwise pulses sent. -/
def onCCW (s : Node) : Node × ℕ × ℕ :=
  match s.ph with
  -- lines 9–15: a `token` pulse
  | .ready =>
    match s.q with
    -- lines 11, 18–20: take the token, dequeue, send `d` data pulses
    | a :: q' => (⟨.send a 0, true, q', s.log⟩, a, 0)
    -- line 13: forward the token
    | [] => (s, 0, 1)
  -- lines 25–29: the `end` pulse; decode, forward `end`
  | .fwd c => (⟨.idle, s.tok, s.q, s.log ++ [c]⟩, 0, 1)
  -- line 23: own `end` pulse is back
  | .waitEnd d => (⟨.idle, s.tok, s.q, s.log ++ [d]⟩, 0, 0)
  | _ => (s, 0, 0)

/-- The payload dequeued when the node reads a counterclockwise pulse: `some a` iff the node takes
the token (line 11) with `a` at the head of its queue. -/
def capture? (s : Node) : Option ℕ :=
  match s.ph, s.q with
  | .ready, a :: _ => some a
  | _, _ => none

variable {n : ℕ}

/-- Clockwise pulses in transit to `u`. -/
def Config.cwIn (c : Config n) (u : ZMod n) : Prop := c.cwR u < c.cwS (u - 1)

/-- A counterclockwise pulse is in transit to `u`. -/
def Config.ccwIn (c : Config n) (u : ZMod n) : Prop := c.ccwR u < c.ccwS (u + 1)

/-- Steps of the ring layer. -/
inductive Label (n : ℕ) where
  /-- The environment (the simulated protocol) appends payload `a` to `Q_u`. -/
  | push (u : ZMod n) (a : ℕ)
  /-- Line 1 → 2: `Q_u` is non-empty, `u` sends its `request` pulse. -/
  | start (u : ZMod n)
  /-- `u` reads a clockwise pulse. -/
  | cw (u : ZMod n)
  /-- `u` reads a counterclockwise pulse. -/
  | ccw (u : ZMod n)

/-- The node that acts in a step. -/
def Label.node : Label n → ZMod n
  | .push u _ | .start u | .cw u | .ccw u => u

/-- Whether a step is enabled. Payloads are positive (unary encodings `1^d`, `d ≥ 1`). -/
def Enabled (c : Config n) : Label n → Prop
  | .push _ a => 0 < a
  | .start u => (c.node u).ph = .idle ∧ (c.node u).q ≠ []
  | .cw u => (c.node u).ph.cwReady = true ∧ c.cwIn u
  | .ccw u => (c.node u).ph.ccwReady = true ∧ c.ccwIn u

/-- The configuration after a step. -/
def next (c : Config n) : Label n → Config n
  | .push u a =>
    { c with node := Function.update c.node u { c.node u with q := (c.node u).q ++ [a] } }
  | .start u =>
    { c with node := Function.update c.node u { c.node u with ph := .waitReq }
             cwS := Function.update c.cwS u (c.cwS u + 1) }
  | .cw u =>
    let r := onCW (c.node u)
    { c with node := Function.update c.node u r.1
             cwR := Function.update c.cwR u (c.cwR u + 1)
             cwS := Function.update c.cwS u (c.cwS u + r.2.1)
             ccwS := Function.update c.ccwS u (c.ccwS u + r.2.2) }
  | .ccw u =>
    let r := onCCW (c.node u)
    { c with node := Function.update c.node u r.1
             ccwR := Function.update c.ccwR u (c.ccwR u + 1)
             cwS := Function.update c.cwS u (c.cwS u + r.2.1)
             ccwS := Function.update c.ccwS u (c.ccwS u + r.2.2)
             -- ghost: record a captured token
             ds := match capture? (c.node u) with | some a => c.ds ++ [a] | none => c.ds
             hold := match capture? (c.node u) with | some _ => u | none => c.hold }

/-- One step of the ring layer. -/
def Step (c c' : Config n) : Prop := ∃ l, Enabled c l ∧ c' = next c l

/-- The initial configuration: all nodes at line 1, `T₀` holds the token, and the queues hold the
payloads `qs u` (the messages `π` sends at start-up). -/
def init (T₀ : ZMod n) (qs : ZMod n → List ℕ) : Config n where
  node u := ⟨.idle, decide (u = T₀), qs u, []⟩
  cwS _ := 0
  cwR _ := 0
  ccwS _ := 0
  ccwR _ := 0
  ds := []
  hold := T₀

/-- Reachable configurations. -/
def Reach (T₀ : ZMod n) (qs : ZMod n → List ℕ) (c : Config n) : Prop :=
  Relation.ReflTransGen Step (init T₀ qs) c

end Podc.FullyDefective.Cycle
