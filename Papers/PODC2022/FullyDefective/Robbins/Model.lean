import Papers.PODC2022.FullyDefective.Robbins.Occ

/-!
# Algorithm 3 of [CCGS22]: the content-oblivious simulator on a Robbins cycle (network layer)

K. Censor-Hillel, S. Cohen, R. Gelles, G. Sela. *Distributed Computations in Fully-Defective
Networks.* PODC 2022 (full version arXiv:2205.11148, Section 4; Theorem 6 of the conference
version = Theorems 10/12 of the full version).

As for Algorithm 1 (`Cycle/Model.lean`), the simulated protocol `π` is abstracted away: queues
receive arbitrary positive payloads (`push`), and a node decodes one payload per epoch into its
`log`. The composition with `π` is in `Robbins/Simulation.lean`.

## The network

The nodes are the vertices `V` of a graph `G` with a fixed Robbins cycle `R` (a closed walk
`R.C : ZMod R.L → V` through all vertices, never traversing an edge in both directions). Channels
are fully defective, so a channel `x → y` is a counter `net x y` of pulses in transit (not FIFO,
which is irrelevant for indistinguishable pulses).

## Local knowledge of the nodes

Node `u` knows, for each of its occurrences on the cycle, the previous and next nodes
`prev_{u,i}`, `next_{u,i}`. We describe occurrences by their positions `p ∈ ZMod L` (`C p = u`):
`prev = C (p - 1)`, `next = C (p + 1)`. The numbering of the occurrences (the rotation maintained by
`RotateEdges()`) is stored as the position `o` of occurrence `0`; occurrence `i + 1` is
`nextOcc` of occurrence `i`, and `RotateEdges()` is `o ← prevOcc o` (the new occurrence `0` is
the old occurrence `k_u - 1`). Program points carry positions of occurrences instead of indices
`i`. All actions of `u` only depend on the sequence of pairs `(prev_{u,i}, next_{u,i})` starting
at its occurrence `0`, as in the paper.

## Program points (`Phase`)

* `idle` — line 1;
* `waitReq need` — line 3: `need x` request pulses are still expected on the channel from `x`
  (initially the number of `i` with `prev_{u,i} = x`; the paper's "wait until a request pulse is
  received on each `prev_{u,i}`", counted per physical channel);
* `ready` — line 8;
* `fdata c p` — lines 32–37 (non-holder): `c` data pulses received so far, waiting for a data pulse
  at occurrence `p` (from `C (p - 1)`); at occurrence `0` (`p = o`) also waiting for the `end` pulse
  (line 37);
* `fend p` — lines 41–44 (non-holder): waiting for the `end` pulse at occurrence `p`
  (from `C (p + 1)`);
* `hdata d t p` — lines 21–26 (holder, payload `d`): the `t`-th data pulse is on its way, waiting
  for it at occurrence `p`;
* `hend d p` — lines 27–30 (holder): waiting for the `end` pulse at occurrence `p`.

A node only reads pulses from the channels it waits on (`waits`): at lines 1 and 8 and the
`until`-test of line 37 the paper does not restrict the sender, and we accept any channel of the
right direction (clockwise channels `x → u` with `mult x u > 0`, counterclockwise ones with
`mult u x > 0`); elsewhere the node reads the channel prescribed by the pseudo-code. The direction
of a pulse is that of its channel, which is well defined on a Robbins cycle (`mult_eq_zero_of_pos`).

## Modelling choices (deviations from the pseudo-code are listed here)

* Unary encoding only (Lines 20, 38–39); the binary encoding of Lemma 14 and the complexity
  bounds (Lemmas 13–14) are not modelled.
* Line 3 is "wait until a request pulse was received on each `prev_{u,i}`"; since several
  occurrences may share the channel from `x`, the node counts request pulses per physical channel,
  with multiplicity `mult x u` (`waitReq need`). Extra pulses on a channel stay in the buffer and
  are read at line 8 as data pulses (the paper's comment on Line 8).
* The token holder appends its own payload to its log when its `end` pulse returns (so that every
  node's log is the sequence of all payloads; the holder of a message addressed to itself delivers
  it like everybody else).
* `RotateEdges()` is the update `o ← prevOcc o`; `prev_{u,i}`, `next_{u,i}` are
  `C (pᵢ ∓ 1)` where `p₀ = o`, `pᵢ₊₁ = nextOcc pᵢ`.
* Asynchrony is modelled by interleaving single receptions; the network may delay any pulse
  arbitrarily (no fairness assumption: safety and deadlock-freedom only).

## Ghost state

`ds` (payloads of the epochs started so far), `τ` (the position of the occurrence holding the token,
or that received the token last) and `wv` (the channel carrying the unique token/data/end pulse in
transit, if any; request pulses are not tracked) are ghost variables for the analysis; transitions
never read them.
-/

namespace Podc.FullyDefective.RobbinsSim

/-- Program points of Algorithm 3 (see the module docstring). -/
inductive Phase (V : Type*) (L : ℕ) where
  /-- Line 1. -/
  | idle
  /-- Line 3: `need x` request pulses still expected from `x`. -/
  | waitReq (need : V → ℕ)
  /-- Line 8. -/
  | ready
  /-- Lines 32–37: `c` data pulses received, waiting at occurrence `p`. -/
  | fdata (c : ℕ) (p : ZMod L)
  /-- Lines 41–44: waiting for the `end` pulse at occurrence `p`. -/
  | fend (p : ZMod L)
  /-- Lines 21–26: payload `d`, data pulse number `t`, waiting at occurrence `p`. -/
  | hdata (d t : ℕ) (p : ZMod L)
  /-- Lines 27–30: payload `d`, waiting for the `end` pulse at occurrence `p`. -/
  | hend (d : ℕ) (p : ZMod L)

/-- Local state of a node. -/
structure Node (V : Type*) (L : ℕ) where
  /-- Program point. -/
  ph : Phase V L
  /-- `isTokenHolder_u`. -/
  tok : Bool
  /-- The queue `Q_u` (payloads = lengths of unary encodings). -/
  q : List ℕ
  /-- The payloads decoded so far, one per completed epoch. -/
  log : List ℕ
  /-- The rotation: position of occurrence `0` (the token segment ends there). -/
  o : ZMod L

/-- A global configuration. -/
structure Config (V : Type*) (L : ℕ) where
  /-- Local states. -/
  node : V → Node V L
  /-- Pulses in transit on the channel `x → y`. -/
  net : V → V → ℕ
  /-- Ghost: payloads of the epochs started so far. -/
  ds : List ℕ
  /-- Ghost: position of the token (holder's occurrence, or last receiver of the token pulse). -/
  τ : ZMod L
  /-- Ghost: the channel carrying the token/data/end pulse in transit, if any. -/
  wv : Option (V × V)

/-- Program points at which a pulse is read as a `request` pulse (lines 1 and 3). -/
def Phase.isReq {V : Type*} {L : ℕ} : Phase V L → Bool
  | .idle | .waitReq _ => true
  | _ => false

/-- Line 1. -/
def Phase.isIdle {V : Type*} {L : ℕ} : Phase V L → Bool
  | .idle => true
  | _ => false

/-- Line 8. -/
def Phase.isReady {V : Type*} {L : ℕ} : Phase V L → Bool
  | .ready => true
  | _ => false

/-- The result of a reaction: new local state, whether the node broadcasts its `request` pulses
(line 2), and the destination of the single other pulse it sends, if any. -/
structure Out (V : Type*) (L : ℕ) where
  /-- New local state. -/
  s : Node V L
  /-- Line 2: send a `request` pulse to `next_{u,i}` for all `i`. -/
  req : Bool
  /-- A `token`, `data` or `end` pulse sent to this neighbour. -/
  dst : Option V

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (R : RobbinsCycle G)

/-- Lines 4–7 (end of line 3): release the token if holding it, go to line 8. -/
def release (s : Node V R.L) (req : Bool) : Out V R.L :=
  if s.tok then ⟨{ s with ph := .ready, tok := false }, req, some (R.C (s.o - 1))⟩
  else ⟨{ s with ph := .ready }, req, none⟩

/-- Line 3 after a `request` pulse: continue waiting, or proceed to line 4. -/
def onReq (s : Node V R.L) (need : V → ℕ) (req : Bool) : Out V R.L :=
  if ∀ y, need y = 0 then release R s req else ⟨{ s with ph := .waitReq need }, req, none⟩

/-- Whether node `u` in state `s` reads pulses from `x` (blocking receive / polling semantics). -/
def waits (u : V) (s : Node V R.L) (x : V) : Prop :=
  match s.ph with
  | .idle => 0 < mult R x u
  | .waitReq need => 0 < need x
  | .ready => 0 < mult R x u ∨ 0 < mult R u x
  | .fdata _ p => x = R.C (p - 1) ∨ (p = s.o ∧ 0 < mult R u x)
  | .fend p => x = R.C (p + 1)
  | .hdata _ _ p => x = R.C (p - 1)
  | .hend _ p => x = R.C (p + 1)

/-- Reaction of node `u` in state `s` to a pulse from `x`. -/
def react (u : V) (s : Node V R.L) (x : V) : Out V R.L :=
  match s.ph with
  -- lines 1–2: a `request` pulse arrives; broadcast own `request` pulses, go on with line 3
  | .idle => onReq R s (Function.update (fun y => mult R y u) x (mult R x u - 1)) true
  -- line 3
  | .waitReq need => onReq R s (Function.update need x (need x - 1)) false
  | .ready =>
    if 0 < mult R u x then
      -- lines 9–16: a `token` pulse; `RotateEdges()`
      match s.q with
      -- lines 12, 19–23: take the token, dequeue, send the first data pulse to `next_{u,0}`
      | a :: rest =>
        ⟨{ ph := .hdata a 1 (nextOcc R (prevOcc R s.o)), tok := true, q := rest, log := s.log,
           o := prevOcc R s.o }, false, some (R.C (prevOcc R s.o + 1))⟩
      -- line 14: forward the token to `prev_{u,0}`
      | [] => ⟨{ s with o := prevOcc R s.o }, false, some (R.C (prevOcc R s.o - 1))⟩
    -- line 34–35 (`i = 0`): the first data pulse, forwarded to `next_{u,0}`
    else ⟨{ s with ph := .fdata 1 (nextOcc R s.o) }, false, some (R.C (s.o + 1))⟩
  | .fdata c p =>
    if p = s.o ∧ 0 < mult R u x then
      -- line 37: the `end` pulse (at occurrence `k_u - 1`); lines 38–43 for `i = k_u - 1`
      ⟨{ s with
          ph := if prevOcc R s.o = s.o then .idle else .fend (prevOcc R (prevOcc R s.o))
          log := s.log ++ [c / occ R u] }, false, some (R.C (prevOcc R s.o - 1))⟩
    -- lines 34–35
    else ⟨{ s with ph := .fdata (c + 1) (nextOcc R p) }, false, some (R.C (p + 1))⟩
  -- lines 42–43
  | .fend p => ⟨{ s with ph := if p = s.o then .idle else .fend (prevOcc R p) }, false,
      some (R.C (p - 1))⟩
  -- line 24 (and the next iteration of lines 21–23, or line 28)
  | .hdata d t p =>
    if p = s.o then
      if t < d then ⟨{ s with ph := .hdata d (t + 1) (nextOcc R s.o) }, false, some (R.C (s.o + 1))⟩
      else ⟨{ s with ph := .hend d (prevOcc R s.o) }, false, some (R.C (s.o - 1))⟩
    else ⟨{ s with ph := .hdata d t (nextOcc R p) }, false, some (R.C (p + 1))⟩
  -- line 29 (and line 28 of the next iteration)
  | .hend d p =>
    if p = s.o then ⟨{ s with ph := .idle, log := s.log ++ [d] }, false, none⟩
    else ⟨{ s with ph := .hend d (prevOcc R p) }, false, some (R.C (p - 1))⟩

/-- Steps. -/
inductive Label (V : Type*) where
  /-- The environment (the simulated protocol) appends payload `a` to `Q_u`. -/
  | push (u : V) (a : ℕ)
  /-- Line 1 → 2: `Q_u` is non-empty, `u` broadcasts its `request` pulses. -/
  | start (u : V)
  /-- `u` reads one pulse from the channel `x → u`. -/
  | recv (u x : V)

/-- Whether a step is enabled. Payloads are positive (unary encodings `1^d`, `d ≥ 1`). -/
def Enabled (c : Config V R.L) : Label V → Prop
  | .push _ a => 0 < a
  | .start u => (c.node u).ph.isIdle = true ∧ (c.node u).q ≠ []
  | .recv u x => waits R u (c.node u) x ∧ 0 < c.net x u

/-- Whether reading from `x` is the reception of a `token` pulse at line 8. -/
def tokRecv (u : V) (s : Node V R.L) (x : V) : Bool :=
  s.ph.isReady && decide (0 < mult R u x)

/-- The configuration after a step. -/
def next (c : Config V R.L) : Label V → Config V R.L
  | .push u a =>
    { c with node := Function.update c.node u { c.node u with q := (c.node u).q ++ [a] } }
  | .start u =>
    { c with node := Function.update c.node u { c.node u with ph := .waitReq fun y => mult R y u }
             net := fun a b => c.net a b + if a = u then mult R u b else 0 }
  | .recv u x =>
    let r := react R u (c.node u) x
    { node := Function.update c.node u r.s
      net := fun a b => c.net a b - (if a = x ∧ b = u then 1 else 0) +
        (if a = u then (if r.req then mult R u b else 0) + (if r.dst = some b then 1 else 0) else 0)
      ds := if tokRecv R u (c.node u) x then
          (match (c.node u).q with | a :: _ => c.ds ++ [a] | [] => c.ds) else c.ds
      τ := if tokRecv R u (c.node u) x then prevOcc R (c.node u).o else c.τ
      wv := match r.dst with
        | some y => some (u, y)
        | none => if (c.node u).ph.isReq then c.wv else none }

/-- One step. -/
def Step (c c' : Config V R.L) : Prop := ∃ l, Enabled R c l ∧ c' = next R c l

/-- The initial configuration (Init of Algorithm 3(a)): everybody at line 1, the occurrence at
position `τ₀` holds the token, every node numbers its occurrences so that segment `0` contains
`τ₀` (occurrence `0` is the first one at or after `τ₀`), and the queues hold the payloads `qs u`. -/
def init (τ₀ : ZMod R.L) (qs : V → List ℕ) : Config V R.L where
  node u := ⟨.idle, decide (u = R.C τ₀), qs u, [], firstOcc R u τ₀⟩
  net _ _ := 0
  ds := []
  τ := τ₀
  wv := none

/-- Reachable configurations. -/
def Reach (τ₀ : ZMod R.L) (qs : V → List ℕ) (c : Config V R.L) : Prop :=
  Relation.ReflTransGen (Step R) (init R τ₀ qs) c

end Podc.FullyDefective.RobbinsSim
