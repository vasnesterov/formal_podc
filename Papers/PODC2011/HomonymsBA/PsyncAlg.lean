import Papers.PODC2011.HomonymsBA.Basic

/-!
# Proposition 5: the partially synchronous algorithm (Figure 5 + Proposition 6)

The algorithm of Figure 5 of the paper, together with the authenticated broadcast of
Proposition 6 (Srikanth–Toueg style echo broadcast), written as an `Algorithm ℓ V Msg St`.

Correct processes start at round `0` and step in every round, so the local round counter
`rnd` is the global round. Superround `s` consists of rounds `2s, 2s+1`; phase `ph` consists of
the four superrounds `4ph, …, 4ph+3`, i.e. of rounds `8ph, …, 8ph+7`:

* round `8ph`   (superround 1, round 1): `Broadcast(⟨propose V, ph⟩)` (line 8): `init` field;
* round `8ph+2` (superround 2, round 1): the leaders send `⟨lock v, ph⟩` (line 12);
* round `8ph+4` (superround 3, round 1): `Broadcast(⟨vote v, ph⟩)` (line 16);
* round `8ph+6` (superround 4, round 1): `⟨ack v, ph⟩` (line 20);
* round `8ph+7` (superround 4, round 2): `⟨decide v⟩` (line 24).

Everything a process sends in a round is bundled into one `Msg` (sent to all identifiers):
the `init` of a broadcast, all `echo`es, the proper set, and the lock/ack/decide items.
Direct (non-broadcast) items carry no phase tag: the receiver interprets them by its own
round counter (all correct processes have the same one).

Authenticated broadcast (Proposition 6): a process that receives `⟨init m⟩` from identifier `i`
in the first round of a superround echoes `(m, i)` from the next round on, forever; a process that
has (cumulatively) received the echo `(m, i)` from `ℓ - 2t` distinct identifiers echoes it too;
`Accept(m, i)` holds once the echo `(m, i)` has been received from `ℓ - t` distinct identifiers.
(The superround tag of the paper's `⟨echo m, r, i⟩` is dropped: every broadcast message already
carries its phase, and no property used by the algorithm depends on the tag.)

The transition only looks at the *set* of received pairs (`Algorithm.Innumerate`); all counting is
by distinct identifiers (`Set.ncard` of sets of identifiers).
-/

namespace Podc.HomonymsBA.Psync

open Set

/-- Messages that are sent with the authenticated broadcast. -/
inductive BMsg (V : Type) where
  /-- `⟨propose W, ph⟩` (line 8). -/
  | propose (W : Set V) (ph : ℕ)
  /-- `⟨vote v, ph⟩` (line 16). -/
  | vote (v : V) (ph : ℕ)

/-- The single message a process sends (to every identifier) in a round. -/
structure Msg (ℓ : ℕ) (V : Type) where
  /-- `⟨init m⟩` of a `Broadcast(m)` started in this round. -/
  init : Option (BMsg V)
  /-- The echoes `(m, i)` (`⟨echo m, i⟩`). -/
  echo : Set (BMsg V × Fin ℓ)
  /-- The proper set, appended to every message. -/
  proper : Set V
  /-- `⟨lock v⟩` (line 12). -/
  lock : Option V
  /-- `⟨ack v⟩` (line 20). -/
  ack : Option V
  /-- `⟨decide v⟩` (line 24). -/
  dec : Option V

/-- Local state of a process. -/
structure St (ℓ : ℕ) (V : Type) where
  /-- Round counter. -/
  rnd : ℕ
  /-- Own identifier. -/
  me : Fin ℓ
  /-- The proper set. -/
  proper : Set V
  /-- The `locks` set of pairs `(value, phase)`. -/
  locks : Set (V × ℕ)
  /-- The echoes this process sends. -/
  echoing : Set (BMsg V × Fin ℓ)
  /-- Echoes received so far: `(j, (m, i))` = echo `(m, i)` received from identifier `j`. -/
  echoRcv : Set (Fin ℓ × (BMsg V × Fin ℓ))
  /-- Lock requests received from the phase leader identifier in superround 2. -/
  lockRcv : Set V
  /-- The lock request this process sent (as a leader) in the current phase. -/
  lockReq : Option V
  /-- The ack this process sends in superround 4 of the current phase. -/
  ackVal : Option V
  /-- The decision. -/
  dec : Option V

variable {ℓ : ℕ} {V : Type} (t : ℕ)

/-- Identifier `i` is a leader of phase `ph` (the paper's `i = (ph mod ℓ) + 1`, 0-based). -/
def IsLeader (i : Fin ℓ) (ph : ℕ) : Prop := i.val = ph % ℓ

/-- `Accept(m, i)` has been performed, given the received echoes `E`. -/
def Acc (E : Set (Fin ℓ × (BMsg V × Fin ℓ))) (m : BMsg V) (i : Fin ℓ) : Prop :=
  ℓ - t ≤ {j | (j, (m, i)) ∈ E}.ncard

/-- `Accept(⟨propose W_j, ph⟩, j)` with `v ∈ W_j` for `ℓ - t` different identifiers `j`
(lines 10–11, 15). -/
def AccProp (E : Set (Fin ℓ × (BMsg V × Fin ℓ))) (ph : ℕ) (v : V) : Prop :=
  ℓ - t ≤ {j | ∃ W, v ∈ W ∧ Acc t E (.propose W ph) j}.ncard

/-- `Accept(⟨vote v, ph⟩, j)` for `ℓ - t` different identifiers `j` (lines 18, 28). -/
def AccVote (E : Set (Fin ℓ × (BMsg V × Fin ℓ))) (v : V) (ph : ℕ) : Prop :=
  ℓ - t ≤ {j | Acc t E (.vote v ph) j}.ncard

/-- The proposal set of line 7: proper values not conflicting with any lock. -/
def propSet (s : St ℓ V) : Set V := {v | v ∈ s.proper ∧ ∀ w x, (w, x) ∈ s.locks → w = v}

open Classical in
/-- Line 10: the value a leader asks to lock. -/
noncomputable def lockSend (s : St ℓ V) : Option V :=
  if h : IsLeader s.me (s.rnd / 8) ∧ ∃ v, AccProp t s.echoRcv (s.rnd / 8) v then
    some h.2.choose else none

open Classical in
/-- Lines 14–16: the value this process votes for. -/
noncomputable def voteChoice (s : St ℓ V) : Option V :=
  if h : ∃ v, v ∈ s.lockRcv ∧ AccProp t s.echoRcv (s.rnd / 8) v then some h.choose else none

open Classical in
/-- Line 18: the value this process locks and acks in phase `ph`. -/
noncomputable def ackChoice (E : Set (Fin ℓ × (BMsg V × Fin ℓ))) (ph : ℕ) : Option V :=
  if h : ∃ v, AccVote t E v ph then some h.choose else none

/-- Lines 27–30: the lock `x` is kept. -/
def KeepLock (E : Set (Fin ℓ × (BMsg V × Fin ℓ))) (x : V × ℕ) : Prop :=
  ¬ ∃ w y, w ≠ x.1 ∧ x.2 < y ∧ AccVote t E w y

/-- The message sent by a process in state `s`. -/
noncomputable def out (s : St ℓ V) : Msg ℓ V where
  init := if s.rnd % 8 = 0 then some (.propose (propSet s) (s.rnd / 8))
    else if s.rnd % 8 = 4 then (voteChoice t s).map fun v => .vote v (s.rnd / 8) else none
  echo := s.echoing
  proper := s.proper
  lock := if s.rnd % 8 = 2 then lockSend t s else none
  ack := if s.rnd % 8 = 6 then s.ackVal else none
  dec := if s.rnd % 8 = 7 then s.dec else none

/-- Proper set, first rule: proper sets containing `v` were received from `t + 1` different
identifiers. -/
def Rule1 (X : Set (Fin ℓ × Msg ℓ V)) (v : V) : Prop :=
  t + 1 ≤ {j | ∃ m, (j, m) ∈ X ∧ v ∈ m.proper}.ncard

/-- Proper set, second rule (read existentially): proper sets `f j` were received from a set `J`
of at least `2t + 1` different identifiers, and no value appears in `t + 1` of them. -/
def Rule2 (X : Set (Fin ℓ × Msg ℓ V)) : Prop :=
  ∃ (J : Set (Fin ℓ)) (f : Fin ℓ → Set V), 2 * t + 1 ≤ J.ncard ∧
    (∀ j ∈ J, ∃ m, (j, m) ∈ X ∧ m.proper = f j) ∧ ∀ v, {j | j ∈ J ∧ v ∈ f j}.ncard ≤ t

/-- The echoes received after this round. -/
def newEchoRcv (s : St ℓ V) (X : Set (Fin ℓ × Msg ℓ V)) : Set (Fin ℓ × (BMsg V × Fin ℓ)) :=
  s.echoRcv ∪ {x | ∃ m, (x.1, m) ∈ X ∧ x.2 ∈ m.echo}

open Classical in
/-- A new decision (lines 21–22 and 25–26). -/
noncomputable def decNew (s : St ℓ V) (X : Set (Fin ℓ × Msg ℓ V)) : Option V :=
  if h : s.rnd % 8 = 6 ∧ IsLeader s.me (s.rnd / 8) ∧
      ∃ v, s.lockReq = some v ∧ ℓ - t ≤ {j | ∃ m, (j, m) ∈ X ∧ m.ack = some v}.ncard then
    some h.2.2.choose
  else if h : s.rnd % 8 = 7 ∧ ∃ v, t + 1 ≤ {j | ∃ m, (j, m) ∈ X ∧ m.dec = some v}.ncard then
    some h.2.choose
  else none

/-- The new lock set. -/
noncomputable def newLocks (s : St ℓ V) (E : Set (Fin ℓ × (BMsg V × Fin ℓ))) : Set (V × ℕ) :=
  if s.rnd % 8 = 5 then
    match ackChoice t E (s.rnd / 8) with
    | some v => insert (v, s.rnd / 8) {x | x ∈ s.locks ∧ x.1 ≠ v}
    | none => s.locks
  else if s.rnd % 8 = 7 then {x | x ∈ s.locks ∧ KeepLock t E x}
  else s.locks

/-- The transition, given the *set* `X` of received pairs. -/
noncomputable def step (s : St ℓ V) (X : Set (Fin ℓ × Msg ℓ V)) : St ℓ V where
  rnd := s.rnd + 1
  me := s.me
  proper := s.proper ∪ {v | Rule1 t X v ∨ Rule2 t X}
  locks := newLocks t s (newEchoRcv s X)
  echoing := s.echoing ∪ {e | (s.rnd % 2 = 0 ∧ ∃ m, (e.2, m) ∈ X ∧ m.init = some e.1) ∨
    ℓ - 2 * t ≤ {j | (j, e) ∈ newEchoRcv s X}.ncard}
  echoRcv := newEchoRcv s X
  lockRcv := if s.rnd % 8 = 2 then
      {v | ∃ j m, IsLeader j (s.rnd / 8) ∧ (j, m) ∈ X ∧ m.lock = some v} else s.lockRcv
  lockReq := if s.rnd % 8 = 2 then lockSend t s else s.lockReq
  ackVal := if s.rnd % 8 = 5 then ackChoice t (newEchoRcv s X) (s.rnd / 8) else s.ackVal
  dec := s.dec.or (decNew t s X)

/-- Initial state (lines 1–3). -/
def initSt (i : Fin ℓ) (v : V) : St ℓ V where
  rnd := 0
  me := i
  proper := {v}
  locks := ∅
  echoing := ∅
  echoRcv := ∅
  lockRcv := ∅
  lockReq := none
  ackVal := none
  dec := none

/-- The algorithm of Figure 5 (with the broadcast of Proposition 6). -/
noncomputable def alg (ℓ t : ℕ) (V : Type) : Algorithm ℓ V (Msg ℓ V) (St ℓ V) where
  init i v := initSt i v
  send s _ := some (out t s)
  step s m := step t s {x | x ∈ m}
  decide s := s.dec

/-- The algorithm is innumerate: it only uses the set of received pairs. -/
theorem alg_innumerate : (alg ℓ t V).Innumerate := by
  intro s m m' h
  simp only [alg]
  congr 1
  exact Set.ext h

end Podc.HomonymsBA.Psync
