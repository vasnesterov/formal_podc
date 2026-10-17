import Cslib.Computability.Distributed.Byzantine.PartialSync.Consensus
import Papers.PODC2024.TetraBFT.Defs

/-!
# Single-shot TetraBFT as a partially synchronous algorithm (Section 3.2)

The protocol of Section 3.2 written as an `Algorithm` of CSLib's partially synchronous Byzantine
model (`Cslib.Byzantine.PartialSync`): `n` nodes `Fin n`, authenticated point-to-point channels and
no signatures (a faulty node can send anything, but cannot forge the sender), at most `f` faulty
nodes, discrete time, every correct node takes one step per time unit; a run fixes the GST and
the delivery time of every message (between correct nodes: at most `δ` after `max(send time, GST)`).

A correct node keeps (`St`): its input, current view, a timer (`clock`, ticks since the view
started), the highest view of a view-change message it sent (`vcSent`), the list of votes it cast,
all messages received so far (with their senders), the last view in which it proposed, its
decision (with the view) and its outbox for the current tick. One step (`step`) runs the rules in
this order:

1. receive the inbox (`recvSt`);
2. view-change echo (`echoSt`): on `f + 1` view-change messages for a view `w` higher than every
   view-change message it sent, send a view-change message for `w` (the highest such `w`). With
   `prm.fixEcho = true` the *repaired* rule (not in the paper) is used instead: echo every view
   `w ≥` the current one with `f + 1` view-change messages for which no view-change message was
   sent yet (`vcList` records the views sent);
3. view change (`viewSt`): on `n − f` view-change messages for a view `w` higher than the current
   one, move to `w` (the highest such), restart the timer, broadcast a proof and a suggest message
   (reports of the votes cast before `w`); otherwise advance the timer, and when it reaches
   `timeout` (`9Δ`) broadcast a view-change message for the next view;
4. proposal (`proposeSt`): the leader of the current view, once per view, proposes its input if
   Rule 1 (on the suggest messages for the view) shows the input safe, otherwise some value that
   Rule 1 shows safe (in view `0` all values are safe and it proposes its input);
5. vote-1 (`vote1St`): once per view, on the first proposal of the current view's leader, if
   the view is `0` or Rule 3 (on the proof messages for the view) shows it safe;
6. vote-2, vote-3, vote-4 (`voteKSt`): once per view, on `n − f` vote-(k−1) messages for the current
   view and the same value;
7. decision (`decideSt`): on `n − f` vote-4 messages for the current view and the same value.

Proof/suggest reports are computed from the full vote history (`mkReport`), which yields exactly the
paper's "highest", "second-highest for a different value" and "highest vote-3/4" entries; the
paper's constant-storage bookkeeping is an optimisation not modelled here. Messages are broadcast to
all nodes (including suggest messages, which the paper sends to the leader only). Messages of all
views are kept, so votes received before entering a view count once the view is entered.

The rule checks (Rules 1 and 3) are taken *verbatim* from `Defs.lean` and decided classically.
-/

namespace TetraBFT

open Finset Cslib.Byzantine.PartialSync

/-- TetraBFT messages (Section 3.1). -/
inductive Msg (V : Type) where
  | proposal (v : ℕ) (x : V)
  | vote (k v : ℕ) (x : V)
  | suggest (v : ℕ) (rep : Report V)
  | proof (v : ℕ) (rep : Report V)
  | viewChange (v : ℕ)
  deriving DecidableEq

/-- Protocol parameters: resilience `f`, leader schedule, view timeout (`9Δ` in the paper). -/
structure Params (n : ℕ) where
  f : ℕ
  leader : ℕ → Fin n
  timeout : ℕ
  /-- `false`: the paper's echo rule. `true`: the *repaired* echo rule (not in the paper): echo
  every view `w ≥` the current view with `f + 1` view-change messages for which no view-change
  message was sent yet (see `ViewSync.lean`). -/
  fixEcho : Bool := false

/-- Local state of a node. -/
structure St (n : ℕ) (V : Type) where
  inp : V
  view : ℕ := 0
  clock : ℕ := 0
  vcSent : ℕ := 0
  votes : List (Vote V) := []
  rcv : List (Fin n × Msg V) := []
  propView : Option ℕ := none
  dec : Option (V × ℕ) := none
  out : List (Msg V) := []
  /-- All views for which a view-change message was sent. -/
  vcList : List ℕ := []

variable {n : ℕ} {V : Type} [DecidableEq V]

/-- Senders of message `m` among the received messages. -/
def senders (rcv : List (Fin n × Msg V)) (m : Msg V) : Finset (Fin n) :=
  univ.filter fun q => (q, m) ∈ rcv

/-- Views of the received view-change messages. -/
def vcViews (rcv : List (Fin n × Msg V)) : List ℕ :=
  rcv.filterMap fun e => match e.2 with
    | .viewChange w => some w
    | _ => none

/-- The highest view `w > lo` with at least `th` distinct view-change senders. -/
def maxVC (rcv : List (Fin n × Msg V)) (th lo : ℕ) : Option ℕ :=
  ((vcViews rcv).filter fun w => decide (lo < w) && decide (th ≤ (senders rcv (.viewChange w)).card)).max?

/-- An entry with the highest view (`none` for the empty list). -/
def best : List (ℕ × V) → Option (ℕ × V)
  | [] => none
  | e :: l => match best l with
    | none => some e
    | some e' => if e'.1 ≤ e.1 then some e else some e'

/-- `(view, value)` of the phase-`a` votes of views `< r`. -/
def phaseVotes (votes : List (Vote V)) (a r : ℕ) : List (ℕ × V) :=
  (votes.filter fun w => decide (w.phase = a) && decide (w.view < r)).map fun w => (w.view, w.val)

/-- The report sent in a proof (`a = 1, b = 4`) or suggest (`a = 2, b = 3`) message for view `r`. -/
def mkReport (votes : List (Vote V)) (r a b : ℕ) : Report V :=
  { hi := best (phaseVotes votes a r)
    prev := match best (phaseVotes votes a r) with
      | none => none
      | some (_, y) => best ((phaseVotes votes a r).filter fun e => decide (e.2 ≠ y))
    top := best (phaseVotes votes b r) }

/-- The first message from `q` selected by `g`. -/
def firstFrom {α : Type} (rcv : List (Fin n × Msg V)) (q : Fin n) (g : Msg V → Option α) :
    Option α :=
  rcv.findSome? fun e => if e.1 = q then g e.2 else none

/-- Report of a proof message for view `v`. -/
def getProof (v : ℕ) : Msg V → Option (Report V)
  | .proof v' rep => if v' = v then some rep else none
  | _ => none

/-- Report of a suggest message for view `v`. -/
def getSuggest (v : ℕ) : Msg V → Option (Report V)
  | .suggest v' rep => if v' = v then some rep else none
  | _ => none

/-- Value of a proposal for view `v`. -/
def getProposal (v : ℕ) : Msg V → Option V
  | .proposal v' x => if v' = v then some x else none
  | _ => none

/-- Value of a vote-`k` message for view `v`. -/
def getVote (k v : ℕ) : Msg V → Option V
  | .vote k' v' x => if k' = k ∧ v' = v then some x else none
  | _ => none

/-- Nodes from which a report (selected by `g`) was received. -/
def repSenders (rcv : List (Fin n × Msg V)) (g : Msg V → Option (Report V)) : Finset (Fin n) :=
  univ.filter fun q => (firstFrom rcv q g).isSome

/-- The (first) report received from `q`. -/
def repOf (rcv : List (Fin n × Msg V)) (g : Msg V → Option (Report V)) (q : Fin n) : Report V :=
  (firstFrom rcv q g).getD ⟨none, none, none⟩

/-- A value with a quorum of vote-`k` messages for view `v`, if any. -/
def quorumVal (f : ℕ) (rcv : List (Fin n × Msg V)) (k v : ℕ) : Option V :=
  (rcv.filterMap fun e => getVote k v e.2).find? fun x =>
    decide (n - f ≤ (senders rcv (.vote k v x)).card)

/-- Has the node cast a vote-`k` in view `v`? -/
def hasVoted (votes : List (Vote V)) (k v : ℕ) : Bool :=
  votes.any fun w => decide (w.phase = k) && decide (w.view = v)

section Stages

variable (prm : Params n)

/-- 1. Receive. -/
def recvSt (s : St n V) (ib : Fin n → List (Msg V)) : St n V :=
  { s with rcv := s.rcv ++ (List.finRange n).flatMap (fun q => (ib q).map fun m => (q, m)),
           out := [] }

/-- The views echoed by the repaired rule: every `w ≥` the current view with `f + 1` view-change
messages for `w` and no view-change message for `w` sent yet. -/
def echoViews (s : St n V) : List ℕ :=
  (vcViews s.rcv).dedup.filter fun w => decide (s.view ≤ w) &&
    decide (prm.f + 1 ≤ (senders s.rcv (.viewChange w)).card) && !(s.vcList.contains w)

/-- 2. View-change echo (the paper's rule, or the repaired one if `prm.fixEcho`). -/
def echoSt (s : St n V) : St n V :=
  if prm.fixEcho then
    { s with vcList := s.vcList ++ echoViews prm s,
             out := s.out ++ (echoViews prm s).map Msg.viewChange }
  else
  match maxVC s.rcv (prm.f + 1) s.vcSent with
  | some w => { s with vcSent := w, vcList := s.vcList ++ [w], out := s.out ++ [.viewChange w] }
  | none => s

/-- 3. View change, or timer. -/
def viewSt (s : St n V) : St n V :=
  match maxVC s.rcv (n - prm.f) s.view with
  | some w =>
    let pr : Msg V := Msg.proof w (mkReport s.votes w 1 4)
    let sg : Msg V := Msg.suggest w (mkReport s.votes w 2 3)
    { s with view := w, clock := 0, out := s.out ++ [pr, sg] }
  | none =>
    if s.clock + 1 = prm.timeout then
      { s with clock := s.clock + 1, vcSent := max s.vcSent (s.view + 1),
               vcList := s.vcList ++ [s.view + 1], out := s.out ++ [.viewChange (s.view + 1)] }
    else { s with clock := s.clock + 1 }

/-- Rule 1 on the suggest messages received for the current view. -/
def leaderSafe (s : St n V) (x : V) : Prop :=
  Rule1 n prm.f (repSenders s.rcv (getSuggest s.view)) (repOf s.rcv (getSuggest s.view)) x s.view

/-- The leader's proposal: its input if it is safe, otherwise some safe value. -/
noncomputable def proposeVal (s : St n V) : Option V :=
  if s.view = 0 then some s.inp
  else @ite _ (leaderSafe prm s s.inp) (Classical.dec _) (some s.inp)
    (@dite _ (∃ x, leaderSafe prm s x) (Classical.dec _) (fun h => some (Classical.choose h))
      (fun _ => none))

/-- 4. Proposal (leader only, once per view). -/
noncomputable def proposeSt (p : Fin n) (s : St n V) : St n V :=
  if p = prm.leader s.view then
    if s.propView = some s.view then s
    else match proposeVal prm s with
      | some x => { s with propView := some s.view, out := s.out ++ [.proposal s.view x] }
      | none => s
  else s

/-- Cast a vote in the current view. -/
def castVote (s : St n V) (k : ℕ) (x : V) : St n V :=
  { s with votes := s.votes ++ [⟨k, s.view, x⟩], out := s.out ++ [.vote k s.view x] }

/-- Rule 3 on the proof messages received for the current view. -/
def nodeSafe (s : St n V) (x : V) : Prop :=
  Rule3 n prm.f (repSenders s.rcv (getProof s.view)) (repOf s.rcv (getProof s.view)) x s.view

/-- 5. Vote-1 for the leader's proposal if it is safe. -/
noncomputable def vote1St (s : St n V) : St n V :=
  if hasVoted s.votes 1 s.view then s
  else match firstFrom s.rcv (prm.leader s.view) (getProposal s.view) with
    | none => s
    | some x =>
      if s.view = 0 then castVote s 1 x
      else @ite _ (nodeSafe prm s x) (Classical.dec _) (castVote s 1 x) s

/-- 6. Vote-k (`k = 2, 3, 4`) on a quorum of vote-(k−1). -/
def voteKSt (k : ℕ) (s : St n V) : St n V :=
  if hasVoted s.votes k s.view then s
  else match quorumVal prm.f s.rcv (k - 1) s.view with
    | none => s
    | some x => castVote s k x

/-- 7. Decision on a quorum of vote-4. -/
def decideSt (s : St n V) : St n V :=
  match s.dec with
  | some _ => s
  | none => match quorumVal prm.f s.rcv 4 s.view with
    | none => s
    | some x => { s with dec := some (x, s.view) }

/-- One step of a node. -/
noncomputable def step (p : Fin n) (s : St n V) (ib : Fin n → List (Msg V)) : St n V :=
  decideSt prm (voteKSt prm 4 (voteKSt prm 3 (voteKSt prm 2 (vote1St prm
    (proposeSt prm p (viewSt prm (echoSt prm (recvSt s ib))))))))

end Stages

/-- **Single-shot TetraBFT** (Section 3.2) as a partially synchronous algorithm. -/
noncomputable def tetra (prm : Params n) : Algorithm (Fin n) (Msg V) (St n V) V V where
  init _ x := { inp := x }
  step := step prm
  send _ s _ := s.out
  decide _ s := s.dec.map Prod.fst

end TetraBFT
