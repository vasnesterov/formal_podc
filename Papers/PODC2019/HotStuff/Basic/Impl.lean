import Papers.PODC2019.HotStuff.Basic.Safety
import Cslib.Computability.Distributed.Byzantine.PartialSync.Auth

/-!
# Basic HotStuff (Algorithm 2) in the partially synchronous model

An implementation of Algorithm 2 as a CSLib `Cslib.Byzantine.PartialSync.Algorithm`: discrete
time, every correct replica takes one step per time unit, Byzantine replicas send arbitrary
messages, messages between correct replicas sent at `τ` are delivered by `max τ gst + δ`.
Signatures are abstract tokens (`Auth`): a partial signature of replica `i` on a tuple `q` is the
token `(i, q)`; a QC carries the tuples' signer set and hence the tokens of all its signers
(an ideal `(n − f, n)`-threshold signature). Byzantine replicas can only use tokens of Byzantine
signers or tokens already emitted by correct replicas (`Run.AuthValid`).

* **Replica role.** Each replica keeps a buffer of all received messages (paired with the
  authenticated sender) and in every step runs, in order, the leader handlers `L1`–`L4` (if it is
  the leader of its current view) and the replica handlers `R1`–`R4`; a handler fires when the
  message it "waits for" is in the buffer. `R4` (decide) and the `nextView` interrupt move to the
  next view and send `Msg(new-view, ⊥, prepareQC)` to the next leader (Lines 35-36).
* **Pacemaker.** `nextView` is an *input* of each replica: `(inp p).1 τ = true` means that the
  pacemaker interrupts replica `p` at time `τ`. Theorem 4 is a statement about runs in which the
  pacemaker does not interrupt during the relevant interval; safety holds for all inputs.
* **Client commands.** `(inp p).2 v` is the command the replica proposes when leading view `v`.
* Messages produced in a step are sent at the next time unit (`out`), once.
-/

namespace HotStuff.Basic

open Classical Cslib.Byzantine.PartialSync

variable {P C : Type*} [Fintype P] [DecidableEq P]

/-- A QC as carried in messages: the signed tuple and the set of signers whose partial
signatures it combines. -/
structure QCm (P C : Type*) where
  qc : QC C
  sigs : Finset P

/-- The genesis QC `⊥` (no signatures). -/
def QCm.gen : QCm P C := ⟨QC.genesis, ∅⟩

/-- Local validity check (`tverify`): genesis, or at least `n − f` signers. -/
def QCm.ok (f : ℕ) (j : QCm P C) : Prop := j.qc.IsGen ∨ Fintype.card P - f ≤ j.sigs.card

/-- Messages of Algorithm 2. The message type tags `pre-commit`, `commit`, `decide` are
represented by the type of the carried QC (the replica only checks `matchingQC`). -/
inductive Msg (P C : Type*)
  /-- `Msg(new-view, ⊥, prepareQC)`, stamped with the sender's view `v` (which it leaves). -/
  | newView (v : ℕ) (j : QCm P C)
  /-- `Msg(prepare, curProposal, highQC)`. -/
  | prepare (v : ℕ) (x : Node C) (j : QCm P C)
  /-- `Msg(pre-commit/commit/decide, ⊥, qc)`. -/
  | cert (j : QCm P C)
  /-- `voteMsg`: the partial signature of `i` on `q`. -/
  | vote (i : P) (q : QC C)

/-- Signature tokens: `(i, q)` is `i`'s partial signature on the tuple `q`. -/
abbrev Tok (P C : Type*) := P × QC C

/-- The tokens of a QC. -/
def QCm.toks (j : QCm P C) : Set (Tok P C) := {k | k.1 ∈ j.sigs ∧ k.2 = j.qc}

/-- Tokens carried by a message. -/
def Msg.toks : Msg P C → Set (Tok P C)
  | .newView _ j => j.toks
  | .prepare _ _ j => j.toks
  | .cert j => j.toks
  | .vote i q => {(i, q)}

/-- The signature structure. -/
def auth : Auth P (Msg P C) (Tok P C) := ⟨Prod.fst, Msg.toks⟩

/-- Inputs of a replica: the pacemaker's interrupts and the client commands to propose. -/
abbrev Inp (C : Type*) := (ℕ → Bool) × (ℕ → C)

/-- Local state of a replica. -/
structure RState (P C : Type*) where
  /-- The replica's input (pacemaker interrupts and client commands). -/
  inp : Inp C
  /-- Number of steps taken (= global time for correct replicas). -/
  clock : ℕ
  view : ℕ
  /-- Replica-role progress in the view (`0`–`4`, as in `Loc`). -/
  phase : ℕ
  lock : QCm P C
  prepQC : QCm P C
  committed : Set (Node C)
  /-- All votes cast so far (ghost: the votes are also sent). -/
  votes : Set (QC C)
  /-- All messages received so far, with their (authenticated) sender. -/
  buf : List (P × Msg P C)
  /-- Leader-role progress in the view: `0` collecting new-views, `1` proposed, `2`/`3`/`4`
  formed the prepare/pre-commit/commit QC. -/
  lphase : ℕ
  /-- The leader's proposal `curProposal` and its justification `highQC`. -/
  prop : Node C
  high : QCm P C
  /-- Messages to send at the next time unit. -/
  out : P → List (Msg P C)
  /-- Ghost: all proposals `(view, node, highQC)` made as a leader. -/
  props : Set (ℕ × Node C × QCm P C)
  /-- Ghost: all QCs formed as a leader. -/
  made : Set (QCm P C)
  /-- Ghost: the views in which the replica decided, with the decided node. -/
  decs : Set (ℕ × Node C)
  /-- Ghost: all messages ever sent, with their destination. -/
  sent : Set (P × Msg P C)
  /-- Ghost: every evaluation of the voting rule of Line 9: view, proposal, justification and the
  lock at that moment. -/
  r1 : Set (ℕ × Node C × QCm P C × QC C)

/-- Projection to the abstract local state. -/
def RState.toLoc (s : RState P C) : Loc C := ⟨s.view, s.phase, s.lock.qc, s.prepQC.qc, s.committed⟩

section Handlers

variable (f : ℕ) (leader : ℕ → P) (p : P)

/-- Add messages to the outbox. -/
def RState.send (s : RState P C) (g : P → List (Msg P C)) : RState P C :=
  { s with out := fun q => s.out q ++ g q, sent := s.sent ∪ {qm | qm.2 ∈ g qm.1} }

/-- Send `m` to `q` only. -/
def to1 (q : P) (m : Msg P C) : P → List (Msg P C) := fun q' => if q' = q then [m] else []

/-- Send `m` to everybody (including oneself). -/
def bcast (m : Msg P C) : P → List (Msg P C) := fun _ => [m]

/-- Move to the next view (Lines 35-36): send `Msg(new-view, ⊥, prepareQC)` to the next leader
and reset the per-view variables. -/
def enterView (s : RState P C) : RState P C :=
  { (s.send (to1 (leader (s.view + 1)) (.newView s.view s.prepQC))) with
    view := s.view + 1, phase := 0, lphase := 0, prop := [], high := QCm.gen }

/-- The justification of a new-view message for view `w`, if it is one and it is valid. -/
noncomputable def nvJ (w : ℕ) : Msg P C → Option (QCm P C)
  | .newView w' j => if w' = w ∧ j.ok f then some j else none
  | _ => none

/-- Senders of valid new-view messages for view `s.view − 1`. -/
noncomputable def nvSenders (s : RState P C) : Finset P :=
  Finset.univ.filter fun q => ∃ j, (q, Msg.newView (s.view - 1) j) ∈ s.buf ∧ j.ok f

/-- The QC with the highest view in a list (genesis if empty). -/
def bestQC : List (QCm P C) → QCm P C
  | [] => QCm.gen
  | j :: js => if (bestQC js).qc.view < j.qc.view then j else bestQC js

/-- Signers of votes on `q` in the buffer. -/
noncomputable def voters (s : RState P C) (q : QC C) : Finset P :=
  Finset.univ.filter fun i => ∃ q', (q', Msg.vote i q) ∈ s.buf

/-- `L1` (Lines 2-6): after `n − f` new-view messages, propose `cmd :: highQC.node`. -/
noncomputable def L1 (s : RState P C) : RState P C :=
  if s.lphase = 0 ∧ p = leader s.view ∧ Fintype.card P - f ≤ (nvSenders f s).card then
    let h := bestQC (s.buf.filterMap fun m => nvJ f (s.view - 1) m.2)
    { (s.send (bcast (.prepare s.view (s.inp.2 s.view :: h.qc.node) h))) with
      lphase := 1, prop := s.inp.2 s.view :: h.qc.node, high := h,
      props := insert (s.view, s.inp.2 s.view :: h.qc.node, h) s.props }
  else s

/-- The QC type formed in leader phase `k` (`1`, `2`, `3`). -/
def lty : ℕ → Phase
  | 1 => .prepare
  | 2 => .precommit
  | _ => .commit

/-- `L2`–`L4` (Lines 11-14, 19-22, 27-30): after `n − f` votes, combine them into a QC and
broadcast it. -/
noncomputable def LQ (k : ℕ) (s : RState P C) : RState P C :=
  if s.lphase = k ∧ p = leader s.view ∧
      Fintype.card P - f ≤ (voters s ⟨lty k, s.view, s.prop⟩).card then
    { (s.send (bcast (.cert ⟨⟨lty k, s.view, s.prop⟩, voters s ⟨lty k, s.view, s.prop⟩⟩))) with
      lphase := k + 1,
      made := insert ⟨⟨lty k, s.view, s.prop⟩, voters s ⟨lty k, s.view, s.prop⟩⟩ s.made }
  else s

/-- `R1` (Lines 7-10). -/
noncomputable def R1 (s : RState P C) : RState P C :=
  if h : s.phase = 0 ∧ ∃ xj : Node C × QCm P C,
      (leader s.view, Msg.prepare s.view xj.1 xj.2) ∈ s.buf then
    let xj := Classical.choose h.2
    if xj.2.ok f ∧ xj.2.qc.node <:+ xj.1 ∧ SafeNode s.lock.qc xj.1 xj.2.qc then
      { (s.send (to1 (leader s.view) (.vote p ⟨.prepare, s.view, xj.1⟩))) with
        phase := 1, votes := insert ⟨.prepare, s.view, xj.1⟩ s.votes,
        r1 := insert (s.view, xj.1, xj.2, s.lock.qc) s.r1 }
    else { s with phase := 1, r1 := insert (s.view, xj.1, xj.2, s.lock.qc) s.r1 }
  else s

/-- The certificate of type `ty` for the current view from the current leader, if any. -/
def HasCert (ty : Phase) (s : RState P C) (j : QCm P C) : Prop :=
  (leader s.view, Msg.cert j) ∈ s.buf ∧ j.qc.ty = ty ∧ j.qc.view = s.view ∧ j.ok f

/-- `R2` (Lines 15-18). -/
noncomputable def R2 (s : RState P C) : RState P C :=
  if h : s.phase = 1 ∧ ∃ j, HasCert f leader .prepare s j then
    let j := Classical.choose h.2
    { (s.send (to1 (leader s.view) (.vote p ⟨.precommit, s.view, j.qc.node⟩))) with
      phase := 2, prepQC := j, votes := insert ⟨.precommit, s.view, j.qc.node⟩ s.votes }
  else s

/-- `R3` (Lines 23-26): lock and vote. -/
noncomputable def R3 (s : RState P C) : RState P C :=
  if h : s.phase = 2 ∧ ∃ j, HasCert f leader .precommit s j then
    let j := Classical.choose h.2
    { (s.send (to1 (leader s.view) (.vote p ⟨.commit, s.view, j.qc.node⟩))) with
      phase := 3, lock := j, votes := insert ⟨.commit, s.view, j.qc.node⟩ s.votes }
  else s

/-- Execute the branch led by `x`. -/
def RState.commitNode (s : RState P C) (x : Node C) : RState P C :=
  { s with phase := 4, committed := insert x s.committed, decs := insert (s.view, x) s.decs }

/-- `R4` (Lines 31-34, then 35-36): execute the committed branch and start the next view. -/
noncomputable def R4 (s : RState P C) : RState P C :=
  if h : s.phase = 3 ∧ ∃ j, HasCert f leader .commit s j then
    let j := Classical.choose h.2
    enterView leader (s.commitNode j.qc.node)
  else s

/-- The received messages, paired with their senders. -/
noncomputable def received (inbox : P → List (Msg P C)) : List (P × Msg P C) :=
  Finset.univ.toList.flatMap fun q => (inbox q).map fun m => (q, m)

/-- Receive the inbox: append it to the buffer, clear the outbox, advance the clock. -/
noncomputable def recv (s : RState P C) (inbox : P → List (Msg P C)) : RState P C :=
  { s with clock := s.clock + 1, out := fun _ => [], buf := s.buf ++ received inbox }

/-- One step: receive, run the leader handlers, the replica handlers, and the `nextView`
interrupt. -/
noncomputable def stepR (s : RState P C) (inbox : P → List (Msg P C)) : RState P C :=
  let s₀ := recv s inbox
  let s₁ := LQ f leader p 3 (LQ f leader p 2 (LQ f leader p 1 (L1 f leader p s₀)))
  let s₂ := R4 f leader (R3 f leader p (R2 f leader p (R1 f leader p s₁)))
  if s.inp.1 s.clock then enterView leader s₂ else s₂

end Handlers

/-- Initial state: view `1`, the "special new-view message from view `0`" to `leader 1`. -/
def RState.init (leader : ℕ → P) (i : Inp C) : RState P C where
  inp := i
  clock := 0
  view := 1
  phase := 0
  lock := QCm.gen
  prepQC := QCm.gen
  committed := ∅
  votes := ∅
  buf := []
  lphase := 0
  prop := []
  high := QCm.gen
  out := to1 (leader 1) (.newView 0 QCm.gen)
  props := ∅
  made := ∅
  decs := ∅
  sent := {(leader 1, .newView 0 QCm.gen)}
  r1 := ∅

/-- **Basic HotStuff** as a partially synchronous algorithm, with fault parameter `f` and leader
schedule `leader`. -/
noncomputable def hotstuff (f : ℕ) (leader : ℕ → P) :
    Algorithm P (Msg P C) (RState P C) (Inp C) Unit where
  init _ i := RState.init leader i
  step p s inbox := stepR f leader p s inbox
  send _ s q := s.out q
  decide _ _ := none

end HotStuff.Basic
