import Papers.PODC2020.ConsecutiveBallotsPaxos.ConsecutiveSet

/-!
# Single-decree Paxos with Consecutive Quorums and Consecutive Proposals

Model of Section 3.1 of [paper] (Classic Paxos), in the style of the paper's TLA+ appendix
(an interleaving system over the set of all messages ever sent):

* acceptors `A` (finite), values `V`, ballots `ℕ`;
* each acceptor keeps `maxBal` (the highest ballot it promised/accepted, `⊥` initially) and
  `last` (its highest accepted proposal `(ballot, value)`, `none` initially);
* `msgs` is the set of all messages ever sent (`sent` in the paper). Messages are never lost
  from this set; a learner or proposer receives a subset of it (asynchrony, loss, delays);
* actions: `prepare b` (Phase 1a), `promise a b` (Phase 1b), `propose b v` (Phase 2a),
  `accept a b v` (Phase 2b). Any action may happen at any time if its guard holds (fully
  asynchronous scheduler; crashes = an agent that stops taking steps).

Proposals (Phase 2a) use the Normal criterion (Definition 10) and, if the flag `cp` is set, also
the extended Consecutive Proposal criterion (Definitions 11–12). With `cp = false` this is Classic
Paxos (Sections 3–4); with `cp = true` it is *Consecutive Paxos* (Section 6). Proposers may use any
sent message (a superset of what a proposer can actually have received), which only adds
behaviours.

Quorums are an arbitrary intersecting quorum system (as in the TLA+ appendix); the paper's
majorities of `2f+1` acceptors are `QuorumSystem.majority`.
-/

namespace Podc.ConsecutiveBallotsPaxos

variable {A V : Type*}

/-- An intersecting quorum system. -/
structure QuorumSystem (A : Type*) where
  /-- The quorums. -/
  IsQuorum : Finset A → Prop
  /-- Any two quorums intersect. -/
  inter : ∀ Q₁ Q₂, IsQuorum Q₁ → IsQuorum Q₂ → ∃ a, a ∈ Q₁ ∧ a ∈ Q₂

/-- Majority quorums (`|Q| ≥ f + 1` out of `2f + 1` acceptors). -/
def QuorumSystem.majority (A : Type*) [Fintype A] [DecidableEq A] : QuorumSystem A where
  IsQuorum Q := Fintype.card A < 2 * Q.card
  inter Q₁ Q₂ h₁ h₂ := by
    by_contra hc
    push Not at hc
    have h : Q₁ ∩ Q₂ = ∅ := by
      ext a; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]; exact hc a
    have := Finset.card_union_add_card_inter Q₁ Q₂
    rw [h, Finset.card_empty] at this
    have := Finset.card_le_univ (Q₁ ∪ Q₂)
    omega

/-- Paxos messages. `promise a b r` reports the highest proposal `r` accepted by `a` (`none` = ⊥). -/
inductive Msg (A V : Type*)
  | prepare (b : ℕ)
  | promise (a : A) (b : ℕ) (r : Option (ℕ × V))
  | propose (b : ℕ) (v : V)
  | accept (a : A) (b : ℕ) (v : V)

open Msg

/-- Global state: acceptors' local state and all messages ever sent. -/
structure State (A V : Type*) where
  /-- Highest ballot promised or accepted (`⊥`: none). -/
  maxBal : A → WithBot ℕ
  /-- Highest proposal accepted. -/
  last : A → Option (ℕ × V)
  /-- All messages ever sent. -/
  msgs : Set (Msg A V)

/-- The initial state. -/
def init : State A V := ⟨fun _ => ⊥, fun _ => none, ∅⟩

/-- Definition 10 of [paper] (Normal Proposal), as `Clause1` of the TLA+ appendix: a quorum `Q`
promised ballot `b`, and either all of them report `⊥`, or `v` is the value of a highest reported
proposal. -/
def NormalClause (QS : QuorumSystem A) (M : Set (Msg A V)) (b : ℕ) (v : V) : Prop :=
  ∃ Q, QS.IsQuorum Q ∧ (∀ a ∈ Q, ∃ r, promise a b r ∈ M) ∧
    ((∀ a ∈ Q, ∀ k w, promise a b (some (k, w)) ∉ M) ∨
     ∃ a ∈ Q, ∃ k, promise a b (some (k, v)) ∈ M ∧
       ∀ a' ∈ Q, ∀ k' w', promise a' b (some (k', w')) ∈ M → k' ≤ k)

/-- Definitions 11–12 of [paper] (Consecutive Proposal, extended), `Clause2` of the TLA+ appendix:
`v` may be proposed in ballot `c + 1` if some acceptor reported `(c, v)` in a promise for `c + 1`,
or sent `accept(c, v)`. -/
def ConsecClause (M : Set (Msg A V)) (b : ℕ) (v : V) : Prop :=
  ∃ c, b = c + 1 ∧ ∃ a, promise a b (some (c, v)) ∈ M ∨ accept a c v ∈ M

/-- A proposal `(b, v)` is justified (Phase 2a criterion). `cp` enables Consecutive Proposals. -/
def ProposalOK (QS : QuorumSystem A) (cp : Bool) (M : Set (Msg A V)) (b : ℕ) (v : V) : Prop :=
  NormalClause QS M b v ∨ (cp = true ∧ ConsecClause M b v)

/-- Protocol actions. -/
inductive Action (A V : Type*)
  | prepare (b : ℕ)
  | promise (a : A) (b : ℕ)
  | propose (b : ℕ) (v : V)
  | accept (a : A) (b : ℕ) (v : V)

/-- Guards of the actions (Section 3.1; TLA+ `Phase1a`, `Phase1b`, `Phase2a`, `Phase2b`). -/
def Action.Enabled (QS : QuorumSystem A) (cp : Bool) (s : State A V) : Action A V → Prop
  | .prepare _ => True
  | .promise a b => Msg.prepare b ∈ s.msgs ∧ s.maxBal a < b
  | .propose b v => (∀ w, Msg.propose b w ∉ s.msgs) ∧ ProposalOK QS cp s.msgs b v
  | .accept a b v => Msg.propose b v ∈ s.msgs ∧ s.maxBal a ≤ b

/-- Effects of the actions. -/
def Action.apply [DecidableEq A] : Action A V → State A V → State A V
  | .prepare b, s => { s with msgs := insert (Msg.prepare b) s.msgs }
  | .promise a b, s => { s with maxBal := Function.update s.maxBal a b,
                                msgs := insert (Msg.promise a b (s.last a)) s.msgs }
  | .propose b v, s => { s with msgs := insert (Msg.propose b v) s.msgs }
  | .accept a b v, s => { maxBal := Function.update s.maxBal a b,
                          last := Function.update s.last a (some (b, v)),
                          msgs := insert (Msg.accept a b v) s.msgs }

/-- One step of the protocol. -/
def Step [DecidableEq A] (QS : QuorumSystem A) (cp : Bool) (s s' : State A V) : Prop :=
  ∃ act : Action A V, act.Enabled QS cp s ∧ s' = act.apply s

/-- Reachable states. -/
def Reachable [DecidableEq A] (QS : QuorumSystem A) (cp : Bool) (s : State A V) : Prop :=
  Relation.ReflTransGen (Step QS cp) init s

/-! ### Chosen and learned -/

/-- Definition 4 of [paper] (Classic Chosen): a quorum sent `accept(i, v)`. -/
def ClassicChosen (QS : QuorumSystem A) (M : Set (Msg A V)) (i : ℕ) (v : V) : Prop :=
  ∃ Q, QS.IsQuorum Q ∧ ∀ a ∈ Q, accept a i v ∈ M

/-- Definition 5 of [paper] (Consecutive Quorum): every member `a` of the quorum `Q` sent some
`accept(x a, v)`, and the ballots `{x a | a ∈ Q}` form a consecutive set. -/
def CQ (QS : QuorumSystem A) (M : Set (Msg A V)) (Q : Finset A) (v : V) : Prop :=
  QS.IsQuorum Q ∧ ∃ x : A → ℕ, (∀ a ∈ Q, accept a (x a) v ∈ M) ∧ ConsecutiveSet (x '' Q)

/-- Definition 6 of [paper] (CQ Chosen), **literally**:
`Chosen(i, v) ≡ ∃ Qᵢ. CQ(Qᵢ, v) ∧ ∃ α ∈ Qᵢ. accept(i, v)_α ∈ sent_α`.
The ballot-`i` accept need not be one of the accepts forming the consecutive quorum. -/
def CQChosen (QS : QuorumSystem A) (M : Set (Msg A V)) (i : ℕ) (v : V) : Prop :=
  ∃ Q, CQ QS M Q v ∧ ∃ a ∈ Q, accept a i v ∈ M

/-- Definition 6 of [paper] as intended (see `differencies.md`): the ballot-`i` accept is one of
the accepts forming the consecutive quorum (`x a = i`). -/
def CQChosen' (QS : QuorumSystem A) (M : Set (Msg A V)) (i : ℕ) (v : V) : Prop :=
  ∃ Q, QS.IsQuorum Q ∧ ∃ x : A → ℕ, (∀ a ∈ Q, accept a (x a) v ∈ M) ∧
    ConsecutiveSet (x '' Q) ∧ ∃ a ∈ Q, x a = i

/-- Definition 3 of [paper] (Learned), for a learner that received the messages `L`. -/
def ClassicLearned (QS : QuorumSystem A) (L : Set (Msg A V)) (i : ℕ) (v : V) : Prop :=
  ClassicChosen QS L i v

/-- CQ-Learned (Section 4): the learner received accepts forming a CQ-chosen pattern. -/
def CQLearned (QS : QuorumSystem A) (L : Set (Msg A V)) (i : ℕ) (v : V) : Prop :=
  CQChosen QS L i v

end Podc.ConsecutiveBallotsPaxos
