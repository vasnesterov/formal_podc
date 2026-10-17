import Mathlib
import Cslib.Computability.Distributed.Byzantine.Certificate

/-!
# Basic HotStuff (Algorithm 2): the abstract asynchronous system

Yin, Malkhi, Reiter, Golan Gueta, Abraham, *HotStuff: BFT Consensus with Linearity and
Responsiveness*, PODC 2019 (arXiv:1803.05069v6), Section 4.

This file defines the *safety-relevant* part of Basic HotStuff as an asynchronous interleaving
transition system with ideal (threshold) signatures.

* **Nodes and branches.** A tree node is identified with the branch it leads (collision-resistant
  hashing makes the parent link a digest of the whole branch). We represent the branch as the list
  of its commands, newest first: `createLeaf(parent, cmd) = cmd :: parent`, the root is `[]`.
  `b` *extends* `a` iff `a <:+ b` (`a` is a suffix of `b`); two nodes *conflict* iff neither
  extends the other (Section 4.2).
* **Quorum certificates.** A QC over `⟨type, viewNumber, node⟩` is the tuple itself (`QC`); it is
  *valid* in a state iff at least `n − f` replicas have signed (voted for) the tuple. The global
  state records the votes cast by correct replicas; Byzantine replicas are treated as having
  signed every tuple (they can sign anything at any time). The genesis QC `⊥` (view `0`, root node)
  is valid by convention ("special new-view messages from view 0").
* **Correct replicas** follow the replica role of Algorithm 2, one phase after the other
  (`phase` = how far the replica got in its current view). A proposal or a QC "from the leader"
  may be *any* tuple satisfying the replica's checks: the leader may be Byzantine, so this is an
  over-approximation of every implementation, and safety for this system implies safety for the
  real protocol (`Basic/Refinement.lean` proves this for our partially synchronous
  implementation). The view synchronizer (`nextView`) is arbitrary: a replica may jump to any
  higher view at any time.
-/

namespace HotStuff.Basic

open Classical

/-- A tree node, identified with its branch: the commands from the node to the root. -/
abbrev Node (C : Type*) := List C

/-- Two nodes conflict if neither extends the other. -/
def Conflict {C : Type*} (a b : Node C) : Prop := ¬ a <:+ b ∧ ¬ b <:+ a

/-- The three voting phases (`prepare`, `pre-commit`, `commit`); the type of a QC. -/
inductive Phase
  | prepare
  | precommit
  | commit
  deriving DecidableEq

/-- The position of a voting phase inside a view. -/
def Phase.rank : Phase → ℕ
  | .prepare => 0
  | .precommit => 1
  | .commit => 2

/-- A quorum certificate (the signed tuple `⟨type, viewNumber, node⟩`). -/
structure QC (C : Type*) where
  ty : Phase
  view : ℕ
  node : Node C

/-- The genesis QC `⊥`. -/
def QC.genesis {C : Type*} : QC C := ⟨.prepare, 0, []⟩

/-- `q` is (a copy of) the genesis QC. -/
def QC.IsGen {C : Type*} (q : QC C) : Prop := q.view = 0 ∧ q.node = []

/-- The `safeNode` predicate of Algorithm 1 (Lines 25-27): the node extends the locked node
(safety rule) or the justification is newer than the lock (liveness rule). -/
def SafeNode {C : Type*} (lock : QC C) (x : Node C) (j : QC C) : Prop :=
  lock.node <:+ x ∨ lock.view < j.view

variable {P C : Type*} [Fintype P] [DecidableEq P]

/-- `i` signed `q`: Byzantine replicas (in `F`) sign anything, correct replicas sign what they
voted for. -/
def Signed (F : Finset P) (V : Set (P × QC C)) (i : P) (q : QC C) : Prop := i ∈ F ∨ (i, q) ∈ V

/-- Replicas that signed `q`: all Byzantine replicas and the correct replicas that voted for it. -/
noncomputable def signers (F : Finset P) (V : Set (P × QC C)) (q : QC C) : Finset P :=
  Cslib.Byzantine.signers (Signed F V) q

/-- A QC is valid if it is the genesis QC or `n − f` replicas signed it (ideal threshold
signatures with threshold `n − f`; the second disjunct is `Cslib.Byzantine.Certified (Signed F V)
(n - f) q`). -/
def Valid (f : ℕ) (F : Finset P) (V : Set (P × QC C)) (q : QC C) : Prop :=
  q.IsGen ∨ Fintype.card P - f ≤ (signers F V q).card

/-- Local state of a correct replica (the bookkeeping variables of Section 4.2). -/
structure Loc (C : Type*) where
  /-- `curView`. -/
  view : ℕ
  /-- Progress in the current view: `0` waiting for the proposal, `1` waiting for the
  `prepareQC`, `2` waiting for the `precommitQC`, `3` waiting for the `commitQC`, `4` decided. -/
  phase : ℕ
  /-- `lockedQC`. -/
  lock : QC C
  /-- `prepareQC`. -/
  prepQC : QC C
  /-- Nodes whose branch has been executed (committed). -/
  committed : Set (Node C)

/-- Initial local state: view `1`, `lockedQC = prepareQC = ⊥`. -/
def Loc.init : Loc C := ⟨1, 0, QC.genesis, QC.genesis, ∅⟩

/-- A local step of a correct replica, given the votes `V` cast so far; it may cast one vote
(`some q`: the replica signs `q`). -/
inductive LStep (f : ℕ) (F : Finset P) (V : Set (P × QC C)) : Loc C → Loc C → Option (QC C) → Prop
  /-- Lines 8-10: the proposal `x` with justification `j` passes the checks; vote. -/
  | prepVote (l : Loc C) (x : Node C) (j : QC C) : l.phase = 0 → Valid f F V j → j.node <:+ x →
      SafeNode l.lock x j → LStep f F V l { l with phase := 1 } (some ⟨.prepare, l.view, x⟩)
  /-- Lines 8-10: a proposal that fails the checks (or any proposal): no vote. -/
  | prepSkip (l : Loc C) : l.phase = 0 → LStep f F V l { l with phase := 1 } none
  /-- Lines 16-18. -/
  | precommitVote (l : Loc C) (q : QC C) : l.phase = 1 → Valid f F V q → q.ty = .prepare →
      q.view = l.view →
      LStep f F V l { l with phase := 2, prepQC := q } (some ⟨.precommit, l.view, q.node⟩)
  /-- Lines 24-26 (the replica locks). -/
  | commitVote (l : Loc C) (q : QC C) : l.phase = 2 → Valid f F V q → q.ty = .precommit →
      q.view = l.view →
      LStep f F V l { l with phase := 3, lock := q } (some ⟨.commit, l.view, q.node⟩)
  /-- Lines 33-34: execute the branch of a valid `commitQC` of the current view. -/
  | decide (l : Loc C) (q : QC C) : l.phase = 3 → Valid f F V q → q.ty = .commit →
      q.view = l.view →
      LStep f F V l { l with phase := 4, committed := insert q.node l.committed } none
  /-- `nextView` (or the end of a view after a decision): move to any higher view. -/
  | newView (l : Loc C) (v : ℕ) : l.view < v → LStep f F V l { l with view := v, phase := 0 } none

/-- Global state: local states and the votes cast by correct replicas. -/
structure St (P C : Type*) where
  loc : P → Loc C
  votes : Set (P × QC C)

/-- The initial state. -/
def St.init : St P C := ⟨fun _ => Loc.init, ∅⟩

/-- The votes added by a step of `r` casting `o`. -/
def newVotes (r : P) (o : Option (QC C)) : Set (P × QC C) := {v | ∃ q, o = some q ∧ v = (r, q)}

/-- A step of the system: some correct replica takes a local step. -/
inductive Step (f : ℕ) (F : Finset P) : St P C → St P C → Prop
  | mk (s : St P C) (r : P) (l' : Loc C) (o : Option (QC C)) : r ∉ F →
      LStep f F s.votes (s.loc r) l' o →
      Step f F s ⟨Function.update s.loc r l', s.votes ∪ newVotes r o⟩

/-- Reachable states. -/
def Reach (f : ℕ) (F : Finset P) (s : St P C) : Prop := Relation.ReflTransGen (Step f F) St.init s

end HotStuff.Basic
