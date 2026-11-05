import Mathlib

/-!
# MultiPaxos (Figure 1 of [paper]), as an interleaving transition system

[paper]: Z. Wang, C. Zhao, S. Mu, H. Chen, J. Li. *On the Parallels between Paxos and Raft, and how
to Port Optimizations.* PODC 2019 (extended version with Appendices A–C).

Model (as in the paper's TLA+ appendix B.1 and in its proof, Appendix C):

* a finite set of servers `N`, each playing proposer, acceptor and learner; values `V`;
  ballots `ℕ` (initially `0`, `Phase1a` increments the ballot, as in Figure 1);
* asynchronous message passing over an unreliable network: every message ever sent stays in a set
  (`m1a`, `m1b`, `m2a`, `m2b`); a server "receives" a message by reading it from the set, so
  messages may be lost (never read), duplicated (read twice) and reordered. Crash-stop failures
  are servers that stop taking steps; no step is ever forced;
* each server keeps `ballot`, `leader` (`phase1Succeeded` in Figure 1), its log
  `inst : ℕ → Option (ℕ × V)` (`instances`, an entry is `(accepted ballot, value)`) and its
  `chosen` set (`chosenSet`);
* as in Appendix C, the `unchosen` optimisation of Figure 1 is dropped: `prepareOK` carries the
  whole log.

Repairs of Figure 1 (all recorded in `differencies.md`):

* `phase1a` resets `leader` (as `IncreaseHighestBallot` in the TLA+ spec) and also produces the
  proposer's own (implicit) `prepareOK`;
* `phase1Succeed` is guarded by `¬ leader` and needs the proposer's own report among the quorum's
  (both as `BecomeLeader` in the TLA+ spec); it sets the whole log to the safe entries (indices
  above the largest reported one become empty);
* `phase2a` may not propose a second value for the same instance and ballot (Figure 1 records
  nothing when proposing, so as written a leader can propose two values);
* `learn` only adds to `chosen` (Figure 1 also overwrites the instance with `(b, v)`); the
  `acceptOK` messages are visible to every learner (the paper's "notify other servers").

Quorums are any intersecting family (`QuorumSystem`); majorities are `QuorumSystem.majority`.
-/

namespace Podc.PaxosRaftRefinement

/-- An intersecting quorum system on the servers `N`. -/
structure QuorumSystem (N : Type*) where
  /-- The quorums. -/
  IsQuorum : Finset N → Prop
  /-- Any two quorums intersect. -/
  inter : ∀ Q₁ Q₂, IsQuorum Q₁ → IsQuorum Q₂ → ∃ a, a ∈ Q₁ ∧ a ∈ Q₂

/-- Majority quorums (`f + 1` out of `2f + 1`, or in general more than half of the servers). -/
def QuorumSystem.majority (N : Type*) [Fintype N] [DecidableEq N] : QuorumSystem N where
  IsQuorum Q := Fintype.card N < 2 * Q.card
  inter Q₁ Q₂ h₁ h₂ := by
    by_contra hc
    push Not at hc
    have h : Q₁ ∩ Q₂ = ∅ := by
      ext a; simp only [Finset.mem_inter, Finset.notMem_empty, iff_false, not_and]; exact hc a
    have := Finset.card_union_add_card_inter Q₁ Q₂
    rw [h, Finset.card_empty] at this
    have := Finset.card_le_univ (Q₁ ∪ Q₂)
    omega

namespace Paxos

variable {N V : Type*}

/-- A `prepareOK` message `⟨src, dst, bal, log⟩`: `src` answers the `prepare` of `dst` for ballot
`bal`, reporting its whole log. -/
@[ext]
structure Msg1b (N V : Type*) where
  /-- Sender (an acceptor). -/
  src : N
  /-- Receiver (the proposer). -/
  dst : N
  /-- The ballot of the `prepare`. -/
  bal : ℕ
  /-- The sender's log. -/
  log : ℕ → Option (ℕ × V)

/-- Global state of MultiPaxos. -/
@[ext]
structure State (N V : Type*) where
  /-- `s.ballot`. -/
  ballot : N → ℕ
  /-- `s.phase1Succeeded`. -/
  leader : N → Bool
  /-- `s.instances`: `inst s i = some (b, v)` — instance `i` holds value `v` accepted at ballot `b`. -/
  inst : N → ℕ → Option (ℕ × V)
  /-- `s.chosenSet`, as pairs `(instance, value)`. -/
  chosen : N → Set (ℕ × V)
  /-- `prepare` messages `(proposer, ballot)`. -/
  m1a : Set (N × ℕ)
  /-- `prepareOK` messages. -/
  m1b : Set (Msg1b N V)
  /-- `accept` messages `(instance, ballot, value)` (Phase 2a). -/
  m2a : Set (ℕ × ℕ × V)
  /-- `acceptOK` messages `(acceptor, instance, ballot, value)` (Phase 2b). -/
  m2b : Set (N × ℕ × ℕ × V)

/-- The initial state: ballots `0`, no leader, empty logs, no messages. -/
def init : State N V where
  ballot _ := 0
  leader _ := false
  inst _ _ := none
  chosen _ := ∅
  m1a := ∅
  m1b := ∅
  m2a := ∅
  m2b := ∅

/-- `e` is `safeEntry` of the reports `S` at instance `i` (Figure 1, line 23): an entry with the
highest ballot among the reported entries for `i`, or empty if nobody reported one. -/
def IsSafeEntry (S : Finset (Msg1b N V)) (i : ℕ) : Option (ℕ × V) → Prop
  | none => ∀ m ∈ S, m.log i = none
  | some (c, v) => (∃ m ∈ S, m.log i = some (c, v)) ∧
      ∀ m ∈ S, ∀ c' v', m.log i = some (c', v') → c' ≤ c

variable [DecidableEq N]

/-- One step of MultiPaxos (Figure 1, repaired as explained in the module docstring). -/
inductive Step (Q : QuorumSystem N) : State N V → State N V → Prop
  /-- `Phase1a(s)`: increment the ballot, send `prepare` (and the implicit own `prepareOK`). -/
  | phase1a (p : State N V) (s : N) :
      Step Q p { p with
        ballot := Function.update p.ballot s (p.ballot s + 1)
        leader := Function.update p.leader s false
        m1a := insert (s, p.ballot s + 1) p.m1a
        m1b := insert ⟨s, s, p.ballot s + 1, p.inst s⟩ p.m1b }
  /-- `Phase1b(s)`: answer a `prepare` of `r` for a higher ballot `b`. -/
  | phase1b (p : State N V) (s r : N) (b : ℕ) (hm : (r, b) ∈ p.m1a) (hb : p.ballot s < b) :
      Step Q p { p with
        ballot := Function.update p.ballot s b
        leader := Function.update p.leader s false
        m1b := insert ⟨s, r, b, p.inst s⟩ p.m1b }
  /-- `Phase1Succeed(s)`: a quorum answered the current ballot; adopt the safe entries. -/
  | phase1Succeed (p : State N V) (s : N) (S : Finset (Msg1b N V)) (newInst : ℕ → Option (ℕ × V))
      (hl : p.leader s = false)
      (hS : ∀ m ∈ S, m ∈ p.m1b ∧ m.dst = s ∧ m.bal = p.ballot s)
      (hQ : Q.IsQuorum (S.image Msg1b.src))
      (hself : ∃ m ∈ S, m.src = s)
      (hsafe : ∀ i, IsSafeEntry S i (newInst i)) :
      Step Q p { p with
        inst := Function.update p.inst s newInst
        leader := Function.update p.leader s true }
  /-- `Phase2a(s, i, v)`: the leader proposes `v` for instance `i` in its ballot. -/
  | phase2a (p : State N V) (s : N) (i : ℕ) (v : V)
      (hl : p.leader s = true)
      (hv : p.inst s i = none ∨ ∃ c, p.inst s i = some (c, v))
      (huniq : ∀ w, (i, p.ballot s, w) ∈ p.m2a → w = v) :
      Step Q p { p with m2a := insert (i, p.ballot s, v) p.m2a }
  /-- `Phase2b(s)`: accept a proposal of a ballot at least the own one. -/
  | phase2b (p : State N V) (s : N) (i b : ℕ) (v : V)
      (hm : (i, b, v) ∈ p.m2a) (hb : p.ballot s ≤ b) :
      Step Q p { p with
        ballot := Function.update p.ballot s b
        leader := Function.update p.leader s (if p.ballot s < b then false else p.leader s)
        inst := Function.update p.inst s (Function.update (p.inst s) i (some (b, v)))
        m2b := insert (s, i, b, v) p.m2b }
  /-- `Learn(s)`: a quorum accepted `v` for instance `i` in ballot `b`. -/
  | learn (p : State N V) (s : N) (i b : ℕ) (v : V) (A : Finset N)
      (hA : Q.IsQuorum A) (hacc : ∀ a ∈ A, (a, i, b, v) ∈ p.m2b) :
      Step Q p { p with chosen := Function.update p.chosen s (insert (i, v) (p.chosen s)) }

/-- Reachable states of MultiPaxos. -/
def Reachable (Q : QuorumSystem N) (p : State N V) : Prop :=
  Relation.ReflTransGen (Step Q) init p

/-- `v` is chosen for instance `i` in ballot `b`: a quorum accepted it (TLA+ `ChosenAt`). -/
def ChosenAt (Q : QuorumSystem N) (p : State N V) (i b : ℕ) (v : V) : Prop :=
  ∃ A, Q.IsQuorum A ∧ ∀ a ∈ A, (a, i, b, v) ∈ p.m2b

end Paxos

end Podc.PaxosRaftRefinement
