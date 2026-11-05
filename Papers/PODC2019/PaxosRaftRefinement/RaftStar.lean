import Papers.PODC2019.PaxosRaftRefinement.Paxos

/-!
# Raft* (Figure 2 of [paper]), as an interleaving transition system

Same network and failure model as `Paxos.lean`: asynchronous message passing, every message ever
sent stays in a set (loss, duplication, reordering), crash-stop servers (a crashed server takes no
further steps), any intersecting quorum system.

A log is a list of entries `(term, value)`; index `i` of the paper is position `i` of the list
(`lastIndex = length - 1`, `commitIndex = commit - 1`: we store the *number* of committed
entries). The `bal` field of Figure 2 is not modelled: the refinement mapping of Appendix C uses
the term of the last log entry as the accepted ballot of every entry (see `Refinement.lean`).

The model is parametrised by `Rules`:

* `voteOK L n t` — when a server with log `L` grants a `requestVote` of a candidate whose log has
  length `n` and last term `t` (Figure 2, lines 9–11). `Rules.fig2` is the rule as printed, which
  compares the voter's entry *at the candidate's last index* with the candidate's last term;
  `Rules.lastTerm` compares the voter's *last* term (as the TLA+ spec B.2 and Raft do);
* `heartbeat` — whether `AppendEntries` may carry no new value (Figure 2 does not exclude
  `vals = []`; the TLA+ spec always appends exactly one value).

Repairs of Figure 2 that are built in (see `differencies.md`): `RequestVote` resets `isLeader` and
casts the candidate's own (implicit) vote, which carries its whole log; `BecomeLeader` needs that
own vote among a quorum of votes and is guarded by `¬ isLeader` (as in the TLA+ spec); votes carry
the voter's whole log (Appendix C, step 2.2/3.5: "we can still assume Raft* includes the full
log"); an `append` message carries the leader's whole log `full` together with `prevLen` and the
receiver only uses `prevLen`, the term at `prevLen - 1` (`pTerm`) and the entries after `prevLen`
(`ents`), as in Figure 2.

Two ghost (history) variables, `props` and `acks`, record the Paxos `accept`/`acceptOK` messages
implied by Raft* steps (as `proposedValues` and `votes` in the TLA+ spec B.2); they do not influence
the behaviour.
-/

namespace Podc.PaxosRaftRefinement

namespace Raft

variable {N V : Type*}

/-- The term of the last entry of a log, `0` for the empty log (terms of entries are `≥ 1`). -/
def lastTerm (L : List (ℕ × V)) : ℕ := (L.getLast?.map Prod.fst).getD 0

/-- The term of the entry at position `n - 1` (`s.log[n-1].term`), `0` if `n = 0` or there is no
such entry (the paper's empty entry). -/
def termAt (L : List (ℕ × V)) (n : ℕ) : ℕ :=
  if n = 0 then 0 else ((L[n - 1]?).map Prod.fst).getD 0

/-- `requestVote(cand, term, lastIndex + 1, lastTerm)`. -/
@[ext]
structure RVMsg (N : Type*) where
  /-- The candidate. -/
  cand : N
  /-- Its new term. -/
  term : ℕ
  /-- Length of its log (`lastIndex + 1`). -/
  len : ℕ
  /-- Term of its last entry. -/
  lterm : ℕ

/-- `requestVoteOK`: `src` votes for `dst` in term `term`, sending its log. -/
@[ext]
structure RVOKMsg (N V : Type*) where
  /-- The voter. -/
  src : N
  /-- The candidate. -/
  dst : N
  /-- The term. -/
  term : ℕ
  /-- The voter's log. -/
  log : List (ℕ × V)

/-- `append(term, prev, pTerm, ents, commit)` sent by `src`, presented as the leader's whole log
`full` and `prevLen = prev + 1`: `ents = full.drop prevLen`, `pTerm = termAt full prevLen`. -/
@[ext]
structure AEMsg (N V : Type*) where
  /-- The leader. -/
  src : N
  /-- Its term. -/
  term : ℕ
  /-- `prev + 1`. -/
  prevLen : ℕ
  /-- The leader's log when sending. -/
  full : List (ℕ × V)
  /-- `commitIndex + 1` of the leader. -/
  commit : ℕ

/-- `appendOK(term, lastIndex)` from `src` to `dst`, with `len = lastIndex + 1`. -/
@[ext]
structure AEOKMsg (N : Type*) where
  /-- The follower. -/
  src : N
  /-- The leader. -/
  dst : N
  /-- The term. -/
  term : ℕ
  /-- The follower's log length. -/
  len : ℕ

/-- Global state of Raft*. -/
@[ext]
structure State (N V : Type*) where
  /-- `currentTerm`. -/
  term : N → ℕ
  /-- `isLeader`. -/
  leader : N → Bool
  /-- The log, entries `(term, value)`. -/
  log : N → List (ℕ × V)
  /-- `commitIndex + 1`. -/
  commit : N → ℕ
  /-- `requestVote` messages. -/
  rv : Set (RVMsg N)
  /-- `requestVoteOK` messages. -/
  rvok : Set (RVOKMsg N V)
  /-- `append` messages. -/
  ae : Set (AEMsg N V)
  /-- `appendOK` messages. -/
  aeok : Set (AEOKMsg N)
  /-- Ghost: Paxos proposals `(index, ballot, value)` implied so far. -/
  props : Set (ℕ × ℕ × V)
  /-- Ghost: Paxos acceptances `(server, index, ballot, value)` implied so far. -/
  acks : Set (N × ℕ × ℕ × V)

/-- The initial state. -/
def init : State N V where
  term _ := 0
  leader _ := false
  log _ := []
  commit _ := 0
  rv := ∅
  rvok := ∅
  ae := ∅
  aeok := ∅
  props := ∅
  acks := ∅

/-- Variants of the rules of Figure 2. -/
structure Rules (V : Type*) where
  /-- A server with log `L` may vote for a candidate with log length `n` and last term `t`. -/
  voteOK : List (ℕ × V) → ℕ → ℕ → Prop
  /-- `AppendEntries` may send no new value. -/
  heartbeat : Prop

/-- Figure 2, lines 9–11, as printed:
`s.log[lIndex].term < lTerm || (s.log[lIndex].term = lTerm && s.lastIndex ≥ lIndex)`. -/
def fig2VoteOK (L : List (ℕ × V)) (n t : ℕ) : Prop :=
  termAt L n < t ∨ (termAt L n = t ∧ n ≤ L.length)

/-- Raft's (and the TLA+ spec B.2's) up-to-date check: the voter's last term is smaller, or equal
with a log that is not longer. -/
def raftVoteOK (L : List (ℕ × V)) (n t : ℕ) : Prop :=
  lastTerm L < t ∨ (lastTerm L = t ∧ L.length ≤ n)

/-- Figure 2 with the voter's last entry instead of its entry at `lIndex`. -/
def fig2FixedVoteOK (L : List (ℕ × V)) (n t : ℕ) : Prop :=
  lastTerm L < t ∨ (lastTerm L = t ∧ n ≤ L.length)

/-- Figure 2 literally: the printed vote rule, and `AppendEntries` with any (possibly empty) `vals`. -/
def Rules.fig2 : Rules V := ⟨fig2VoteOK, True⟩

/-- Repaired Raft*: the voter's last term must not exceed the candidate's (any log lengths), and
every `AppendEntries` appends at least one value. -/
def Rules.repaired : Rules V := ⟨fun L _ t => lastTerm L ≤ t, False⟩

/-- `ext` extends a log of length `n` by safe entries of the votes `S` (Figure 2, lines 22–27):
the new length is the largest reported length, and the value at each new position is taken from a
vote whose log has the largest last term among the votes reaching that position. -/
def ExtOK (S : Finset (RVOKMsg N V)) (n : ℕ) (ext : List V) : Prop :=
  (∀ m ∈ S, m.log.length ≤ n + ext.length) ∧
  ∀ j (hj : j < ext.length), ∃ m ∈ S, ∃ c, m.log[n + j]? = some (c, ext[j]) ∧
    ∀ m' ∈ S, n + j < m'.log.length → lastTerm m'.log ≤ lastTerm m.log

/-- Ghost proposals of all entries of `L` in ballot `t`. -/
def propsOf (L : List (ℕ × V)) (t : ℕ) : Set (ℕ × ℕ × V) :=
  {x | ∃ i, ∃ h : i < L.length, x = (i, t, L[i].2)}

/-- Ghost acceptances by `s` of all entries of `L` in ballot `t`. -/
def acksOf (s : N) (L : List (ℕ × V)) (t : ℕ) : Set (N × ℕ × ℕ × V) :=
  {x | ∃ i, ∃ h : i < L.length, x = (s, i, t, L[i].2)}

/-- The follower's log matches the `append` message at `prevLen - 1` (Figure 2:
`s.log[prev].term == pTerm`). -/
def PrevMatch (L : List (ℕ × V)) (m : AEMsg N V) : Prop :=
  m.prevLen = 0 ∨ ∃ e ∈ L[m.prevLen - 1]?, ∃ e' ∈ m.full[m.prevLen - 1]?, e.1 = e'.1

variable [DecidableEq N]

/-- One step of Raft* (Figure 2) under the rules `R`. -/
inductive Step (Q : QuorumSystem N) (R : Rules V) : State N V → State N V → Prop
  /-- `RequestVote(s)` (with the candidate's own vote). -/
  | requestVote (r : State N V) (s : N) :
      Step Q R r { r with
        term := Function.update r.term s (r.term s + 1)
        leader := Function.update r.leader s false
        rv := insert ⟨s, r.term s + 1, (r.log s).length, lastTerm (r.log s)⟩ r.rv
        rvok := insert ⟨s, s, r.term s + 1, r.log s⟩ r.rvok }
  /-- `ReceiveVote(s)`. -/
  | receiveVote (r : State N V) (s : N) (m : RVMsg N) (hm : m ∈ r.rv) (ht : r.term s < m.term)
      (hv : R.voteOK (r.log s) m.len m.lterm) :
      Step Q R r { r with
        term := Function.update r.term s m.term
        leader := Function.update r.leader s false
        rvok := insert ⟨s, m.cand, m.term, r.log s⟩ r.rvok }
  /-- `BecomeLeader(s)`: keep the own log and extend it by the safe entries of the votes. -/
  | becomeLeader (r : State N V) (s : N) (S : Finset (RVOKMsg N V)) (ext : List V)
      (hl : r.leader s = false)
      (hS : ∀ m ∈ S, m ∈ r.rvok ∧ m.dst = s ∧ m.term = r.term s)
      (hself : ∃ m ∈ S, m.src = s)
      (hQ : Q.IsQuorum (S.image RVOKMsg.src))
      (hext : ExtOK S (r.log s).length ext) :
      Step Q R r { r with
        leader := Function.update r.leader s true
        log := Function.update r.log s (r.log s ++ ext.map (fun v => (r.term s, v)))
        props := if ext = [] then r.props else
          r.props ∪ propsOf (r.log s ++ ext.map (fun v => (r.term s, v))) (r.term s)
        acks := if ext = [] then r.acks else
          r.acks ∪ acksOf s (r.log s ++ ext.map (fun v => (r.term s, v))) (r.term s) }
  /-- `AppendEntries(s, vals, prev)`: append `vals` and send the entries after `prevLen`. -/
  | appendEntries (r : State N V) (s : N) (vals : List V) (prevLen : ℕ)
      (hl : r.leader s = true) (hvals : vals ≠ [] ∨ R.heartbeat)
      (hprev : prevLen ≤ (r.log s).length) :
      Step Q R r { r with
        log := Function.update r.log s (r.log s ++ vals.map (fun v => (r.term s, v)))
        ae := insert ⟨s, r.term s, prevLen, r.log s ++ vals.map (fun v => (r.term s, v)),
          r.commit s⟩ r.ae
        props := r.props ∪ propsOf (r.log s ++ vals.map (fun v => (r.term s, v))) (r.term s)
        acks := r.acks ∪ acksOf s (r.log s ++ vals.map (fun v => (r.term s, v))) (r.term s) }
  /-- `ReceiveAppend(s)`: Raft* rejects an `append` that would erase entries. -/
  | receiveAppend (r : State N V) (s : N) (m : AEMsg N V) (hm : m ∈ r.ae)
      (ht : r.term s ≤ m.term) (hprev : m.prevLen ≤ (r.log s).length)
      (hmatch : PrevMatch (r.log s) m) (hlen : (r.log s).length ≤ m.full.length) :
      Step Q R r { r with
        term := Function.update r.term s m.term
        leader := Function.update r.leader s (if r.term s < m.term then false else r.leader s)
        log := Function.update r.log s ((r.log s).take m.prevLen ++ m.full.drop m.prevLen)
        commit := Function.update r.commit s (max m.commit (r.commit s))
        aeok := insert ⟨s, m.src, m.term, m.full.length⟩ r.aeok
        acks := r.acks ∪
          acksOf s ((r.log s).take m.prevLen ++ m.full.drop m.prevLen) m.term }
  /-- `LeaderLearn(s)`: commit up to an index acknowledged by the followers in `S`. -/
  | leaderLearn (r : State N V) (s : N) (S : Finset (AEOKMsg N)) (k : ℕ)
      (hl : r.leader s = true)
      (hS : ∀ m ∈ S, m ∈ r.aeok ∧ m.dst = s ∧ m.term = r.term s)
      (hQ : Q.IsQuorum (insert s (S.image AEOKMsg.src)))
      (hk : ∀ m ∈ S, k ≤ m.len) (hkl : k ≤ (r.log s).length) :
      Step Q R r { r with commit := Function.update r.commit s (max (r.commit s) k) }

/-- Reachable states of Raft* under the rules `R`. -/
def Reachable (Q : QuorumSystem N) (R : Rules V) (r : State N V) : Prop :=
  Relation.ReflTransGen (Step Q R) init r

/-- The committed prefix agrees: **state machine safety** of Raft. -/
def CommitSafe (r : State N V) : Prop :=
  ∀ s s' i (h : i < (r.log s).length) (h' : i < (r.log s').length),
    i < r.commit s → i < r.commit s' → (r.log s)[i].2 = (r.log s')[i].2

end Raft

end Podc.PaxosRaftRefinement
