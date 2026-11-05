import Papers.PODC2019.PaxosRaftRefinement.Paxos

/-!
# The TLA+ module `MultiPaxos` of [paper] (Appendix B.1), transcribed, and its `Invariance` refuted

A line-by-line transcription of the TLA+ specification `MultiPaxos` printed in Appendix B.1 of
[paper] (pages 27–30 of the extended version); `Lnn` in docstrings refers to the line numbers of
the printed module.

Representation choices:

* constants: `Acceptor` is a type `A`, `Value` a type `V`, `Quorum` a `QuorumSystem A` (an
  intersecting family of finite sets of acceptors, which is `QuorumAssumption`, L28–29);
* `Ballot = Index = Nat` (L23–24); the "ballot" `-1` of empty log entries and of `logTail` is
  handled by using `ℤ` for those fields; `NoVal` (L25, a value outside `Value`) is `none`, so
  a log entry `⟨b, v⟩ ∈ (Ballot ∪ {-1}) × (Value ∪ {NoVal})` is a pair `ℤ × Option V`;
* `CHOOSE` (in `Max`, L7, and `GetHighestBallotEntry`, L64–67) is Hilbert's `Classical.epsilon`:
  deterministic, unspecified when nothing satisfies the predicate, as in TLA+;
* each action is a predicate on the pair (unprimed state `s`, primed state `s'`), listing every
  variable (the `UNCHANGED` clauses become equations); `TypeOK` (L136–145) holds by typing;
* `S ∈ SUBSET 1bmsgs` in `Next` (L162) ranges over finite subsets (`Finset`); `1bmsgs` is finite
  in every reachable state anyway.

In `Propose` (L118–123) the text "`⇒ v is safe at i, b`" after `logs[a][i][2] = NoVal` is a
grey comment, not part of the formula. So `Propose(a, i, v)` is enabled whenever `a` is a leader
and its log entry at `i` holds `v` or no value, and it records nothing in `logs`: a leader whose
entry is empty may propose *several different values* at the same index and ballot.

**Main result** (`tla_invariance_false`): with three acceptors, majority quorums and
`Value = Bool`, a state reachable from `Init` by `Next` steps violates `OneValuePerBallot`, and both
`true` and `false` are chosen at index `0`; hence `THEOREM Invariance` (L177) is false. The run:
`IncreaseHighestBallot(a0, 1)`, `Phase1a(a0)`, `Phase1b(a1, ·)`, `Phase1b(a2, ·)`,
`BecomeLeader(a1, {1b of a1, 1b of a2})`, `Propose(a1, 0, TRUE)`, `Propose(a1, 0, FALSE)`,
`Accept(a1, 0, 1, TRUE)`, `Accept(a2, 0, 1, TRUE)`, `Accept(a0, 0, 1, FALSE)`,
`Accept(a2, 0, 1, FALSE)`.

A second problem (`tla_two_leaders_same_ballot`): `1b` messages are not addressed to the
proposer that sent the `1a`, and `BecomeLeader(a, S)` only needs `a`'s own `1b` in `S`; so two
acceptors may become leaders of the same ballot from the same set of `1b` messages.
-/

namespace Podc.PaxosRaftRefinement

namespace TLA

open Relation

variable {A V : Type*}

/-- A `1a` message `[acc ↦ a, bal ↦ b]` (L97). -/
@[ext]
structure Msg1a (A : Type*) where
  /-- The sender. -/
  acc : A
  /-- Its ballot. -/
  bal : ℕ

/-- A `1b` message `[acc ↦ a, bal ↦ b, log ↦ logs[a], logTail ↦ logTail[a]]` (L105–106). -/
@[ext]
structure Msg1b (A V : Type*) where
  /-- The sender. -/
  acc : A
  /-- The ballot of the `1a` message answered. -/
  bal : ℕ
  /-- The sender's whole log. -/
  log : ℕ → ℤ × Option V
  /-- The sender's `logTail`. -/
  logTail : ℤ

/-- The variables of the module (L14–21). -/
@[ext]
structure State (A V : Type*) where
  /-- `highestBallot[a]`: the highest ballot number acceptor `a` has seen. -/
  highestBallot : A → ℕ
  /-- `isLeader[a]`: whether acceptor `a` is the leader and can propose values. -/
  isLeader : A → Bool
  /-- `logTail[a]`: pointer to the end of the log (`-1` for an empty log). -/
  logTail : A → ℤ
  /-- `votes[a][i]`: the set of votes `⟨b, v⟩` cast by acceptor `a` at index `i`. -/
  votes : A → ℕ → Set (ℕ × V)
  /-- `proposedValues`: the proposals `⟨i, b, v⟩`. -/
  proposedValues : Set (ℕ × ℕ × V)
  /-- `logs[a][i]`: the latest vote `⟨b, v⟩` cast by acceptor `a` at index `i`. -/
  logs : A → ℕ → ℤ × Option V
  /-- `1amsgs`. -/
  msgs1a : Set (Msg1a A)
  /-- `1bmsgs`. -/
  msgs1b : Set (Msg1b A V)

/-- `Max(s) ≜ CHOOSE x ∈ s : ∀ y ∈ s : x ≥ y` (L7). -/
noncomputable def tlaMax (s : Set ℤ) : ℤ :=
  Classical.epsilon fun x => x ∈ s ∧ ∀ y ∈ s, x ≥ y

/-- `VotedFor(a, i, b, v) ≜ ⟨b, v⟩ ∈ votes[a][i]` (L31). -/
def VotedFor (s : State A V) (a : A) (i b : ℕ) (v : V) : Prop :=
  (b, v) ∈ s.votes a i

/-- `ChosenAt(i, b, v) ≜ ∃ Q ∈ Quorum : ∀ a ∈ Q : VotedFor(a, i, b, v)` (L33–34). -/
def ChosenAt (Q : QuorumSystem A) (s : State A V) (i b : ℕ) (v : V) : Prop :=
  ∃ q, Q.IsQuorum q ∧ ∀ a ∈ q, VotedFor s a i b v

/-- `chosen ≜ [i ∈ Index ↦ {v ∈ Value : ∃ b ∈ Ballot : ChosenAt(i, b, v)}]` (L36). -/
def chosen (Q : QuorumSystem A) (s : State A V) (i : ℕ) : Set V :=
  {v | ∃ b, ChosenAt Q s i b v}

/-- `DidNotVoteAt(a, i, b) ≜ ∀ v ∈ Value : ¬VotedFor(a, i, b, v)` (L38). -/
def DidNotVoteAt (s : State A V) (a : A) (i b : ℕ) : Prop :=
  ∀ v, ¬ VotedFor s a i b v

/-- `CannotVoteAt(a, i, b) ≜ highestBallot[a] > b ∧ DidNotVoteAt(a, i, b)` (L40–41). -/
def CannotVoteAt (s : State A V) (a : A) (i b : ℕ) : Prop :=
  s.highestBallot a > b ∧ DidNotVoteAt s a i b

/-- `NoneOtherChoosableAt(i, b, v)` (L43–45). -/
def NoneOtherChoosableAt (Q : QuorumSystem A) (s : State A V) (i b : ℕ) (v : V) : Prop :=
  ∃ q, Q.IsQuorum q ∧ ∀ a ∈ q, VotedFor s a i b v ∨ CannotVoteAt s a i b

/-- `SafeAt(i, b, v) ≜ ∀ c ∈ 0 .. (b - 1) : NoneOtherChoosableAt(i, c, v)` (L47). -/
def SafeAt (Q : QuorumSystem A) (s : State A V) (i b : ℕ) (v : V) : Prop :=
  ∀ c < b, NoneOtherChoosableAt Q s i c v

/-- `ShowsSafeAt(Q, i, b, v)` (L49–53); `c` ranges over `-1 .. (b - 1)`. -/
def ShowsSafeAt (s : State A V) (q : Finset A) (i b : ℕ) (v : V) : Prop :=
  (∀ a ∈ q, s.highestBallot a ≥ b) ∧
  ∃ c : ℤ, -1 ≤ c ∧ c ≤ (b : ℤ) - 1 ∧
    (c ≠ -1 → ∃ a ∈ q, VotedFor s a i c.toNat v) ∧
    ∀ d : ℕ, c + 1 ≤ d → (d : ℤ) ≤ (b : ℤ) - 1 → ∀ a ∈ q, DidNotVoteAt s a i d

/-- `OneValuePerBallot` (L56–58). -/
def OneValuePerBallot (s : State A V) : Prop :=
  ∀ a1 a2 b v1 v2 i, VotedFor s a1 i b v1 ∧ VotedFor s a2 i b v2 → v1 = v2

/-- `LogsSafe` (L60–62). -/
def LogsSafe (Q : QuorumSystem A) (s : State A V) : Prop :=
  ∀ a (b : ℕ) i v, s.logs a i = ((b : ℤ), some v) → SafeAt Q s i b v

/-- `GetHighestBallotEntry(i, logsIn1b)` (L64–67): an entry at index `i` of one of the logs with
the highest ballot. -/
noncomputable def GetHighestBallotEntry (i : ℕ) (logsIn1b : Set (ℕ → ℤ × Option V)) :
    ℤ × Option V :=
  Classical.epsilon fun bv => (∃ log ∈ logsIn1b, bv = log i) ∧ ∀ log ∈ logsIn1b, bv.1 ≥ (log i).1

variable [DecidableEq A]

/-- `UpdateLog(a, logsIn1b, i1, i2)` (L69, L81–87). -/
def UpdateLog (a : A) (logsIn1b : Set (ℕ → ℤ × Option V)) (i1 i2 : ℤ) (s s' : State A V) :
    Prop :=
  (∀ i : ℕ, i1 ≤ i ∧ (i : ℤ) ≤ i2 → s'.logs a i = GetHighestBallotEntry i logsIn1b) ∧
  (∀ x, x ≠ a → s'.logs x = s.logs x) ∧
  (∀ i : ℕ, ¬ (i1 ≤ i ∧ (i : ℤ) ≤ i2) → s'.logs a i = s.logs a i) ∧
  s'.logTail = if i2 > s.logTail a then Function.update s.logTail a i2 else s.logTail

/-- `IncreaseHighestBallot(a, b)` (L89–93). -/
def IncreaseHighestBallot (a : A) (b : ℕ) (s s' : State A V) : Prop :=
  s.highestBallot a < b ∧
  s'.highestBallot = Function.update s.highestBallot a b ∧
  s'.isLeader = Function.update s.isLeader a false ∧
  s'.logTail = s.logTail ∧ s'.votes = s.votes ∧ s'.proposedValues = s.proposedValues ∧
  s'.logs = s.logs ∧ s'.msgs1a = s.msgs1a ∧ s'.msgs1b = s.msgs1b

/-- `Phase1a(a)` (L95–99). -/
def Phase1a (a : A) (s s' : State A V) : Prop :=
  s.isLeader a = false ∧
  s'.msgs1a = insert ⟨a, s.highestBallot a⟩ s.msgs1a ∧
  s'.highestBallot = s.highestBallot ∧ s'.isLeader = s.isLeader ∧ s'.logTail = s.logTail ∧
  s'.votes = s.votes ∧ s'.proposedValues = s.proposedValues ∧ s'.logs = s.logs ∧
  s'.msgs1b = s.msgs1b

/-- `Phase1b(a, 1amsg)` (L101–107). -/
def Phase1b (a : A) (m : Msg1a A) (s s' : State A V) : Prop :=
  m.bal > s.highestBallot a ∧
  s'.highestBallot = Function.update s.highestBallot a m.bal ∧
  s'.isLeader = Function.update s.isLeader a false ∧
  s'.msgs1b = insert ⟨a, m.bal, s.logs a, s.logTail a⟩ s.msgs1b ∧
  s'.logTail = s.logTail ∧ s'.votes = s.votes ∧ s'.proposedValues = s.proposedValues ∧
  s'.logs = s.logs ∧ s'.msgs1a = s.msgs1a

/-- `BecomeLeader(a, S)` (L109–116). -/
def BecomeLeader (Q : QuorumSystem A) (a : A) (S : Finset (Msg1b A V)) (s s' : State A V) :
    Prop :=
  s.isLeader a = false ∧
  (∃ m ∈ S, m.acc = a) ∧
  (∀ m ∈ S, m.bal = s.highestBallot a) ∧
  Q.IsQuorum (S.image Msg1b.acc) ∧
  UpdateLog a {l | ∃ m ∈ S, m.log = l} 0 (tlaMax {t | ∃ m ∈ S, m.logTail = t}) s s' ∧
  s'.isLeader = Function.update s.isLeader a true ∧
  s'.highestBallot = s.highestBallot ∧ s'.votes = s.votes ∧
  s'.proposedValues = s.proposedValues ∧ s'.msgs1a = s.msgs1a ∧ s'.msgs1b = s.msgs1b

/-- `Propose(a, i, v)` (L118–123). The grey "`⇒ v is safe at i, b`" on L121 is a comment. -/
def Propose (a : A) (i : ℕ) (v : V) (s s' : State A V) : Prop :=
  s.isLeader a = true ∧
  ((s.logs a i).2 = some v ∨ (s.logs a i).2 = none) ∧
  s'.proposedValues = insert (i, s.highestBallot a, v) s.proposedValues ∧
  s'.highestBallot = s.highestBallot ∧ s'.isLeader = s.isLeader ∧ s'.logTail = s.logTail ∧
  s'.votes = s.votes ∧ s'.logs = s.logs ∧ s'.msgs1a = s.msgs1a ∧ s'.msgs1b = s.msgs1b

/-- `Accept(a, i, b, v)` (L125–134). -/
def Accept (a : A) (i b : ℕ) (v : V) (s s' : State A V) : Prop :=
  (i, b, v) ∈ s.proposedValues ∧
  b ≥ s.highestBallot a ∧
  s'.highestBallot = Function.update s.highestBallot a b ∧
  s'.votes = Function.update s.votes a (Function.update (s.votes a) i (s.votes a i ∪ {(b, v)})) ∧
  s'.logs = Function.update s.logs a (Function.update (s.logs a) i ((b : ℤ), some v)) ∧
  s'.logTail = (if (i : ℤ) > s.logTail a then Function.update s.logTail a i else s.logTail) ∧
  s'.isLeader = (if b > s.highestBallot a then Function.update s.isLeader a false
    else s.isLeader) ∧
  s'.proposedValues = s.proposedValues ∧ s'.msgs1a = s.msgs1a ∧ s'.msgs1b = s.msgs1b

/-- `Init` (L147–154). -/
def Init (s : State A V) : Prop :=
  s.highestBallot = (fun _ => 0) ∧ s.isLeader = (fun _ => false) ∧ s.logTail = (fun _ => -1) ∧
  s.votes = (fun _ _ => ∅) ∧ s.logs = (fun _ _ => (-1, none)) ∧ s.proposedValues = ∅ ∧
  s.msgs1a = ∅ ∧ s.msgs1b = ∅

/-- `Next` (L156–167). -/
def Next (Q : QuorumSystem A) (s s' : State A V) : Prop :=
  (∃ a b, IncreaseHighestBallot a b s s') ∨
  (∃ a, Phase1a a s s') ∨
  (∃ a, ∃ m ∈ s.msgs1a, Phase1b a m s s') ∨
  (∃ a, ∃ S : Finset (Msg1b A V), ↑S ⊆ s.msgs1b ∧ BecomeLeader Q a S s s') ∨
  (∃ a i v, Propose a i v s s') ∨
  (∃ a, ∃ pv ∈ s.proposedValues, Accept a pv.1 pv.2.1 pv.2.2 s s')

/-- The states reachable in a behaviour of `Spec ≜ Init ∧ □[Next]_vars` (L172). -/
def Reachable (Q : QuorumSystem A) (s : State A V) : Prop :=
  ∃ s₀, Init s₀ ∧ ReflTransGen (Next Q) s₀ s

/-- `Inv ≜ TypeOK ∧ LogsSafe ∧ OneValuePerBallot` (L174); `TypeOK` holds by typing. -/
def Inv (Q : QuorumSystem A) (s : State A V) : Prop :=
  LogsSafe Q s ∧ OneValuePerBallot s

/-! ### Canonical successor states of the actions -/

section Successors

variable {Q : QuorumSystem A}

theorem tlaMax_eq {t : Set ℤ} {x : ℤ} (hx : x ∈ t) (hmax : ∀ y ∈ t, x ≥ y) : tlaMax t = x := by
  have h := Classical.epsilon_spec (p := fun x => x ∈ t ∧ ∀ y ∈ t, x ≥ y) ⟨x, hx, hmax⟩
  exact le_antisymm (hmax _ h.1) (h.2 x hx)

theorem next_increaseHighestBallot (s : State A V) (a : A) (b : ℕ) (h : s.highestBallot a < b) :
    Next Q s { s with highestBallot := Function.update s.highestBallot a b
                      isLeader := Function.update s.isLeader a false } :=
  Or.inl ⟨a, b, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem next_phase1a (s : State A V) (a : A) (h : s.isLeader a = false) :
    Next Q s { s with msgs1a := insert ⟨a, s.highestBallot a⟩ s.msgs1a } :=
  Or.inr <| Or.inl ⟨a, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem next_phase1b (s : State A V) (a : A) (m : Msg1a A) (hm : m ∈ s.msgs1a)
    (h : m.bal > s.highestBallot a) :
    Next Q s { s with highestBallot := Function.update s.highestBallot a m.bal
                      isLeader := Function.update s.isLeader a false
                      msgs1b := insert ⟨a, m.bal, s.logs a, s.logTail a⟩ s.msgs1b } :=
  Or.inr <| Or.inr <| Or.inl ⟨a, m, hm, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `BecomeLeader(a, S)` when every `1b` message of `S` reports an empty log tail (`-1`): the
range `0 .. Max({m.logTail : m ∈ S}) = 0 .. -1` of `UpdateLog` is empty, so only `isLeader`
changes. -/
theorem next_becomeLeader_of_empty (s : State A V) (a : A) (S : Finset (Msg1b A V))
    (hsub : ↑S ⊆ s.msgs1b) (hl : s.isLeader a = false) (hown : ∃ m ∈ S, m.acc = a)
    (hbal : ∀ m ∈ S, m.bal = s.highestBallot a) (hQ : Q.IsQuorum (S.image Msg1b.acc))
    (htail : ∀ m ∈ S, m.logTail = -1) (hat : -1 ≤ s.logTail a) :
    Next Q s { s with isLeader := Function.update s.isLeader a true } := by
  have hM : tlaMax {t | ∃ m ∈ S, m.logTail = t} = -1 := by
    obtain ⟨m, hm, -⟩ := hown
    refine tlaMax_eq ⟨m, hm, htail m hm⟩ ?_
    rintro y ⟨m', hm', rfl⟩
    rw [htail m' hm']
  refine Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨a, S, hsub, hl, hown, hbal, hQ,
    ⟨?_, fun _ _ => rfl, fun _ _ => rfl, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro i hi
    rw [hM] at hi
    omega
  · rw [hM]
    split_ifs <;> first | rfl | omega

theorem next_propose (s : State A V) (a : A) (i : ℕ) (v : V) (hl : s.isLeader a = true)
    (hv : (s.logs a i).2 = some v ∨ (s.logs a i).2 = none) :
    Next Q s { s with proposedValues := insert (i, s.highestBallot a, v) s.proposedValues } :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
    ⟨a, i, v, hl, hv, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem next_accept (s : State A V) (a : A) (i b : ℕ) (v : V)
    (hp : (i, b, v) ∈ s.proposedValues) (hb : b ≥ s.highestBallot a) :
    Next Q s { s with
      highestBallot := Function.update s.highestBallot a b
      votes := Function.update s.votes a
        (Function.update (s.votes a) i (s.votes a i ∪ {(b, v)}))
      logs := Function.update s.logs a (Function.update (s.logs a) i ((b : ℤ), some v))
      logTail := if (i : ℤ) > s.logTail a then Function.update s.logTail a i else s.logTail
      isLeader := if b > s.highestBallot a then Function.update s.isLeader a false
        else s.isLeader } :=
  Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr
    ⟨a, (i, b, v), hp, hp, hb, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Successors

/-! ### The counterexample -/

/-- The initial state. -/
def init : State A V where
  highestBallot _ := 0
  isLeader _ := false
  logTail _ := -1
  votes _ _ := ∅
  proposedValues := ∅
  logs _ _ := (-1, none)
  msgs1a := ∅
  msgs1b := ∅

omit [DecidableEq A] in
theorem init_Init : Init (init : State A V) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Majority quorums of three acceptors: any two of them. -/
abbrev Q3 : QuorumSystem (Fin 3) := QuorumSystem.majority (Fin 3)

/-- The two `1b` messages of the run (from `a1` and `a2`, ballot `1`, empty logs). -/
noncomputable abbrev S12 : Finset (Msg1b (Fin 3) Bool) :=
  open scoped Classical in {⟨1, 1, fun _ => (-1, none), -1⟩, ⟨2, 1, fun _ => (-1, none), -1⟩}

/-- **The TLA+ theorem `Invariance` (L177) of [paper], Appendix B.1, is false.** With three
acceptors, majority quorums and `Value = Bool`, a state reachable from `Init` by `Next` steps
violates `OneValuePerBallot` (hence `Inv`), and both values are chosen at index `0`. -/
theorem tla_invariance_false : ∃ s : State (Fin 3) Bool, Reachable Q3 s ∧
    ¬ OneValuePerBallot s ∧ ¬ Inv Q3 s ∧ chosen Q3 s 0 = Set.univ := by
  have h : ReflTransGen (Next Q3) init (init : State (Fin 3) Bool) := .refl
  -- IncreaseHighestBallot(a0, 1); Phase1a(a0); Phase1b(a1, ·); Phase1b(a2, ·)
  replace h := h.tail (next_increaseHighestBallot _ 0 1 (by simp [init]))
  replace h := h.tail (next_phase1a _ 0 (by simp [init]))
  replace h := h.tail (next_phase1b _ 1 ⟨0, 1⟩ (by simp) (by simp [init]))
  replace h := h.tail (next_phase1b _ 2 ⟨0, 1⟩ (by simp) (by simp [init]))
  -- BecomeLeader(a1, {1b of a1, 1b of a2})
  replace h := h.tail (next_becomeLeader_of_empty _ 1 S12
    (by intro m; simp [init]; tauto) (by simp [init]) (by simp) (by simp [init])
    (by simp [QuorumSystem.majority]) (by simp) (by simp [init]))
  -- Propose(a1, 0, TRUE); Propose(a1, 0, FALSE)
  replace h := h.tail (next_propose _ 1 0 true (by simp) (by simp [init]))
  replace h := h.tail (next_propose _ 1 0 false (by simp) (by simp [init]))
  -- Accept(a1, 0, 1, TRUE); Accept(a2, 0, 1, TRUE); Accept(a0, 0, 1, FALSE); Accept(a2, 0, 1, FALSE)
  replace h := h.tail (next_accept _ 1 0 1 true (by simp) (by simp))
  replace h := h.tail (next_accept _ 2 0 1 true (by simp) (by simp))
  replace h := h.tail (next_accept _ 0 0 1 false (by simp) (by simp))
  replace h := h.tail (next_accept _ 2 0 1 false (by simp) (by simp))
  have hov : ∀ t : State (Fin 3) Bool, (1, true) ∈ t.votes 1 0 → (1, false) ∈ t.votes 0 0 →
      ¬ OneValuePerBallot t := fun t h1 h2 hc =>
    absurd (hc 1 0 1 true false 0 ⟨h1, h2⟩) (by simp)
  refine ⟨_, ⟨init, init_Init, h⟩, hov _ (by simp) (by simp),
    fun hi => hov _ (by simp) (by simp) hi.2, ?_⟩
  clear h hov
  ext v
  simp only [Set.mem_univ, iff_true]
  refine ⟨1, ?_⟩
  cases v
  · exact ⟨{0, 2}, by simp [QuorumSystem.majority], by simp [VotedFor, init]⟩
  · exact ⟨{1, 2}, by simp [QuorumSystem.majority], by simp [VotedFor, init]⟩

/-- Two acceptors can become leaders of the same ballot `1` from the same two `1b` messages:
`1b` messages are not addressed to the proposer of the `1a`, and `BecomeLeader(a, S)` only
needs `a`'s own `1b` message in `S`. -/
theorem tla_two_leaders_same_ballot : ∃ s : State (Fin 3) Bool, Reachable Q3 s ∧
    s.isLeader 1 = true ∧ s.isLeader 2 = true ∧ s.highestBallot 1 = 1 ∧
    s.highestBallot 2 = 1 := by
  have h : ReflTransGen (Next Q3) init (init : State (Fin 3) Bool) := .refl
  replace h := h.tail (next_increaseHighestBallot _ 0 1 (by simp [init]))
  replace h := h.tail (next_phase1a _ 0 (by simp [init]))
  replace h := h.tail (next_phase1b _ 1 ⟨0, 1⟩ (by simp) (by simp [init]))
  replace h := h.tail (next_phase1b _ 2 ⟨0, 1⟩ (by simp) (by simp [init]))
  replace h := h.tail (next_becomeLeader_of_empty _ 1 S12
    (by intro m; simp [init]; tauto) (by simp [init]) (by simp) (by simp [init])
    (by simp [QuorumSystem.majority]) (by simp) (by simp [init]))
  replace h := h.tail (next_becomeLeader_of_empty _ 2 S12
    (by intro m; simp [init]; tauto) (by simp [init]) (by simp) (by simp [init])
    (by simp [QuorumSystem.majority]) (by simp) (by simp [init]))
  exact ⟨_, ⟨init, init_Init, h⟩, by simp, by simp, by simp, by simp⟩

end TLA

end Podc.PaxosRaftRefinement
