import Papers.PODC2020.ConsecutiveBallotsPaxos.Safety

/-!
# Concrete executions (Tables 1–3 of [paper])

Five acceptors `A, B, C, D, E` (`Fin 5`), majority quorums, values `x, y`.
-/

namespace Podc.ConsecutiveBallotsPaxos

open Msg

variable {A V : Type*} [DecidableEq A]

/-- Run a list of actions from a state. -/
def runFrom : State A V → List (Action A V) → State A V
  | s, [] => s
  | s, act :: rest => runFrom (act.apply s) rest

/-- Every action of the list is enabled when it is taken. -/
def ValidFrom (QS : QuorumSystem A) (cp : Bool) : State A V → List (Action A V) → Prop
  | _, [] => True
  | s, act :: rest => act.Enabled QS cp s ∧ ValidFrom QS cp (act.apply s) rest

lemma reachable_runFrom {QS : QuorumSystem A} {cp : Bool} {s : State A V}
    (hs : Reachable QS cp s) {acts : List (Action A V)} (h : ValidFrom QS cp s acts) :
    Reachable QS cp (runFrom s acts) := by
  induction acts generalizing s with
  | nil => exact hs
  | cons act rest ih => exact ih (hs.tail ⟨act, h.1, rfl⟩) h.2

lemma validFrom_append {QS : QuorumSystem A} {cp : Bool} {s : State A V}
    {l₁ l₂ : List (Action A V)} (h₁ : ValidFrom QS cp s l₁)
    (h₂ : ValidFrom QS cp (runFrom s l₁) l₂) : ValidFrom QS cp s (l₁ ++ l₂) := by
  induction l₁ generalizing s with
  | nil => exact h₂
  | cons act rest ih => exact ⟨h₁.1, ih h₁.2 h₂⟩

lemma runFrom_append (s : State A V) (l₁ l₂ : List (Action A V)) :
    runFrom s (l₁ ++ l₂) = runFrom (runFrom s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => rfl
  | cons act rest ih => exact ih _

/-- Two values. -/
inductive Val | x | y
  deriving DecidableEq

/-- Majority quorums over five acceptors. -/
abbrev QS5 : QuorumSystem (Fin 5) := QuorumSystem.majority (Fin 5)

/-- Table 3 execution: ballot 9 is proposed with `x` (promises from `C, D, E`, all `⊥`) and
accepted by `D, E`; ballot 10 is proposed with `x` (promises `C ⊥, D (9,x), E (9,x)`) and accepted
by `C`. Acceptors: `A = 0, …, E = 4`. -/
def table3 : List (Action (Fin 5) Val) :=
  [.prepare 9, .promise 2 9, .promise 3 9, .promise 4 9, .propose 9 .x,
   .accept 3 9 .x, .accept 4 9 .x,
   .prepare 10, .promise 2 10, .promise 3 10, .promise 4 10, .propose 10 .x,
   .accept 2 10 .x]

lemma table3_valid : ValidFrom QS5 false init table3 := by
  simp [table3, ValidFrom, Action.Enabled, Action.apply, init, ProposalOK, NormalClause]
  refine ⟨WithBot.bot_lt_coe _, ⟨{2, 3, 4}, by simp [QuorumSystem.majority], by simp⟩, by decide,
    ⟨{2, 3, 4}, by simp [QuorumSystem.majority], by simp, Or.inr ⟨4, by simp, 9, by simp, by simp⟩⟩⟩

/-- The final state of the Table 3 execution. -/
noncomputable def s3 : State (Fin 5) Val := runFrom init table3

lemma s3_reachable : Reachable QS5 false s3 := reachable_runFrom .refl table3_valid

lemma s3_accept {a : Fin 5} {b : ℕ} {v : Val} :
    accept a b v ∈ s3.msgs ↔ (a = 2 ∧ b = 10 ∨ a = 3 ∧ b = 9 ∨ a = 4 ∧ b = 9) ∧ v = .x := by
  simp only [s3, table3, runFrom, Action.apply, init]
  simp
  tauto

/-- Table 3 of [paper]: the accepts `C (x,10)`, `D (x,9)`, `E (x,9)` form a Consecutive Quorum, so
`x` is CQ chosen (in ballots 9 and 10, also in the intended sense of Definition 6) … -/
theorem table3_cqChosen : CQChosen' QS5 s3.msgs 10 .x ∧ CQChosen' QS5 s3.msgs 9 .x := by
  have hc : ConsecutiveSet ((fun a : Fin 5 => if a = 2 then 10 else 9) '' (({2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))) := by
    have : (fun a : Fin 5 => if a = 2 then 10 else 9) '' (({2, 3, 4} : Finset (Fin 5)) : Set (Fin 5))
        = Set.Icc 9 10 := by
      ext n
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc]
      simp
      omega
    rw [this]; exact consecutiveSet_Icc 9 10
  refine ⟨⟨{2, 3, 4}, by simp [QuorumSystem.majority], fun a => if a = 2 then 10 else 9,
    fun a ha => ?_, hc, 2, by simp, by simp⟩,
    ⟨{2, 3, 4}, by simp [QuorumSystem.majority], fun a => if a = 2 then 10 else 9,
    fun a ha => ?_, hc, 3, by simp, by simp⟩⟩ <;>
  · rw [s3_accept]
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp

/-- … but `x` is not chosen in the classic sense (Definition 4): no majority accepted it in a
single ballot. Hence CQ Chosen is strictly weaker than Classic Chosen (Section 4). -/
theorem table3_not_classicChosen (i : ℕ) (v : Val) : ¬ ClassicChosen QS5 s3.msgs i v := by
  rintro ⟨Q, hQ, hacc⟩
  have hQ' : 5 < 2 * Q.card := by simpa [QuorumSystem.majority] using hQ
  have hsub : Q ⊆ (if i = 9 then {3, 4} else {2}) := by
    intro a ha
    have := (s3_accept.mp (hacc a ha)).1
    split_ifs with h
    · subst h; simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · simp only [Finset.mem_singleton]; omega
  have := Finset.card_le_card hsub
  split_ifs at this <;> simp at this <;> omega

/-- … and no other value can be learned (Table 3: "no other value can be learned"). -/
theorem table3_only_x {i : ℕ} {w : Val} (h : CQChosen QS5 s3.msgs i w) : w = .x :=
  theorem_3_2 s3_reachable h table3_cqChosen.1.cqChosen

/-! ### Table 2: a majority accepting the same value in non-consecutive ballots is not enough -/

/-- Table 2 execution (ballots 7–10), followed by ballot 11 in which `y` is proposed (promises
`A ⊥`, `B (8,y)`, `E (7,x)`) and accepted by `A, B, E`. -/
def table2 : List (Action (Fin 5) Val) :=
  [.prepare 7, .promise 2 7, .promise 3 7, .promise 4 7, .propose 7 .x, .accept 4 7 .x,
   .prepare 8, .promise 0 8, .promise 1 8, .promise 2 8, .propose 8 .y, .accept 1 8 .y,
   .prepare 9, .promise 2 9, .promise 3 9, .promise 4 9, .propose 9 .x, .accept 3 9 .x,
   .prepare 10, .promise 2 10, .promise 3 10, .promise 4 10, .propose 10 .x, .accept 2 10 .x,
   .prepare 11, .promise 0 11, .promise 1 11, .promise 4 11, .propose 11 .y,
   .accept 0 11 .y, .accept 1 11 .y, .accept 4 11 .y]

lemma table2_valid : ValidFrom QS5 false init table2 := by
  simp [table2, ValidFrom, Action.Enabled, Action.apply, init, ProposalOK, NormalClause]
  have maj : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c → QS5.IsQuorum {a, b, c} := by
    intro a b c hab hac hbc
    simp [QuorumSystem.majority, Finset.card_insert_of_notMem, hab, hac, hbc]
  refine ⟨WithBot.bot_lt_coe _, ⟨{2, 3, 4}, maj _ _ _ (by decide) (by decide) (by decide), by simp⟩,
    WithBot.bot_lt_coe _, by decide,
    ⟨{0, 1, 2}, maj _ _ _ (by decide) (by decide) (by decide), by simp⟩, by decide, by decide,
    ⟨{2, 3, 4}, maj _ _ _ (by decide) (by decide) (by decide), by simp, Or.inr ⟨by simp, by simp⟩⟩,
    by decide,
    ⟨{2, 3, 4}, maj _ _ _ (by decide) (by decide) (by decide), by simp,
      Or.inr ⟨3, by simp, 9, by simp, by simp⟩⟩, by decide, by decide,
    ⟨{0, 1, 4}, maj _ _ _ (by decide) (by decide) (by decide), by simp, Or.inr ⟨by simp, by simp⟩⟩⟩

/-- The final state of the Table 2 execution (extended by ballot 11). -/
noncomputable def s2 : State (Fin 5) Val := runFrom init table2

lemma s2_reachable : Reachable QS5 false s2 := reachable_runFrom .refl table2_valid

lemma s2_accept {a : Fin 5} {b : ℕ} {v : Val} :
    accept a b v ∈ s2.msgs ↔
      (a = 4 ∧ b = 7 ∧ v = .x) ∨ (a = 1 ∧ b = 8 ∧ v = .y) ∨ (a = 3 ∧ b = 9 ∧ v = .x) ∨
      (a = 2 ∧ b = 10 ∧ v = .x) ∨ (a = 0 ∧ b = 11 ∧ v = .y) ∨ (a = 1 ∧ b = 11 ∧ v = .y) ∨
      (a = 4 ∧ b = 11 ∧ v = .y) := by
  simp only [s2, table2, runFrom, Action.apply, init]
  simp
  tauto

/-- The naive learning criterion rejected in Section 1.1: a majority accepted `v`, in arbitrary
ballots. -/
def NaiveChosen {A V : Type*} (QS : QuorumSystem A) (M : Set (Msg A V)) (v : V) : Prop :=
  ∃ Q, QS.IsQuorum Q ∧ ∀ a ∈ Q, ∃ b, accept a b v ∈ M

/-- Tables 1–2 of [paper]: in a reachable state of Classic Paxos, the majority `C, D, E` accepted
`x` (in the non-consecutive ballots `10, 9, 7`), and yet `y` is chosen in ballot 11 by `A, B, E`.
So "a majority accepted the same value" is not a safe learning criterion; the consecutiveness
requirement of Definition 5 cannot be dropped. -/
theorem table2_naive_unsafe :
    ∃ s, Reachable QS5 false s ∧ NaiveChosen QS5 s.msgs Val.x ∧ ClassicChosen QS5 s.msgs 11 .y ∧
      accept 2 10 Val.x ∈ s.msgs ∧ accept 3 9 Val.x ∈ s.msgs ∧ accept 4 7 Val.x ∈ s.msgs := by
  refine ⟨s2, s2_reachable, ⟨{2, 3, 4}, by simp [QuorumSystem.majority], ?_⟩,
    ⟨{0, 1, 4}, by simp [QuorumSystem.majority], ?_⟩, ?_, ?_, ?_⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨10, s2_accept.mpr (by simp)⟩
    · exact ⟨9, s2_accept.mpr (by simp)⟩
    · exact ⟨7, s2_accept.mpr (by simp)⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [s2_accept]
    rcases ha with rfl | rfl | rfl <;> simp
  all_goals exact s2_accept.mpr (by simp)

/-! ### Consecutive Paxos (Sections 5–6): a Consecutive Proposal in action -/

/-- Ballot 1: promises `A, B, C` (`⊥`), `x` proposed and accepted by `A`. Ballot 2: `x` proposed by
a Consecutive Proposal (Definition 12: the proposer saw `accept(1, x)` of `A`), without any promise,
and accepted by `B, C`. -/
def consecActs : List (Action (Fin 5) Val) :=
  [.prepare 1, .promise 0 1, .promise 1 1, .promise 2 1, .propose 1 .x, .accept 0 1 .x,
   .propose 2 .x, .accept 1 2 .x, .accept 2 2 .x]

lemma consecActs_valid : ValidFrom QS5 true init consecActs := by
  simp [consecActs, ValidFrom, Action.Enabled, Action.apply, init, ProposalOK, NormalClause,
    ConsecClause]
  exact ⟨{0, 1, 2}, by simp [QuorumSystem.majority], by simp⟩

/-- Non-vacuity of the Consecutive Paxos model: a reachable state in which `x` is CQ chosen through
the consecutive ballots `{1, 2}`, using a Consecutive Proposal, and not classically chosen in
ballot 2 at that point. -/
theorem consecPaxos_example :
    ∃ s, Reachable QS5 true s ∧ CQChosen' QS5 s.msgs 2 Val.x ∧
      (∀ w, propose 2 w ∈ s.msgs → ∀ a r, promise a 2 r ∉ s.msgs) := by
  refine ⟨runFrom init consecActs, reachable_runFrom .refl consecActs_valid,
    ⟨{0, 1, 2}, by simp [QuorumSystem.majority], fun a => if a = 0 then 1 else 2, ?_, ?_, 1,
      by simp, by simp⟩, ?_⟩
  · intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl <;> simp [consecActs, runFrom, Action.apply, init]
  · have : (fun a : Fin 5 => if a = 0 then 1 else 2) '' (({0, 1, 2} : Finset (Fin 5)) : Set (Fin 5))
        = Set.Icc 1 2 := by
      ext n
      simp only [Finset.coe_insert, Finset.coe_singleton, Set.image_insert_eq, Set.image_singleton,
        Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_Icc]
      simp
      omega
    rw [this]; exact consecutiveSet_Icc 1 2
  · intro w _ a r
    simp [consecActs, runFrom, Action.apply, init]

end Podc.ConsecutiveBallotsPaxos
