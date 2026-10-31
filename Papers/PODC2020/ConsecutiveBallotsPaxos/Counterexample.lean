import Papers.PODC2020.ConsecutiveBallotsPaxos.Examples

/-!
# Lemmas 4.2' and 4.3' are false for the literal Definition 6

Definition 6 of [paper] reads `Chosen(i, v) ≡ ∃ Qᵢ. CQ(Qᵢ, v) ∧ ∃ α ∈ Qᵢ. accept(i, v)_α ∈ sent_α`.
The ballot-`i` accept of `α` need not be the accept of `α` that is part of the Consecutive Quorum.
Execution (five acceptors `A..E = 0..4`, Classic Paxos, majority quorums):

* ballot 3: promises `A, B, C` (all `⊥`), `x` proposed, accepted by `A`;
* ballot 5: promises `B, C, D` (all `⊥`), `y` proposed, accepted by `D`;
* ballot 9: promises `A (3,x)`, `B ⊥`, `C ⊥`, `x` proposed, accepted by `A, B, C`.

Then `{A, B, C}` is a (classic, hence consecutive) quorum for `x` in ballot 9 and `A` also sent
`accept(3, x)`, so `x` is "chosen in ballot 3" by the literal Definition 6. But `y ≠ x` was proposed
in ballot `5 > 3` (refuting Lemma 4.3') and accepted by `D` in ballot `5 > 3` (refuting
Lemma 4.2'). Safety itself is not affected (`theorem_3_2`): `y` is never chosen.
-/

namespace Podc.ConsecutiveBallotsPaxos

open Msg

/-- The counterexample execution. -/
def cexActs : List (Action (Fin 5) Val) :=
  [.prepare 3, .promise 0 3, .promise 1 3, .promise 2 3, .propose 3 .x, .accept 0 3 .x,
   .prepare 5, .promise 1 5, .promise 2 5, .promise 3 5, .propose 5 .y, .accept 3 5 .y,
   .prepare 9, .promise 0 9, .promise 1 9, .promise 2 9, .propose 9 .x,
   .accept 0 9 .x, .accept 1 9 .x, .accept 2 9 .x]

lemma cexActs_valid : ValidFrom QS5 false init cexActs := by
  simp [cexActs, ValidFrom, Action.Enabled, Action.apply, init, ProposalOK, NormalClause]
  have maj : ∀ a b c : Fin 5, a ≠ b → a ≠ c → b ≠ c → QS5.IsQuorum {a, b, c} := by
    intro a b c hab hac hbc
    simp [QuorumSystem.majority, Finset.card_insert_of_notMem, hab, hac, hbc]
  refine ⟨WithBot.bot_lt_coe _, ⟨{0, 1, 2}, maj _ _ _ (by decide) (by decide) (by decide), by simp⟩,
    by decide, WithBot.bot_lt_coe _,
    ⟨{1, 2, 3}, maj _ _ _ (by decide) (by decide) (by decide), by simp⟩, by decide, by decide,
    ⟨{0, 1, 2}, maj _ _ _ (by decide) (by decide) (by decide), by simp, Or.inr ⟨by simp, by simp⟩⟩⟩

/-- The final state of the counterexample execution. -/
noncomputable def cex : State (Fin 5) Val := runFrom init cexActs

lemma cex_reachable : Reachable QS5 false cex := reachable_runFrom .refl cexActs_valid

lemma cex_accept {a : Fin 5} {b : ℕ} {v : Val} :
    accept a b v ∈ cex.msgs ↔
      (a = 0 ∧ b = 3 ∧ v = .x) ∨ (a = 3 ∧ b = 5 ∧ v = .y) ∨
      (a = 0 ∧ b = 9 ∧ v = .x) ∨ (a = 1 ∧ b = 9 ∧ v = .x) ∨ (a = 2 ∧ b = 9 ∧ v = .x) := by
  simp only [cex, cexActs, runFrom, Action.apply, init]
  simp
  tauto

lemma cex_propose_5 : propose 5 Val.y ∈ cex.msgs := by
  simp [cex, cexActs, runFrom, Action.apply, init]

/-- `x` is "chosen in ballot 3" according to the literal Definition 6. -/
theorem cex_chosen_3 : CQChosen QS5 cex.msgs 3 .x := by
  refine ⟨{0, 1, 2}, ⟨by simp [QuorumSystem.majority], fun _ => 9, fun a ha => ?_, ?_⟩, 0, by simp,
    cex_accept.mpr (by simp)⟩
  · simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rw [cex_accept]
    rcases ha with rfl | rfl | rfl <;> simp
  · rw [Set.Nonempty.image_const ⟨0, by simp⟩]
    exact consecutiveSet_singleton 9

/-- … but not in the intended sense (the ballot-3 accept is not part of a Consecutive Quorum). -/
theorem cex_not_chosen'_3 : ¬ CQChosen' QS5 cex.msgs 3 .x := fun h =>
  absurd (lemma_4_3' cex_reachable h (by norm_num : 3 < 5) cex_propose_5) (by decide)

/-- **Lemma 4.3' of [paper] is false for the literal Definition 6**: `x` is chosen in ballot 3,
yet `y ≠ x` is proposed in ballot `5 > 3`, in a reachable state of Classic Paxos with five
acceptors and majority quorums. The intended version is `lemma_4_3'`. -/
theorem lemma_4_3'_literal_false :
    ¬ ∀ s : State (Fin 5) Val, Reachable QS5 false s → ∀ i v, CQChosen QS5 s.msgs i v →
      ∀ j, i < j → ∀ w, propose j w ∈ s.msgs → w = v := by
  intro h
  exact absurd (h cex cex_reachable 3 .x cex_chosen_3 5 (by norm_num) .y cex_propose_5)
    (by decide)

/-- **Lemma 4.2' of [paper] is false for the literal Definition 6**: acceptor `D` accepted `y`
in ballot 5, yet `x ≠ y` is chosen in ballot `3 < 5`. The intended version is `lemma_4_2'`. -/
theorem lemma_4_2'_literal_false :
    ¬ ∀ s : State (Fin 5) Val, Reachable QS5 false s → ∀ a i v, accept a i v ∈ s.msgs →
      ∀ j, j < i → ∀ w, CQChosen QS5 s.msgs j w → w = v := by
  intro h
  exact absurd (h cex cex_reachable 3 5 .y (cex_accept.mpr (by simp)) 3 (by norm_num) .x
    cex_chosen_3) (by decide)

end Podc.ConsecutiveBallotsPaxos
