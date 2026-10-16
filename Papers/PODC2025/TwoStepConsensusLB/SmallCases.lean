import Papers.PODC2025.TwoStepConsensusLB.LowerBound

/-!
# The degenerate case `n = 1`

The lower bounds `theorem_1_lower`, `theorem_2_lower` assume `n ≥ 2` (the paper assumes
`n ≥ 3`). This hypothesis is needed: with a single process, "decide your own input at once" is a
`1`-resilient `0`-two-step consensus task protocol, although `n = 1 < 3 = max {2e + f, 2f + 1}`.
-/

set_option linter.unusedSectionVars false

namespace TwoStepConsensus

/-- "Decide your own input": the state is the decision. -/
def selfDecide (V : Type*) : Protocol Unit V Unit (Option V) where
  init _ := none
  step _ _ s i _ := s.orElse fun _ => i
  send _ _ _ := []
  decide _ s := s

theorem selfDecide_st {V : Type*} (R : Run Unit V Unit) (I : Unit → V) (hR : R.inv = taskInv I)
    (τ : ℕ) : R.st (selfDecide V) τ () = none ∨ R.st (selfDecide V) τ () = some (I ()) := by
  induction τ with
  | zero => left; rfl
  | succ τ ih =>
    rw [Run.st_succ]
    split_ifs
    · change ((R.st (selfDecide V) τ ()).orElse fun _ => R.inv () τ) = none ∨
        ((R.st (selfDecide V) τ ()).orElse fun _ => R.inv () τ) = some (I ())
      rw [hR]
      rcases ih with h | h <;> rw [h] <;> simp only [taskInv] <;> split_ifs <;> simp
    · exact ih

/-- With `n = 1`, Theorem 1's bound `n ≥ max {2e + f, 2f + 1}` fails for `f = 1`, `e = 0`. -/
theorem theorem_1_fails_n_one {V : Type*} :
    SolvesTask (selfDecide V) 1 ∧ TwoStepTask (selfDecide V) 0 ∧
      ¬ (2 * 0 + 1 ≤ Fintype.card Unit ∧ 2 * 1 + 1 ≤ Fintype.card Unit) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, by simp⟩
  · intro R I _ hR p τ v hv
    refine ⟨(), ?_⟩
    rcases selfDecide_st R I hR τ with h | h <;> unfold Run.DecidesAt at hv <;>
      simp_all [selfDecide]
  · intro R I _ hR p q τ τ' v w hv hw
    rcases selfDecide_st R I hR τ with h | h <;> rcases selfDecide_st R I hR τ' with h' | h' <;>
      unfold Run.DecidesAt at hv hw <;> simp_all [selfDecide]
  · intro R I _ hR p hp
    refine ⟨1, I (), ?_⟩
    unfold Run.DecidesAt
    rw [Run.st_succ_of_alive _ _ (Run.alive_of_crash_none _ hp _)]
    simp [selfDecide, hR, taskInv]
  · intro E hE
    have hE : E = ∅ := Finset.card_eq_zero.mp hE
    subst hE
    have key : ∀ I : Unit → V, (syncRun (M := Unit) ∅ (taskInv I) fun _ _ l => l).DecidedBy2
        (selfDecide V) () := by
      intro I
      refine ⟨1, by omega, I (), ?_⟩
      unfold Run.DecidesAt
      rw [Run.st_succ_of_alive _ _ (Run.alive_of_crash_none _ (by simp [syncRun]) _)]
      simp [selfDecide, syncRun, taskInv]
    exact ⟨fun I => ⟨_, IsOrder.id, (), key I⟩, fun I _ p _ => ⟨_, IsOrder.id, key I⟩⟩

end TwoStepConsensus
