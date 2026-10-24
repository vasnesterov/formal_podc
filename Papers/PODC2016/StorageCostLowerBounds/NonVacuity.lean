import Papers.PODC2016.StorageCostLowerBounds.Witness
import Papers.PODC2016.StorageCostLowerBounds.Corollary42

/-!
# Non-vacuity of the repaired Theorem 4.1

The single-server register (`Witness.lean`, `n = 1`, `f = 0`) satisfies all hypotheses of
`theorem41_count` / `theorem41` / `theoremB1_count`: regular (even atomic), live, no gossip,
`ReaderQuiet` (via `RepliesOnly`), and its server has `|V|` states.
-/

namespace Podc.StorageCost

open Cslib.ChannelFailures Cslib.SharedMemory

/-- The repaired Theorem 4.1 applies to the single-server register; for it the bound reads
`|V| (|V| - 1) ≤ |V| · |V|`. -/
theorem nonvacuous_theorem41 {V : Type} [Fintype V] (v₀ : V) :
    Fintype.card V * (Fintype.card V - 1) ≤
      (∏ i ∈ (Finset.univ : Finset (Fin 1)), (Witness.srvStates v₀ i).card) *
        ∑ i ∈ (Finset.univ : Finset (Fin 1)), (Witness.srvStates v₀ i).card := by
  obtain ⟨hR, -, hL, hG, hRO, hS, -⟩ := Witness.witness_hyps v₀
  exact theorem41_count (f := 0) hR hL hG (readerQuiet_of_repliesOnly hRO) hS (by simp)
    Finset.univ_nonempty

/-- The hypotheses of the repaired theorems are satisfiable with `|V|` server states. -/
theorem nonvacuous_hyps {V : Type} [Fintype V] (v₀ : V) :
    IsRegular (Witness.alg v₀) ∧ Live (Witness.alg v₀) 0 ∧ NoGossip (Witness.alg v₀) ∧
      ReaderQuiet (Witness.alg v₀) ∧ StateBound (Witness.alg v₀) (Witness.srvStates v₀) ∧
      (Witness.srvStates v₀ 0).card = Fintype.card V := by
  obtain ⟨hR, -, hL, hG, hRO, hS, hc⟩ := Witness.witness_hyps v₀
  exact ⟨hR, hL, hG, readerQuiet_of_repliesOnly hRO, hS, hc⟩

end Podc.StorageCost
