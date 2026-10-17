import Papers.PODC2013.CongestedCliqueRouting.SortMain

/-!
# Sanity checks: the specifications are not vacuous

Messages and keys cannot be delivered without communication: no algorithm solves the routing
task or the sorting task in `0` rounds once `n ≥ 2`. (The model forbids "teleporting" messages:
a node holds only its own inputs and what it has received.)
-/

namespace CongestedCliqueRouting

open Finset

/-- Routing needs at least one round (for `n ≥ 2`). -/
theorem routing_not_zero_rounds (n B : ℕ) (hn : 2 ≤ n) :
    ¬ ∃ A : Algorithm (Fin n) (Fin n → Option (Fin n)) (Header n) B, Solves A 0 := by
  rintro ⟨A, hA⟩
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  let d : RoutingInstance n := fun i j => if i = a ∧ j = a then some b else none
  have hload : d.LoadOK := by
    intro k
    calc (univ.filter fun p : Fin n × Fin n => d p.1 p.2 = some k).card
        ≤ ({(a, a)} : Finset (Fin n × Fin n)).card := by
          refine card_le_card fun p hp => ?_
          simp only [mem_filter, mem_univ, true_and, d] at hp
          split_ifs at hp with h
          · simp [Prod.ext_iff, h.1, h.2]
      _ ≤ n := by simp; omega
  have := (hA d hload).2.2 a a b (by simp [d])
  rcases this with ⟨h, -⟩ | ⟨r, hr, -⟩
  · simp [a, b, Fin.ext_iff] at h
  · omega

/-- Sorting needs at least one round (already for `n = 2`). -/
theorem sorting_not_zero_rounds (B : ℕ) :
    ¬ ∃ A : Algorithm (Fin 2) (Fin 2 → ℕ) ℕ B, SortSolves A 0 := by
  rintro ⟨A, hA⟩
  -- node `0` holds the keys `2, 3`, node `1` holds `0, 1`
  let keys : Fin 2 → Fin 2 → ℕ := fun i j => (1 - i) * 2 + j
  have hinj : Function.Injective fun p : Fin 2 × Fin 2 => keys p.1 p.2 := by decide
  have hrank : keyRank keys (keys 0 0) = 2 := by decide
  have := (hA keys hinj).2.2 0 0 1 (by rw [hrank]; rfl)
  rcases this with ⟨j, hj⟩ | ⟨r, hr, -⟩
  · revert hj; revert j; decide
  · omega

end CongestedCliqueRouting
