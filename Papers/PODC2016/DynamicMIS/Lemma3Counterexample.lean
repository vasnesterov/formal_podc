import Papers.PODC2016.DynamicMIS.Lemma2

/-!
# Lemma 3 with "`= 1/|P|`" is false for edge changes

Lemma 3 of the paper claims, for every `P ⊆ V`,
`Pr[π(v*) = min π(P) | S′ = P ∧ π(v**) ≤ π(v*)] = 1/|P|`.
For an edge change with `v** ∈ P` this conditional probability is `0` (the paper's proof notes this
case and only concludes `≤ 1/|P|`, which suffices for Theorem 1).

Instance: `H` = the path `0 – 1 – 2` (the graph without the changed edge `{0, 2}`), `v* = 2`,
`v** = 0`. For the order `1 < 0 < 2` the set `S′` (influenced set of `v*` with `v*` moved to the
front) is `{0, 1, 2}` and `π(v**) ≤ π(v*)`, so the conditioning event is non-empty, while
`π(v*) = min π(P)` never holds on it.
-/

open Finset SimpleGraph

namespace DynamicMIS

/-- The order `1 < 0 < 2` on `Fin 3`. -/
def ceOrder : Fin 3 ≃ Fin (Fintype.card (Fin 3)) :=
  (Equiv.swap (0 : Fin 3) 1).trans (finCongr (Fintype.card_fin 3).symm)

theorem ceOrder_influencedFirst :
    (pathGraph 3).influencedFirst Set.univ ceOrder 2 = univ := by
  have hr : ∀ v : Fin 3, moveFirst ceOrder 2 v =
      if v = 2 then 0 else if v = 0 then 2 else 1 := by
    intro v; fin_cases v <;> rfl
  have h2 : (pathGraph 3).partialGreedy Set.univ (moveFirst ceOrder 2) 2 2 = none :=
    partialGreedy_self _
  have h1 : (pathGraph 3).partialGreedy Set.univ (moveFirst ceOrder 2) 2 1 = none := by
    rw [partialGreedy_eq_none_iff]
    refine Or.inr ⟨Set.mem_univ _, fun w hw hwr => ?_, 2, by simp [pathGraph_adj], by
      simp [hr], h2⟩
    fin_cases w
    · simp [hr] at hwr
    · simp at hw
    · simp
  have h0 : (pathGraph 3).partialGreedy Set.univ (moveFirst ceOrder 2) 2 0 = none := by
    rw [partialGreedy_eq_none_iff]
    refine Or.inr ⟨Set.mem_univ _, fun w hw hwr => ?_, 1, by simp [pathGraph_adj], by
      simp [hr], h1⟩
    fin_cases w
    · simp at hw
    · simp [h1]
    · simp [pathGraph_adj] at hw
  ext u
  simp only [mem_influencedFirst, Finset.mem_univ, iff_true]
  fin_cases u
  · exact h0
  · exact h1
  · exact h2

/-- **Lemma 3 (with equality) fails.** For the path `0 – 1 – 2` and the edge change `{0, 2}`
(`v* = 2`, `v** = 0`), the event `S′ = {0, 1, 2} ∧ π(v**) ≤ π(v*)` has positive probability, but
`π(v*) = min π(S′)` never holds on it: the conditional probability is `0 ≠ 1/3`. -/
theorem lemma3_eq_counterexample :
    (∃ π : Fin 3 ≃ Fin (Fintype.card (Fin 3)),
        (pathGraph 3).influencedFirst Set.univ π 2 = univ ∧ π 0 ≤ π 2) ∧
      ∀ π : Fin 3 ≃ Fin (Fintype.card (Fin 3)),
        (pathGraph 3).influencedFirst Set.univ π 2 = univ → π 0 ≤ π 2 →
          ¬ ∀ u ∈ (pathGraph 3).influencedFirst Set.univ π 2, π 2 ≤ π u := by
  refine ⟨⟨ceOrder, ceOrder_influencedFirst, by decide⟩, fun π hP h02 hmin => ?_⟩
  have := le_antisymm h02 (hmin 0 (by simp [hP]))
  exact absurd (π.injective this) (by decide)

end DynamicMIS
