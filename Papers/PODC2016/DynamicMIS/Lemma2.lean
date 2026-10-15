import Papers.PODC2016.DynamicMIS.Theorem1

/-!
# Lemma 2 and the exact value of `E|S|` for node changes

* `lemma2`: the paper's Lemma 2. `S'` is the influenced set of `v*` computed in the base graph (the
  graph without the changed edge; with the changed node) for the order in which `v*` is moved to the
  front (`SimpleGraph.influencedFirst`). If `S ≠ ∅` then `v*` is the `π`-first node of `S'` and
  `S = S'`.
* `theorem1_node_eq`: for an (effective) node insertion or deletion, `E_π |S| = 1` exactly
  (the paper only claims `≤ 1`).
-/

open Finset SimpleGraph
open scoped BigOperators

namespace DynamicMIS

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- **Lemma 2** (Censor-Hillel–Haramaty–Karnin). If `S ≠ ∅`, then `π(v*) = min π(S')` and
`S = S'`, where `S'` is computed with `v*` moved to the front of the order. -/
theorem lemma2 (c : Change V) (cfg : Config V) (π : V ≃ Fin (Fintype.card V))
    (h : infl c cfg (orderRank π) ≠ ∅) :
    (∀ u ∈ (c.baseGraph cfg).influencedFirst (c.baseNodes cfg) π (c.vStar (orderRank π)),
        π (c.vStar (orderRank π)) ≤ π u) ∧
      infl c cfg (orderRank π) =
        ↑((c.baseGraph cfg).influencedFirst (c.baseNodes cfg) π (c.vStar (orderRank π))) := by
  classical
  have hinv : ¬ InvariantAt (c.apply cfg).graph (c.apply cfg).nodes (orderRank π)
      (cfg.graph.greedyMIS cfg.nodes (orderRank π)) (c.vStar (orderRank π)) :=
    fun hi => h (infl_eq_empty hi)
  obtain ⟨h₁, h₂⟩ := infl_eq (orderRank_injective π) hinv
  refine ⟨(mem_greedyMIS_iff_first (greedyMIS_subset _ _ _ h₁)).1 h₁, ?_⟩
  rw [influencedFirst_eq_of_mem h₁, Set.coe_toFinset, h₂]

omit [Fintype V] in
/-- For an effective node change, the invariant breaks at `x` iff `x` is in the greedy MIS of the
graph containing `x`. -/
theorem not_invariant_node_iff {x : V} {c : Change V} {cfg : Config V} {r : V → ℕ}
    (hr : Function.Injective r)
    (hc : (c = .insertNode x ∧ x ∉ cfg.nodes) ∨ (c = .deleteNode x ∧ x ∈ cfg.nodes)) :
    ¬ InvariantAt (c.apply cfg).graph (c.apply cfg).nodes r
        (cfg.graph.greedyMIS cfg.nodes r) (c.vStar r) ↔
      x ∈ (c.baseGraph cfg).greedyMIS (c.baseNodes cfg) r := by
  have hv : c.vStar r = x := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> rfl
  constructor
  · intro h; have := (infl_eq hr h).1; rwa [hv] at this
  intro hx
  rcases hc with ⟨rfl, hxA⟩ | ⟨rfl, hxA⟩
  · -- insertion: `x` was out, and its rule now holds
    have hs : (Change.baseGraph (.insertNode x) cfg).IsGreedyExcept
        (Change.baseNodes (.insertNode x) cfg) r x (cfg.graph.greedyMIS cfg.nodes r) :=
      (flipData _ cfg hr).isGreedyExcept_old
    intro hi
    have hxs : x ∉ cfg.graph.greedyMIS cfg.nodes r :=
      fun h => hxA (greedyMIS_subset _ _ _ h)
    apply hxs
    refine hi.2 ⟨Set.mem_insert x _, fun w hw hrw hws => ?_⟩
    have := ((greedyMIS_iff _ _ _).1 hx).2 w hw hrw
    exact this ((mem_iff_mem_of_lt hs (isGreedyExcept_greedyMIS _ _ _ x) hrw).1 hws)
  · -- deletion: `x` was in, and must leave
    have hs : (Change.baseGraph (.deleteNode x) cfg).IsGreedyExcept
        (Change.baseNodes (.deleteNode x) cfg) r x (cfg.graph.greedyMIS cfg.nodes r) :=
      (flipData _ cfg hr).isGreedyExcept_old
    intro hi
    have hxs : x ∈ cfg.graph.greedyMIS cfg.nodes r := by
      rw [← (greedyRule_iff_mem_greedyMIS hs)] at hx
      rw [greedyMIS_iff]
      exact ⟨hxA, fun w hw hrw => hx.2 w hw hrw⟩
    exact (hi.1 hxs).1.2 rfl

/-- **Theorem 1, exact form for node changes.** For the insertion of a node `x ∉ A` or the
deletion of a node `x ∈ A`, `E_π |S| = 1`. -/
theorem theorem1_node_eq {x : V} (c : Change V) (cfg : Config V)
    (hc : (c = .insertNode x ∧ x ∉ cfg.nodes) ∨ (c = .deleteNode x ∧ x ∈ cfg.nodes)) :
    𝔼 π : V ≃ Fin (Fintype.card V), ((infl c cfg (orderRank π)).ncard : ℚ) = 1 := by
  classical
  have hv : ∀ r, c.vStar r = x := by rcases hc with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> intro r <;> rfl
  have hxA : x ∈ c.baseNodes cfg := by
    rcases hc with ⟨rfl, -⟩ | ⟨rfl, h⟩
    · exact Or.inr (Set.mem_insert x _)
    · exact Or.inl h
  have hsum : ∑ π : V ≃ Fin (Fintype.card V), (infl c cfg (orderRank π)).ncard =
      (Fintype.card V).factorial := by
    rw [← sum_card_influenced_eq (G := c.baseGraph cfg) hxA]
    refine Finset.sum_congr rfl fun π _ => ?_
    by_cases hx : x ∈ (c.baseGraph cfg).greedyMIS (c.baseNodes cfg) (orderRank π)
    · have hinv := (not_invariant_node_iff (orderRank_injective π) hc).2 hx
      rw [ite_eq_left hx, (infl_eq (orderRank_injective π) hinv).2, hv,
        Set.ncard_eq_toFinset_card']
    · have hinv : InvariantAt (c.apply cfg).graph (c.apply cfg).nodes (orderRank π)
          (cfg.graph.greedyMIS cfg.nodes (orderRank π)) (c.vStar (orderRank π)) :=
        by_contra fun h => hx ((not_invariant_node_iff (orderRank_injective π) hc).1 h)
      rw [ite_eq_right hx, infl_eq_empty hinv, Set.ncard_empty]
  rw [Fintype.expect_eq_sum_div_card, Fintype.card_equiv (Fintype.equivFin V)]
  rw [div_eq_one_iff_eq (by positivity)]
  exact_mod_cast hsum

end DynamicMIS
