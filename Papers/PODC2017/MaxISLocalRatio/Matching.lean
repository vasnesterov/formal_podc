import Papers.PODC2017.MaxISLocalRatio.Distributed

/-!
# 2-approximate maximum-weight matching via the line graph (Section 2.4, Theorem 2.10)

A matching of `G` is an independent set of the line graph `L(G)` (Mathlib's `G.lineGraph`, whose
vertices are the edges of `G`). The key observation of Section 2.4: in `L(G)` every independent set
(matching) meets the closed neighbourhood of an edge `e = {a, b}` in at most `2` edges (at most one
matching edge contains `a`, at most one contains `b`). Hence Lemma 2.2 holds with `r = 2` instead of
`Δ(L(G))`, and Algorithm 1, run on `L(G)` with edge weights, returns a 2-approximate maximum-weight
matching for **every** choice rule.

* `matching_localBound` — the local bound `2` in `L(G)`.
* `seqLR_lineGraph_isApprox` — Algorithm 1 on `L(G)` is a 2-approximation for max-weight matching.
* `theorem_2_10_det` — deterministic half of Theorem 2.10, at the level of the line graph: Algorithm 3
  run on `L(G)` with a black-box proper colouring of `L(G)` with `k` colours (an edge colouring of
  `G`) terminates after `3k` rounds of `L(G)` and outputs a 2-approximate maximum-weight matching.
  `lineGraph_degree_le`: `L(G)` has maximum degree `≤ 2Δ - 2`, so `k = 2Δ - 1` colours suffice
  (as in the paper).

Not formalized: the simulation of `L(G)`-rounds by `G`-rounds (in LOCAL each `L(G)`-round costs `O(1)`
rounds of `G`; in CONGEST the paper's Theorem 2.8 on "local aggregation algorithms" is only
sketched), see `differencies.md`.
-/

set_option linter.unusedSectionVars false

namespace Podc.MaxISLocalRatio

open Finset Cslib.LocallyIterative

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A set of edges of `G` is a matching: distinct edges share no vertex. -/
def IsMatchingSet (M : Finset G.edgeSet) : Prop :=
  ∀ e ∈ M, ∀ f ∈ M, e ≠ f → ∀ v, v ∈ (e : Sym2 V) → v ∉ (f : Sym2 V)

variable {G}

-- CSLib candidate
/-- Matchings are exactly the independent sets of the line graph. -/
theorem isMatchingSet_iff_isIndepSet (M : Finset G.edgeSet) :
    IsMatchingSet G M ↔ G.lineGraph.IsIndepSet (M : Set G.edgeSet) := by
  constructor
  · intro h e he f hf hef hadj
    obtain ⟨-, v, hve, hvf⟩ := SimpleGraph.lineGraph_adj_iff_exists.1 hadj
    exact h e he f hf hef v hve hvf
  · intro h e he f hf hef v hve hvf
    exact h he hf hef (SimpleGraph.lineGraph_adj_iff_exists.2 ⟨hef, v, hve, hvf⟩)

-- CSLib candidate
/-- In a matching at most one edge contains a given vertex. -/
theorem card_filter_mem_le_one {T : Finset G.edgeSet} (hT : G.lineGraph.IsIndepSet (T : Set G.edgeSet))
    (a : V) : #(T.filter fun f : G.edgeSet => a ∈ f.1) ≤ 1 := by
  refine card_le_one.2 fun f hf f' hf' => ?_
  obtain ⟨hfT, haf⟩ := mem_filter.1 hf
  obtain ⟨hf'T, haf'⟩ := mem_filter.1 hf'
  by_contra hne
  exact hT hfT hf'T hne (SimpleGraph.lineGraph_adj_iff_exists.2 ⟨hne, a, haf, haf'⟩)

-- CSLib candidate
open scoped Classical in
/-- **Section 2.4, key bound.** Every matching meets the closed neighbourhood of an edge
`e = {a, b}` in `L(G)` in at most `2` edges. -/
theorem matching_localBound (U : Finset G.edgeSet) : LocalBound G.lineGraph U 2 := by
  rintro ⟨z, hz⟩ _ T hT
  revert hz
  refine Sym2.ind (fun a b hz _ => ?_) z
  -- every edge of `T ∩ N[e]` contains `a` or `b`
  have hsub : T ∩ cl G.lineGraph ⟨s(a, b), hz⟩ ⊆ T.filter (fun f : G.edgeSet => a ∈ f.1) ∪
      T.filter (fun f : G.edgeSet => b ∈ f.1) := by
    intro f hf
    obtain ⟨hfT, hfe⟩ := mem_inter.1 hf
    rcases mem_cl.1 hfe with rfl | hadj
    · exact mem_union_left _ (mem_filter.2 ⟨hfT, Sym2.mem_mk_left a b⟩)
    · obtain ⟨-, v, hv, hvf⟩ := SimpleGraph.lineGraph_adj_iff_exists.1 hadj
      rcases Sym2.mem_iff.1 hv with rfl | rfl
      · exact mem_union_left _ (mem_filter.2 ⟨hfT, hvf⟩)
      · exact mem_union_right _ (mem_filter.2 ⟨hfT, hvf⟩)
  have := (card_le_card hsub).trans (card_union_le _ _)
  have := card_filter_mem_le_one hT a
  have := card_filter_mem_le_one hT b
  have : #(T ∩ cl G.lineGraph ⟨s(a, b), hz⟩) ≤ 2 := by omega
  exact_mod_cast this

open scoped Classical in
/-- **Section 2.4.** Algorithm 1 run on the line graph with edge weights returns, for every
admissible choice rule, a matching `M` with `w(M*) ≤ 2 w(M)` for every matching `M*`. -/
theorem seqLR_lineGraph_isApprox (R : Rule G.lineGraph) (w : G.edgeSet → ℝ) :
    IsMatchingSet G (seqLR R w) ∧
      ∀ M : Finset G.edgeSet, IsMatchingSet G M → wt w M ≤ 2 * wt w (seqLR R w) := by
  have h := seqLR_isApprox R (r := 2) (by norm_num) (fun _ => matching_localBound _) w
  refine ⟨(isMatchingSet_iff_isIndepSet _).2 h.1, fun M hM => ?_⟩
  exact h.2 M ((isMatchingSet_iff_isIndepSet _).1 hM)

open scoped Classical in
/-- **Theorem 2.10, deterministic half (at the level of the line graph).** Run Algorithm 3 on
`L(G)` with edge weights `w` and a black-box proper colouring `c` of `L(G)` with `k` colours (e.g.
`k = 2Δ - 1`, see `lineGraph_degree_le`). After `3k` rounds (of `L(G)`) every edge has an output,
outputs are final and correct when produced, and the edges that output `InIS` form a matching `M`
with `w(M*) ≤ 2 w(M)` for every matching `M*`. -/
theorem theorem_2_10_det {c : G.edgeSet → ℕ} (hc : IsProper G.lineGraph c) {k : ℕ}
    (hk : ∀ e, c e < k) (w : G.edgeSet → ℝ) :
    ∃ M : Finset G.edgeSet, IsMatchingSet G M ∧
      (∀ M' : Finset G.edgeSet, IsMatchingSet G M' → wt w M' ≤ 2 * wt w M) ∧
      (∀ t, 3 * k ≤ t → ∀ e, output (cfg3 G.lineGraph c w t e) = some (decide (e ∈ M))) ∧
      (∀ t e b, output (cfg3 G.lineGraph c w t e) = some b → (b = true ↔ e ∈ M)) := by
  obtain ⟨h1, h2⟩ := seqLR_lineGraph_isApprox (colorRule G.lineGraph c hc) w
  exact ⟨_, h1, h2, fun _ ht e => output_eq hc hk w ht e, fun _ _ _ h => output_sound hc w h⟩

-- CSLib candidate
open scoped Classical in
/-- The line graph of a graph with maximum degree `≤ Δ` has maximum degree `≤ 2Δ - 2`; hence a
`(2Δ-1)`-colouring of `L(G)` (an edge colouring of `G`) is a `(Δ(L(G))+1)`-colouring. -/
theorem lineGraph_degree_le {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ) (e : G.edgeSet) :
    G.lineGraph.degree e ≤ 2 * Δ - 2 := by
  obtain ⟨z, hz⟩ := e
  revert hz
  refine Sym2.ind (fun a b hz => ?_) z
  rw [← SimpleGraph.card_neighborFinset_eq_degree]
  have hsub : (G.lineGraph.neighborFinset ⟨s(a, b), hz⟩).map (Function.Embedding.subtype _) ⊆
      ((G.incidenceFinset a).erase s(a, b)) ∪ ((G.incidenceFinset b).erase s(a, b)) := by
    intro f hf
    obtain ⟨f, hf', rfl⟩ := mem_map.1 hf
    rw [SimpleGraph.mem_neighborFinset] at hf'
    obtain ⟨hne, v, hv, hvf⟩ := SimpleGraph.lineGraph_adj_iff_exists.1 hf'
    have hne' : (f : Sym2 V) ≠ s(a, b) := fun h => hne (Subtype.ext h.symm)
    rcases Sym2.mem_iff.1 hv with rfl | rfl
    · exact mem_union_left _ (mem_erase.2 ⟨hne',
        G.mem_incidenceFinset.2 ⟨f.2, hvf⟩⟩)
    · exact mem_union_right _ (mem_erase.2 ⟨hne',
        G.mem_incidenceFinset.2 ⟨f.2, hvf⟩⟩)
  have h1 := (card_le_card hsub).trans (card_union_le _ _)
  rw [card_map] at h1
  have hza : s(a, b) ∈ G.incidenceFinset a := G.mem_incidenceFinset.2 ⟨hz, Sym2.mem_mk_left a b⟩
  have hzb : s(a, b) ∈ G.incidenceFinset b := G.mem_incidenceFinset.2 ⟨hz, Sym2.mem_mk_right a b⟩
  rw [card_erase_of_mem hza, card_erase_of_mem hzb, G.card_incidenceFinset_eq_degree,
    G.card_incidenceFinset_eq_degree] at h1
  have := hΔ a
  have := hΔ b
  have : 0 < G.degree a := (G.card_incidenceFinset_eq_degree a) ▸ card_pos.2 ⟨_, hza⟩
  have : 0 < G.degree b := (G.card_incidenceFinset_eq_degree b) ▸ card_pos.2 ⟨_, hzb⟩
  omega

end Podc.MaxISLocalRatio
