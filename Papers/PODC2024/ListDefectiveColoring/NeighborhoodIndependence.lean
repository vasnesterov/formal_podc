import Mathlib

/-!
# Neighbourhood independence and arbdefective colourings (Claim 4.1 of [FK24])

Fuchs, Kuhn. *Simpler and More General Distributed Coloring Based on Simple List Defective
Coloring Algorithms* (PODC 2024; arXiv:2405.04648), cited as [FK24].

* `SimpleGraph.NeighborhoodIndepLE G θ`: the neighbourhood independence of `G` is at most `θ`,
  i.e. every independent set contained in a neighbourhood `N(v)` has at most `θ` elements.
* `SimpleGraph.exists_isIndepSet_card_le_mul` (graph-theoretic core): if all edges inside a finite
  vertex set `W` are oriented and every vertex of `W` has at most `d` out-neighbours in `W`, then
  `W` contains an independent set `I` with `|W| ≤ (2d+1)·|I|` (greedy: a vertex of degree `≤ 2d`
  in `G[W]` exists by double counting; take it, delete its closed neighbourhood, recurse).
* `SimpleGraph.card_le_of_subset_neighborSet`: consequently a set `W ⊆ N(v)` with such an
  orientation has at most `(2d+1)·θ` elements.
* `FK24.claim_4_1` (Claim 4.1): in a `d`-arbdefective colouring of a graph with neighbourhood
  independence `≤ θ`, every node has at most `(2d+1)·θ` neighbours of its own colour.
-/

open Finset

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The neighbourhood independence of `G` is at most `θ`: every independent set of `G` that is
contained in the neighbourhood of a single node has at most `θ` elements. -/
def NeighborhoodIndepLE (θ : ℕ) : Prop :=
  ∀ (v : V) (I : Finset V), (I : Set V) ⊆ G.neighborSet v → G.IsIndepSet (I : Set V) → #I ≤ θ

variable {G}

-- CSLib candidate
open Classical in
/-- Graph-theoretic core of Claim 4.1 of [FK24]: if every edge of `G` between two vertices of the
finite set `W` is oriented by `O` (in at least one direction) and every vertex of `W` has at most
`d` out-neighbours inside `W`, then `W` contains an independent set `I` with
`|W| ≤ (2d + 1) · |I|`. -/
theorem exists_isIndepSet_card_le_mul (W : Finset V) (O : V → V → Prop) (d : ℕ)
    (horient : ∀ u ∈ W, ∀ w ∈ W, G.Adj u w → O u w ∨ O w u)
    (hout : ∀ u ∈ W, #{w ∈ W | G.Adj u w ∧ O u w} ≤ d) :
    ∃ I ⊆ W, G.IsIndepSet (I : Set V) ∧ #W ≤ (2 * d + 1) * #I := by
  induction W using Finset.strongInduction with
  | H W ih =>
  rcases W.eq_empty_or_nonempty with rfl | hne
  · exact ⟨∅, empty_subset _, by simp, by simp⟩
  -- the sum of the degrees inside `W` is at most `2 d |W|`
  have hsum : ∑ u ∈ W, #{w ∈ W | G.Adj u w} ≤ ∑ _u ∈ W, 2 * d := by
    calc ∑ u ∈ W, #{w ∈ W | G.Adj u w}
        ≤ ∑ u ∈ W, (#{w ∈ W | G.Adj u w ∧ O u w} + #{w ∈ W | G.Adj u w ∧ O w u}) := by
          refine sum_le_sum fun u hu => (card_le_card ?_).trans (card_union_le _ _)
          intro w hw
          simp only [mem_filter, mem_union] at hw ⊢
          rcases horient u hu w hw.1 hw.2 with h | h <;> tauto
      _ = ∑ u ∈ W, #{w ∈ W | G.Adj u w ∧ O u w} + ∑ u ∈ W, #{w ∈ W | G.Adj u w ∧ O w u} :=
          sum_add_distrib
      _ = ∑ u ∈ W, #{w ∈ W | G.Adj u w ∧ O u w} + ∑ w ∈ W, #{u ∈ W | G.Adj w u ∧ O w u} := by
          congr 1
          have := sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s := W) (t := W)
            (r := fun u w => G.Adj u w ∧ O w u)
          simp only [bipartiteAbove, bipartiteBelow] at this
          rw [this]
          refine sum_congr rfl fun w _ => ?_
          congr 1
          ext u
          simp [G.adj_comm]
      _ ≤ ∑ _u ∈ W, d + ∑ _u ∈ W, d := add_le_add (sum_le_sum hout) (sum_le_sum hout)
      _ = ∑ _u ∈ W, 2 * d := by rw [← sum_add_distrib]; congr 1; ext; ring
  obtain ⟨u, hu, hdeg⟩ := exists_le_of_sum_le hne hsum
  -- delete `u` and its neighbours
  set W' := {w ∈ W | w ≠ u ∧ ¬ G.Adj u w} with hW'def
  have hW'sub : W' ⊆ W := filter_subset _ _
  have hW' : W' ⊂ W := by
    refine Finset.ssubset_iff_subset_ne.2 ⟨hW'sub, fun h => ?_⟩
    have : u ∈ W' := h ▸ hu
    simp [W'] at this
  obtain ⟨I', hI'W', hI', hcard⟩ := ih W' hW'
    (fun a ha b hb hab => horient a (hW'sub ha) b (hW'sub hb) hab)
    (fun a ha => (card_le_card (filter_subset_filter _ hW'sub)).trans (hout a (hW'sub ha)))
  have huI' : u ∉ I' := fun h => by simpa [W'] using hI'W' h
  refine ⟨insert u I', insert_subset hu (hI'W'.trans hW'sub), ?_, ?_⟩
  · rw [coe_insert]
    refine hI'.insert fun b hb _ => ?_
    have hbW' := hI'W' hb
    simp only [W', mem_filter] at hbW'
    exact ⟨hbW'.2.2, fun h => hbW'.2.2 (G.adj_symm h)⟩
  · have hcov : W ⊆ insert u ({w ∈ W | G.Adj u w} ∪ W') := by
      intro w hw
      by_cases hwu : w = u
      · simp [hwu]
      by_cases hadj : G.Adj u w
      · simp [hw, hadj]
      · simp [W', hw, hwu, hadj]
    have h1 := card_le_card hcov
    have h2 := card_insert_le u ({w ∈ W | G.Adj u w} ∪ W')
    have h3 := card_union_le {w ∈ W | G.Adj u w} W'
    rw [card_insert_of_notMem huI']
    nlinarith

open Classical in
/-- A set `W` contained in the neighbourhood of a node `v` whose internal edges are oriented with
out-degrees at most `d` has at most `(2d + 1) · θ` elements, if the neighbourhood independence of
`G` is at most `θ` (the argument of Claim 4.1 of [FK24]). -/
theorem card_le_of_subset_neighborSet {θ : ℕ} (hθ : G.NeighborhoodIndepLE θ) {v : V}
    {W : Finset V} (hW : (W : Set V) ⊆ G.neighborSet v) (O : V → V → Prop) (d : ℕ)
    (horient : ∀ u ∈ W, ∀ w ∈ W, G.Adj u w → O u w ∨ O w u)
    (hout : ∀ u ∈ W, #{w ∈ W | G.Adj u w ∧ O u w} ≤ d) :
    #W ≤ (2 * d + 1) * θ := by
  obtain ⟨I, hIW, hI, hcard⟩ := exists_isIndepSet_card_le_mul W O d horient hout
  have : #I ≤ θ := hθ v I (fun x hx => hW (hIW hx)) hI
  exact hcard.trans (Nat.mul_le_mul_left _ this)

end SimpleGraph

namespace FK24

open SimpleGraph

variable {V α : Type*} {G : SimpleGraph V} [G.LocallyFinite]

open Classical in
/-- Claim 4.1 of [FK24]. Let `G` have neighbourhood independence at most `θ` and let `(col, O)` be
a `d`-arbdefective colouring: every monochromatic edge is oriented by `O` and every node has at
most `d` out-neighbours of its own colour. Then every node has at most `(2d + 1) · θ` neighbours
of its own colour, i.e. `col` is a `(2d + 1) · θ`-defective colouring. -/
theorem claim_4_1 {θ d : ℕ} (hθ : G.NeighborhoodIndepLE θ) {col : V → α} {O : V → V → Prop}
    (horient : ∀ ⦃u w⦄, G.Adj u w → col u = col w → O u w ∨ O w u)
    (hout : ∀ u, #{w ∈ G.neighborFinset u | O u w ∧ col w = col u} ≤ d) (v : V) :
    #{u ∈ G.neighborFinset v | col u = col v} ≤ (2 * d + 1) * θ := by
  refine card_le_of_subset_neighborSet hθ (v := v) ?_ O d ?_ ?_
  · intro u hu
    simp only [coe_filter, Set.mem_ofPred_eq, mem_neighborFinset] at hu
    exact hu.1
  · intro u hu w hw huw
    simp only [mem_filter] at hu hw
    exact horient huw (hu.2.trans hw.2.symm)
  · intro u hu
    refine le_trans (card_le_card ?_) (hout u)
    intro w hw
    simp only [mem_filter, mem_neighborFinset] at hu hw ⊢
    exact ⟨hw.2.1, hw.2.2, hw.1.2.trans hu.2.symm⟩

end FK24
