import Cslib.Foundations.Combinatorics.SimpleGraph.ShortcutDilation
import Mathlib

/-!
# Definitions of [HIZ16]

[HIZ16] B. Haeupler, T. Izumi, G. Zuzic. *Low-Congestion Shortcuts without Embedding.* PODC 2016
(full version arXiv:1607.07553v3; numbering follows it).

Parts (`SimpleGraph.IsParts`), shortcuts (`ι → Finset (Sym2 V)`), rooted spanning trees
(`SimpleGraph.RootedTree`), `T`-restricted shortcuts (`RootedTree.Restricts`, Definition 4) and the
graph `G[P_i] + H_i` (`SimpleGraph.partGraph`) come from CSLib. Here:

* `blockParam P H` (Definition 5): the number of *block components* of a part `P` with shortcut
  edges `H`, i.e. the connected components of `(V, H)` that contain a vertex of `P`.
  (CSLib's `numBlocks` counts the components of `(P ∪ V(H), H)`, including those that miss `P`;
  the two agree under `BlocksMeetPart`, see `blockParam_eq_numBlocks`.)
* `PartCongestionLE` (Definition 2): every edge `e` lies in at most `c` of the sets
  `E_G[P_i] ∪ H_i`. This implies CSLib's `CongestionLE` (which only counts the `H_i`); all our
  hypotheses use the weaker `CongestionLE`.
* `climb_image_ncard_le_blockParam`, `blockParam_le_climb_image_ncard`: for a `T`-restricted `H`,
  block components are in bijection with their tops (the end of the climb along `H`).
-/

set_option linter.unusedSectionVars false

namespace ShortcutsNoEmbedding

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-- Definition 5 of [HIZ16]: the number of block components of part `P` with shortcut edges `H`:
connected components of `(V, H)` containing at least one vertex of `P`. -/
noncomputable def blockParam (P : Finset V) (H : Finset (Sym2 V)) : ℕ :=
  ((blockGraph H).connectedComponentMk '' (P : Set V)).ncard

/-- The edges of `G[P]`: both endpoints in `P`. -/
def InPart (P : Finset V) (e : Sym2 V) : Prop := ∀ v ∈ e, v ∈ P

variable (G) in
open Classical in
/-- Definition 2 of [HIZ16] (congestion): every edge of `G` lies in at most `c` of the sets
`E_G[P_i] ∪ H_i`. -/
def PartCongestionLE {ι : Type*} [Fintype ι] (P : ι → Finset V) (H : ι → Finset (Sym2 V))
    (c : ℕ) : Prop :=
  ∀ e ∈ G.edgeSet, (univ.filter fun i => InPart (P i) e ∨ e ∈ H i).card ≤ c

/-- Congestion in the sense of Definition 2 implies the (weaker) CSLib congestion, which only
counts the shortcut edges. -/
theorem PartCongestionLE.congestionLE [DecidableEq V] {ι : Type*} [Fintype ι] {P : ι → Finset V}
    {H : ι → Finset (Sym2 V)} {c : ℕ} (h : PartCongestionLE G P H c) :
    G.CongestionLE univ H c := by
  intro e he
  have := h e he
  have h2 : (univ.filter fun i => e ∈ H i).card ≤ c := by
    refine le_trans (card_le_card fun i hi => ?_) this
    simp only [mem_filter, mem_univ, true_and] at hi ⊢
    exact Or.inr hi
  exact_mod_cast h2

/-- Under `BlocksMeetPart`, Definition 5 agrees with CSLib's `numBlocks`. -/
theorem blockParam_eq_numBlocks {P : Finset V} {H : Finset (Sym2 V)} (h : BlocksMeetPart P H) :
    blockParam P H = numBlocks P H := by
  unfold blockParam numBlocks
  congr 1
  apply Set.Subset.antisymm
  · exact Set.image_mono Set.subset_union_left
  · rintro _ ⟨z, hz, rfl⟩
    obtain ⟨y, hy, hzy⟩ := h z hz
    exact ⟨y, hy, (ConnectedComponent.eq.2 hzy).symm⟩

/-- A part with at least one vertex has at least one block component. -/
theorem one_le_blockParam {P : Finset V} (hP : P.Nonempty) (H : Finset (Sym2 V)) :
    1 ≤ blockParam P H := by
  obtain ⟨v, hv⟩ := hP
  unfold blockParam
  rw [Nat.one_le_iff_ne_zero, Ne, Set.ncard_eq_zero (Set.toFinite _)]
  exact Set.Nonempty.ne_empty ⟨_, v, hv, rfl⟩

namespace RootedTreeBlocks

variable [DecidableEq V] {T : G.RootedTree}

/-- Every block component of `H` is represented by its top: `x` and `climb H x` lie in the same
component. Hence there are at most as many block components as tops. -/
theorem blockParam_le_climb_image_ncard (P : Finset V) (H : Finset (Sym2 V)) :
    blockParam P H ≤ (T.climb H '' (P : Set V)).ncard := by
  unfold blockParam
  have : (blockGraph H).connectedComponentMk '' (P : Set V) =
      (blockGraph H).connectedComponentMk '' (T.climb H '' (P : Set V)) := by
    rw [Set.image_image]
    exact Set.image_congr fun x _ => ConnectedComponent.sound (RootedTree.reachable_climb H x)
  rw [this]
  exact Set.ncard_image_le (Set.toFinite _)

/-- For a `T`-restricted `H`, the top of a block component does not depend on the vertex of the
component we climb from, so there are at most as many tops as block components. -/
theorem climb_image_ncard_le_blockParam {P : Finset V} {H : Finset (Sym2 V)}
    (hH : T.Restricts H) : (T.climb H '' (P : Set V)).ncard ≤ blockParam P H := by
  unfold blockParam
  have : T.climb H '' (P : Set V) ⊆
      (fun C : (blockGraph H).ConnectedComponent => T.climb H C.out) ''
        ((blockGraph H).connectedComponentMk '' (P : Set V)) := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨_, ⟨x, hx, rfl⟩, ?_⟩
    apply RootedTree.climb_eq_of_reachable hH
    exact ConnectedComponent.exact (Quot.out_eq _)
  exact (Set.ncard_le_ncard this (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))

end RootedTreeBlocks

end ShortcutsNoEmbedding
