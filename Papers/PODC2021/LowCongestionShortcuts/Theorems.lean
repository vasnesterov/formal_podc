import Papers.PODC2021.LowCongestionShortcuts.Main
import Papers.PODC2021.LowCongestionShortcuts.Observations
import Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree
import Mathlib

/-!
# Main results of [GH21]

[GH21] M. Ghaffari, B. Haeupler. *Low-Congestion Shortcuts for Graphs Excluding Dense Minors.*
PODC 2021 (arXiv:2008.03091).

* `theorem_3_1`: every graph with minor density `≤ δ` admits, for trees of depth `≤ D`,
  tree-restricted `8δD`-congestion `(8δ + 1)`-block partial shortcuts (paper: `8δ` blocks).
* `theorem_3_1_minorDensity`: the same with `δ = δ(G)`.
* `theorem_1_2`: every connected `n`-vertex graph with diameter `≤ D` admits, for every collection
  of parts, a (tree-restricted) shortcut with congestion `8δD (⌊log₂ n⌋ + 1)` and dilation
  `(8δ + 1)(2D + 1)` (paper: `O(δ D log n)` and `O(δ D)`, via `8δD log₂ n` and `8δ(2D+1)`).
-/

set_option linter.unusedSectionVars false

namespace LowCongestionShortcuts

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- **Theorem 3.1 of [GH21]**, with block number `8δ + 1` instead of `8δ`: a graph whose minors
all have edge density `≤ δ` admits tree-restricted `8δD`-congestion `(8δ + 1)`-block partial
shortcuts with respect to every rooted spanning tree of depth `≤ D`. -/
theorem theorem_3_1 {δ : ℝ} (hδ : G.MinorDensityLE δ) (D : ℕ) :
    G.AdmitsPartialTreeShortcuts D (8 * δ * D) (8 * δ + 1) := by
  intro T hT ι _ _ P hP
  classical
  obtain ⟨O, hO⟩ := exists_stable T P (8 * δ * D) hT
  refine ⟨univ.filter fun i => ((O.filter fun v => i ∈ parts T P O v).card : ℝ) ≤ 8 * δ, ?_,
    shortcut T P O, fun i _ => restricts_shortcut P O i, ?_, fun i hi => ⟨?_,
      blocksMeetPart_shortcut P O i⟩⟩
  · -- case (I) holds, since case (II) is impossible
    by_contra h
    exact caseII_false hδ hP hT hO (by push Not at h; exact h)
  · intro e he
    have hc : 0 ≤ 8 * δ * D := by
      induction e using Sym2.ind with
      | h a b => have := hδ.half_le (G.mem_edgeSet.1 he); positivity
    refine card_filter_mem_shortcut_le _ hc (fun v hv hvO => ?_) e
    by_contra h'
    exact hvO ((hO v).2 ⟨hv, le_of_not_gt h'⟩)
  · have h1 := numBlocks_shortcut_le (T := T) P O i
    have h2 := (mem_filter.1 hi).2
    have : (numBlocks (P i) (shortcut T P O i) : ℝ) ≤
        1 + ((O.filter fun v => i ∈ parts T P O v).card : ℝ) := by exact_mod_cast h1
    linarith

/-- **Theorem 3.1 of [GH21]** with `δ = δ(G)` the minor density of `G` (block number
`8δ(G) + 1`). -/
theorem theorem_3_1_minorDensity (D : ℕ) :
    G.AdmitsPartialTreeShortcuts D (8 * G.minorDensity * D) (8 * G.minorDensity + 1) :=
  theorem_3_1 minorDensityLE_minorDensity D

/-- **Theorem 1.2 of [GH21]** (explicit form, for any `δ ≥ δ(G)`): a connected `n`-vertex graph `G`
in which all distances are at most `D` admits, for every collection of parts, a shortcut (even a
tree-restricted one) with congestion `8δD (⌊log₂ n⌋ + 1)` and dilation `(8δ + 1)(2D + 1)`. -/
theorem theorem_1_2_of_minorDensityLE {δ : ℝ} (hδ : G.MinorDensityLE δ) (hG : G.Connected)
    {D : ℕ} (hD : ∀ u v, G.dist u v ≤ D) {ι : Type} [Fintype ι] [DecidableEq ι]
    (P : ι → Finset V) (hP : G.IsParts P) :
    ∃ H : ι → Finset (Sym2 V), (∀ i, ∀ e ∈ H i, e ∈ G.edgeSet) ∧
      G.CongestionLE univ H (8 * δ * D * (Nat.log 2 (Fintype.card V) + 1)) ∧
      ∀ i, G.DilationLE (P i) (H i) ((8 * δ + 1) * (2 * D + 1)) := by
  have : Nonempty V := hG.nonempty
  have hδ0 : 0 ≤ δ := hδ.nonneg
  obtain ⟨T, hT⟩ := exists_rootedTree_depthLE hG hD
  obtain ⟨H, hres, hcong, hblk⟩ :=
    observation_2_7 (theorem_3_1 hδ D) (by positivity) T hT P hP
  refine ⟨H, fun i e he => RootedTree.edge_mem_graph_edgeSet (hres i e he), hcong, fun i => ?_⟩
  exact observation_2_6 T hT (P i) (hP.connected i) (H i) (hres i) (hblk i).2 (hblk i).1

/-- **Theorem 1.2 of [GH21]**: any `n`-node graph `G` with diameter `≤ D` and minor density
`δ = δ(G)` admits shortcuts with congestion `8δD(⌊log₂ n⌋ + 1) = O(δ D log n)` and dilation
`(8δ + 1)(2D + 1) = O(δ D)`. -/
theorem theorem_1_2 (hG : G.Connected) {D : ℕ} (hD : ∀ u v, G.dist u v ≤ D) {ι : Type}
    [Fintype ι] [DecidableEq ι] (P : ι → Finset V) (hP : G.IsParts P) :
    ∃ H : ι → Finset (Sym2 V), (∀ i, ∀ e ∈ H i, e ∈ G.edgeSet) ∧
      G.CongestionLE univ H (8 * G.minorDensity * D * (Nat.log 2 (Fintype.card V) + 1)) ∧
      ∀ i, G.DilationLE (P i) (H i) ((8 * G.minorDensity + 1) * (2 * D + 1)) :=
  theorem_1_2_of_minorDensityLE minorDensityLE_minorDensity hG hD P hP

end LowCongestionShortcuts
