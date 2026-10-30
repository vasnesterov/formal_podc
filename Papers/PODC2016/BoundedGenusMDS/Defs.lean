import Cslib.Foundations.Combinatorics.SimpleGraph.Ball
import Podc.Foundations.Combinatorics.SimpleGraph.Depth1Minor
import Mathlib

/-!
# The modified Lenzen–Pignolet–Wattenhofer algorithm

Definitions for Amiri, Schmid, Siebertz, *A local constant factor MDS approximation for bounded
genus graphs* (PODC 2016, arXiv:1602.02991v2).

Depth-1 minors (`SimpleGraph.Depth1Model`, `IsDepth1Minor`, `Depth1DensityLE G c` = "all depth-1
minors have edge density `≤ c`", `ExcludesKt3 G t`) and their counting tools are staged in
`Podc/Foundations/Combinatorics/SimpleGraph/Depth1Minor.lean`.

* The algorithm: `phase1` (the set `D`), the residual degree `resDeg`, dominator functions
  `IsDominator` ("choose any `dom(v) ∈ N[v]` of maximal residual degree"), and `output`.
* `IsApprox G f S`: `S` is a dominating set of size `≤ f · |M|` for every dominating set `M`.
* `output_isDominatingSet`: the output dominates `G`.
-/

open Finset

namespace Podc.BoundedGenusMDS

open SimpleGraph (Depth1Model IsDepth1Minor Depth1DensityLE ExcludesKt3 depth1_of_cover_two)

open Classical

variable {V : Type}

section Algorithm

variable [Fintype V] (G : SimpleGraph V)

/-- Open neighbourhood `N(v)` as a finset. -/
noncomputable def nbhd (v : V) : Finset V := univ.filter (G.Adj v)

/-- Closed neighbourhood `N[A]` of a vertex set. -/
noncomputable def cnbhd (A : Finset V) : Finset V :=
  univ.filter fun x => ∃ a ∈ A, x = a ∨ G.Adj a x

/-- Phase 1 of the modified algorithm (Algorithm 1 with `|A| ≤ 2c` in line 5): the set `D` of
vertices `v` whose open neighbourhood cannot be covered by at most `2c` closed neighbourhoods of
vertices other than `v`. -/
noncomputable def phase1 (c : ℕ) : Finset V :=
  univ.filter fun v => ¬ ∃ A : Finset V, v ∉ A ∧ A.card ≤ 2 * c ∧ nbhd G v ⊆ cnbhd G A

/-- Residual degree `d_{V-D}(w) = |N[w] \ N[D]|` (line 12 of Algorithm 1). -/
noncomputable def resDeg (D : Finset V) (w : V) : ℕ := (cnbhd G {w} \ cnbhd G D).card

/-- `dom` is a valid dominator function for Phase 2 (lines 13–15 of Algorithm 1): every vertex `v`
not dominated by `D` picks some `dom v ∈ N[v]` of maximal residual degree in `N[v]`
("choose any"; ties are broken arbitrarily). -/
def IsDominator (D : Finset V) (dom : V → V) : Prop :=
  ∀ v, v ∉ cnbhd G D →
    dom v ∈ cnbhd G {v} ∧ ∀ w ∈ cnbhd G {v}, resDeg G D w ≤ resDeg G D (dom v)

/-- Output `D ∪ D'` of the modified Algorithm 1, where `D' = dom(V \ N[D])`. -/
noncomputable def output (c : ℕ) (dom : V → V) : Finset V :=
  phase1 G c ∪ (univ \ cnbhd G (phase1 G c)).image dom

/-- `S` is an `f`-approximation of a minimum dominating set: `S` dominates `G` and
`|S| ≤ f · |M|` for every dominating set `M` (equivalently, `|S| ≤ f · γ(G)`). -/
def IsApprox (f : ℕ) (S : Finset V) : Prop :=
  G.IsDominatingSet (S : Set V) ∧ ∀ M : Finset V, G.IsDominatingSet (M : Set V) → S.card ≤ f * M.card

variable {G}

@[simp] lemma mem_nbhd {v x : V} : x ∈ nbhd G v ↔ G.Adj v x := by simp [nbhd]

lemma mem_cnbhd {A : Finset V} {x : V} : x ∈ cnbhd G A ↔ ∃ a ∈ A, x = a ∨ G.Adj a x := by
  simp [cnbhd]

@[simp] lemma mem_cnbhd_singleton {v x : V} : x ∈ cnbhd G {v} ↔ x = v ∨ G.Adj v x := by
  simp [cnbhd]

lemma mem_phase1 {c : ℕ} {v : V} :
    v ∈ phase1 G c ↔ ¬ ∃ A : Finset V, v ∉ A ∧ A.card ≤ 2 * c ∧ nbhd G v ⊆ cnbhd G A := by
  simp [phase1]

lemma card_nbhd (v : V) : (nbhd G v).card + 1 = (cnbhd G {v}).card := by
  have : cnbhd G {v} = insert v (nbhd G v) := by
    ext x; simp [eq_comm]
  rw [this, card_insert_of_notMem (by simp)]

/-- The output of the algorithm dominates `G` (Section 3, "This simple observation proves that the
algorithm correctly computes a dominating set"). -/
theorem output_isDominatingSet {c : ℕ} {dom : V → V} (hdom : IsDominator G (phase1 G c) dom) :
    G.IsDominatingSet (output G c dom : Set V) := by
  intro v
  by_cases hv : v ∈ cnbhd G (phase1 G c)
  · obtain ⟨a, ha, h⟩ := mem_cnbhd.1 hv
    rcases h with rfl | h
    · left; simp [output, ha]
    · right; exact ⟨a, by simp [output, ha], h.symm⟩
  · have hd := (hdom v hv).1
    have hmem : dom v ∈ (output G c dom : Set V) := by
      simp only [output, coe_union, coe_image, Set.mem_union, Set.mem_image]
      right; exact ⟨v, by simpa using hv, rfl⟩
    rcases mem_cnbhd_singleton.1 hd with h | h
    · left; rwa [← h]
    · right; exact ⟨dom v, hmem, h⟩

end Algorithm


end Podc.BoundedGenusMDS
