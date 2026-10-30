import Mathlib
import Papers.PODC2017.LCLGrids.TorusGraph

/-!
# No edge `2d`-colouring of an odd torus (Theorem 21)

Theorem 21 of Brandt et al., *LCL Problems on Grids* (PODC 2017): for odd `n`, the
`d`-dimensional torus `(ℤ/n)^d` has no proper edge colouring with `2d` colours.

An edge colouring is a vertex colouring of the line graph (`SimpleGraph.lineGraph`).

## Proof

Every vertex has degree `2d`, so in a proper edge `2d`-colouring every vertex sees every colour
exactly once: each colour class is a perfect matching. By the handshake lemma the number of
vertices `n ^ d` is then twice the number of edges of colour `0`, which is impossible for odd `n`.

The general counting step is `even_card_of_lineGraph_coloring`: a `k`-regular finite graph
(`k ≥ 1`) whose edges are properly `k`-coloured has an even number of vertices.
-/

namespace Podc.LCLGrids

open Finset SimpleGraph

section General

variable {V : Type*} {G : SimpleGraph V} {α : Type*}

/-- The spanning subgraph of the edges of colour `c` under an edge colouring `C` of `G`. -/
def colourClass (C : G.lineGraph.Coloring α) (c : α) : SimpleGraph V where
  Adj v w := ∃ h : G.Adj v w, C ⟨s(v, w), h⟩ = c
  symm := ⟨fun v w ⟨h, hc⟩ => ⟨h.symm, by
    have e : (⟨s(w, v), h.symm⟩ : G.edgeSet) = ⟨s(v, w), h⟩ := Subtype.ext Sym2.eq_swap
    rw [e]; exact hc⟩⟩
  loopless := ⟨fun v ⟨h, _⟩ => G.loopless.irrefl v h⟩

/-- In a proper edge colouring, the edges at a vertex `v` get pairwise distinct colours. -/
lemma coloring_injective_at (C : G.lineGraph.Coloring α) {v u u' : V} (hu : G.Adj v u)
    (hu' : G.Adj v u') (h : C ⟨s(v, u), hu⟩ = C ⟨s(v, u'), hu'⟩) : u = u' := by
  by_contra hne
  refine C.valid ?_ h
  rw [lineGraph_adj_iff_exists]
  refine ⟨fun e => hne ?_, v, Sym2.mem_mk_left _ _, Sym2.mem_mk_left _ _⟩
  exact Sym2.congr_right.1 (congrArg Subtype.val e)

variable [Fintype V] [DecidableRel G.Adj] {k : ℕ}

/-- In a proper edge `k`-colouring of a `k`-regular graph, every vertex has exactly one incident
edge of each colour. -/
lemma existsUnique_colourClass_adj (hG : G.IsRegularOfDegree k) (C : G.lineGraph.Coloring (Fin k))
    (c : Fin k) (v : V) : ∃! u, (colourClass C c).Adj v u := by
  classical
  let f : ∀ u ∈ G.neighborFinset v, Fin k :=
    fun u hu => C ⟨s(v, u), (mem_neighborFinset G v u).1 hu⟩
  have hinj : ∀ a₁ a₂ ha₁ ha₂, f a₁ ha₁ = f a₂ ha₂ → a₁ = a₂ :=
    fun _ _ _ _ h => coloring_injective_at C _ _ h
  obtain ⟨u, hu, hcu⟩ := surj_on_of_inj_on_of_card_le (t := univ) f (fun _ _ => mem_univ _) hinj
    (by simp [card_neighborFinset_eq_degree, hG v]) c (mem_univ _)
  refine ⟨u, ⟨(mem_neighborFinset G v u).1 hu, hcu.symm⟩, ?_⟩
  rintro w ⟨hw, hwc⟩
  exact coloring_injective_at C hw ((mem_neighborFinset G v u).1 hu) (hwc.trans hcu)

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/EdgeColoring.lean
/-- A `k`-regular finite graph (`0 < k`) with a proper edge `k`-colouring has an even number of
vertices: each colour class is a perfect matching. -/
theorem even_card_of_lineGraph_coloring (hk : 0 < k) (hG : G.IsRegularOfDegree k)
    (C : G.lineGraph.Coloring (Fin k)) : Even (Fintype.card V) := by
  classical
  let H := colourClass C ⟨0, hk⟩
  have hdeg : ∀ v, H.degree v = 1 := by
    intro v
    obtain ⟨u, hu, huniq⟩ := existsUnique_colourClass_adj hG C ⟨0, hk⟩ v
    rw [← card_neighborFinset_eq_degree, card_eq_one]
    exact ⟨u, by ext w; simpa [mem_neighborFinset] using ⟨huniq w, fun h => h ▸ hu⟩⟩
  have := H.sum_degrees_eq_twice_card_edges
  simp only [hdeg, sum_const, card_univ, smul_eq_mul, mul_one] at this
  exact ⟨_, this.trans (two_mul _)⟩

end General

variable {d n : ℕ}

/-- **Theorem 21** of [Brandt et al., *LCL Problems on Grids*, PODC 2017]: for `d ≥ 1` and odd
`n ≥ 3`, the `d`-dimensional torus `(ℤ/n)^d` has no proper edge colouring with `2d` colours.

(The hypothesis `3 ≤ n` is needed: for `n = 1` the torus is a single vertex without edges, which is
trivially edge-colourable.) -/
theorem not_edgeColouring_torus (hd : 1 ≤ d) (hn : 3 ≤ n) (hodd : Odd n) :
    IsEmpty ((torusGraph d n).lineGraph.Coloring (Fin (2 * d))) := by
  have : NeZero n := ⟨by omega⟩
  refine ⟨fun C => ?_⟩
  have h := even_card_of_lineGraph_coloring (by omega) (torusGraph_isRegularOfDegree hn) C
  rw [card_torus] at h
  exact Nat.not_even_iff_odd.2 (hodd.pow) h

/-! ### Non-vacuity: the `4 × 4` torus is edge `4`-colourable -/

/-- Colour of the edge `{v, w}` of the `4 × 4` torus: `0`/`1` for horizontal edges and `2`/`3` for
vertical ones, alternating along each cycle. -/
def torus44Colour (v w : Fin 2 → ZMod 4) : Fin 4 :=
  if v 0 ≠ w 0 then (if (v 0 + w 0).val = 1 then 0 else 1)
  else (if (v 1 + w 1).val = 1 then 2 else 3)

lemma torus44Colour_comm : ∀ v w, torus44Colour v w = torus44Colour w v := by decide

lemma torus44Colour_ne : ∀ (x : Fin 2 → ZMod 4) (s t : Fin 2 ⊕ Fin 2), s ≠ t →
    torus44Colour x (nbr x s) ≠ torus44Colour x (nbr x t) := by decide

/-- An explicit proper edge `4`-colouring of the `4 × 4` torus. -/
def torus44Colouring : (torusGraph 2 4).lineGraph.Coloring (Fin 4) :=
  Coloring.mk (fun e => Sym2.lift ⟨torus44Colour, torus44Colour_comm⟩ e.1) (by
    intro e₁ e₂ h
    rw [lineGraph_adj_iff_exists] at h
    obtain ⟨hne, x, h₁, h₂⟩ := h
    obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.1 h₁
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.1 h₂
    have hxa : a ∈ (torusGraph 2 4).neighborFinset x := by
      rw [mem_neighborFinset, ← mem_edgeSet, ← ha]; exact e₁.2
    have hxb : b ∈ (torusGraph 2 4).neighborFinset x := by
      rw [mem_neighborFinset, ← mem_edgeSet, ← hb]; exact e₂.2
    rw [neighborFinset_torusGraph (by norm_num), mem_image] at hxa hxb
    obtain ⟨s, -, rfl⟩ := hxa
    obtain ⟨t, -, rfl⟩ := hxb
    simp only [ha, hb, Sym2.lift_mk]
    refine torus44Colour_ne x s t ?_
    rintro rfl
    exact hne (Subtype.ext (ha.trans hb.symm)))

/-- Non-vacuity of Theorem 21: for even `n` the conclusion fails, e.g. the `4 × 4` torus has a
proper edge `2 · 2`-colouring. -/
theorem torus44_edgeColourable : Nonempty ((torusGraph 2 4).lineGraph.Coloring (Fin (2 * 2))) :=
  ⟨torus44Colouring⟩

end Podc.LCLGrids
