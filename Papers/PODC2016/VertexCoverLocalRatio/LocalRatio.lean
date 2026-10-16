import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The local-ratio template (Section 2, Theorem 2.1)

Bar-Yehuda, Censor-Hillel, Schwartzman, *A Distributed (2+ε)-Approximation for Vertex Cover in
`O(log Δ / ε log log Δ)` Rounds*, PODC 2016.

A vertex-weighted graph `G = (V, w, E)`; an edge function `δ : E → ℝ≥0` is *`G`-valid* if
`∑_{e ∋ v} δ(e) ≤ w(v)` for every vertex `v`. With `ε' = ε/(2+ε)` let
`S_δ = {v | w(v) - ∑_{e ∋ v} δ(e) ≤ ε' w(v)}`.

Theorem 2.1: `w(S_δ) ≤ (2+ε)·OPT`. We prove it against *every* vertex cover `C` (in particular a
minimum-weight one), and without assuming `w ≥ 0` (not needed).

Edge functions are functions on `Sym2 V` (only their values on edges of `G` matter).
-/

set_option linter.unusedSectionVars false

namespace VertexCoverLocalRatio

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- The weight `w(S) = ∑_{v ∈ S} w(v)` of a set of vertices. -/
def wt (w : V → ℝ) (S : Finset V) : ℝ := ∑ v ∈ S, w v

/-- `w̃_δ(v) = ∑_{e ∋ v} δ(e)`. -/
def tilde (δ : Sym2 V → ℝ) (v : V) : ℝ := ∑ u ∈ G.neighborFinset v, δ s(v, u)

/-- `δ` is `G`-valid: nonnegative on edges and `∑_{e ∋ v} δ(e) ≤ w(v)` for every vertex. -/
def IsValid (w : V → ℝ) (δ : Sym2 V → ℝ) : Prop :=
  (∀ e ∈ G.edgeSet, 0 ≤ δ e) ∧ ∀ v, tilde G δ v ≤ w v

/-- `ε' = ε / (2 + ε)`. -/
noncomputable def epsP (ε : ℝ) : ℝ := ε / (2 + ε)

/-- `S_δ = {v | w'_δ(v) ≤ ε' w(v)}` where `w'_δ = w - w̃_δ`. -/
noncomputable def Sdelta (ε : ℝ) (w : V → ℝ) (δ : Sym2 V → ℝ) : Finset V :=
  univ.filter fun v => w v - tilde G δ v ≤ epsP ε * w v

variable {G}

theorem tilde_nonneg {δ : Sym2 V → ℝ} (hδ : ∀ e ∈ G.edgeSet, 0 ≤ δ e) (v : V) :
    0 ≤ tilde G δ v :=
  sum_nonneg fun u hu => hδ _ ((mem_neighborFinset G v u).1 hu)

/-- Weak duality for edge packings, in the form used in the proof of Theorem 2.1:
`∑_{v ∈ V} w̃_δ(v) ≤ 2 ∑_{v ∈ C} w̃_δ(v)` for every vertex cover `C`. -/
theorem sum_tilde_le_two_mul {δ : Sym2 V → ℝ} (hδ : ∀ e ∈ G.edgeSet, 0 ≤ δ e) {C : Finset V}
    (hC : G.IsVertexCover ↑C) :
    ∑ v, tilde G δ v ≤ 2 * ∑ v ∈ C, tilde G δ v := by
  have hsplit := (sum_filter_add_sum_filter_not univ (· ∈ C) (tilde G δ)).symm
  have hfC : univ.filter (· ∈ C) = C := by ext; simp
  rw [hfC] at hsplit
  have hout : ∑ v ∈ univ.filter (· ∉ C), tilde G δ v ≤ ∑ v ∈ C, tilde G δ v := by
    have h1 : ∑ v ∈ univ.filter (· ∉ C), tilde G δ v =
        ∑ v ∈ univ.filter (· ∉ C), ∑ u ∈ C.filter (G.Adj v), δ s(v, u) := by
      refine sum_congr rfl fun v hv => ?_
      simp only [mem_filter, mem_univ, true_and] at hv
      unfold tilde
      congr 1
      ext u
      simp only [mem_neighborFinset, mem_filter]
      constructor
      · intro h
        refine ⟨?_, h⟩
        rcases hC h with h' | h'
        · exact absurd h' hv
        · exact h'
      · exact fun h => h.2
    have h2 : ∑ v ∈ univ.filter (· ∉ C), ∑ u ∈ C.filter (G.Adj v), δ s(v, u) =
        ∑ u ∈ C, ∑ v ∈ (univ.filter (· ∉ C)).filter (G.Adj u), δ s(v, u) := by
      apply sum_comm'
      intro v u
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h3.symm⟩, h2⟩
      · rintro ⟨⟨h1, h3⟩, h2⟩; exact ⟨h1, h2, h3.symm⟩
    rw [h1, h2]
    refine sum_le_sum fun u _ => ?_
    unfold tilde
    calc ∑ v ∈ (univ.filter (· ∉ C)).filter (G.Adj u), δ s(v, u)
        = ∑ v ∈ (univ.filter (· ∉ C)).filter (G.Adj u), δ s(u, v) := by
          refine sum_congr rfl fun v _ => by rw [Sym2.eq_swap]
      _ ≤ ∑ v ∈ G.neighborFinset u, δ s(u, v) := by
          apply sum_le_sum_of_subset_of_nonneg
          · intro v hv
            simp only [mem_filter] at hv
            simpa using hv.2
          · intro v hv _
            exact hδ _ ((mem_neighborFinset G u v).1 hv)
  linarith

/-- **Theorem 2.1** (local-ratio template). Fix `ε > 0` and a `G`-valid `δ`. Then
`w(S_δ) ≤ (2+ε)·w(C)` for every vertex cover `C`; in particular `w(S_δ) ≤ (2+ε)·OPT`, and if `S_δ`
is a vertex cover it is a `(2+ε)`-approximation of a minimum-weight vertex cover. -/
theorem theorem_2_1 {ε : ℝ} (hε : 0 < ε) {w : V → ℝ} {δ : Sym2 V → ℝ} (hv : IsValid G w δ)
    {C : Finset V} (hC : G.IsVertexCover ↑C) :
    wt w (Sdelta G ε w δ) ≤ (2 + ε) * wt w C := by
  obtain ⟨hδ, hval⟩ := hv
  -- `(1 - ε') w(v) ≤ w̃(v)` on `S_δ`
  have h1 : (1 - epsP ε) * wt w (Sdelta G ε w δ) ≤ ∑ v ∈ Sdelta G ε w δ, tilde G δ v := by
    rw [wt, mul_sum]
    refine sum_le_sum fun v hv => ?_
    simp only [Sdelta, mem_filter, mem_univ, true_and] at hv
    linarith
  have h2 : ∑ v ∈ Sdelta G ε w δ, tilde G δ v ≤ ∑ v, tilde G δ v :=
    sum_le_sum_of_subset_of_nonneg (subset_univ _) fun v _ _ => tilde_nonneg hδ v
  have h3 := sum_tilde_le_two_mul hδ hC
  have h4 : ∑ v ∈ C, tilde G δ v ≤ wt w C := sum_le_sum fun v _ => hval v
  have hθ : (2 + ε) * (1 - epsP ε) = 2 := by
    unfold epsP; field_simp; ring
  have hpos : 0 < 1 - epsP ε := by
    unfold epsP; rw [sub_pos, div_lt_one (by linarith)]; linarith
  have h5 : (1 - epsP ε) * wt w (Sdelta G ε w δ) ≤ 2 * wt w C := by linarith
  have h6 := mul_le_mul_of_nonneg_left h5 (by linarith : (0 : ℝ) ≤ 2 + ε)
  rw [← mul_assoc, hθ] at h6
  linarith

/-- Theorem 2.1, "in particular" part: if `S_δ` is a vertex cover, its weight is within `2+ε` of
the weight of every vertex cover. -/
theorem theorem_2_1_approx {ε : ℝ} (hε : 0 < ε) {w : V → ℝ} {δ : Sym2 V → ℝ}
    (hv : IsValid G w δ) (_hS : G.IsVertexCover ↑(Sdelta G ε w δ)) :
    ∀ C : Finset V, G.IsVertexCover ↑C → wt w (Sdelta G ε w δ) ≤ (2 + ε) * wt w C :=
  fun _ hC => theorem_2_1 hε hv hC

end VertexCoverLocalRatio
