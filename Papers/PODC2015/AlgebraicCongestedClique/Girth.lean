import Cslib.Foundations.Combinatorics.SimpleGraph.Girth
import Mathlib

/-!
# Girth: Lemma 14 and the combinatorial core of Theorem 15 (Censor-Hillel et al., PODC 2015)

* `lemma_14`: a graph on `n` vertices with girth `g` has at most `n^{1 + 1/⌊(g-1)/2⌋} + n` edges
  (the Moore bound, CSLib `NoShortCycles.ncard_edgeSet_le_rpow`).
* `theorem_15_dense`, `theorem_15_sparse`: the case split of the proof of Theorem 15 for `ρ > 0`
  with `ℓ = ⌈2 + 2/ρ⌉`: if the graph has more than `n^{1+1/⌊ℓ/2⌋} + n` edges its girth is at most
  `ℓ`; otherwise it has at most `2 n^{1+ρ}` edges.
-/

namespace Podc.AlgebraicCongestedClique

open SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Lemma 14 (girth `≥ g` form): if every cycle has length at least `g ≥ 3`, then `G` has at most
`n^{1 + 1/⌊(g-1)/2⌋} + n` edges. -/
theorem lemma_14_of_le {g : ℕ} (hg : 3 ≤ g) (h : (g : ℕ∞) ≤ G.egirth) :
    (G.edgeSet.ncard : ℝ) ≤
      (Fintype.card V : ℝ) ^ (1 + 1 / (((g - 1) / 2 : ℕ) : ℝ)) + Fintype.card V := by
  refine NoShortCycles.ncard_edgeSet_le_rpow (by omega) ?_
  rw [noShortCycles_iff_lt_egirth]
  refine lt_of_lt_of_le ?_ h
  exact_mod_cast (by omega : 2 * ((g - 1) / 2) < g)

/-- Lemma 14 of [Censor-Hillel et al., PODC 2015] (from [Bollobás, *Extremal graph theory*,
pp. 362–363]): a graph with girth `g` has at most `n^{1 + 1/⌊(g-1)/2⌋} + n` edges. -/
theorem lemma_14 {g : ℕ} (h : G.egirth = g) :
    (G.edgeSet.ncard : ℝ) ≤
      (Fintype.card V : ℝ) ^ (1 + 1 / (((g - 1) / 2 : ℕ) : ℝ)) + Fintype.card V := by
  have h3 : (3 : ℕ∞) ≤ g := h ▸ three_le_egirth
  exact lemma_14_of_le G (by exact_mod_cast h3) h.ge

/-- The threshold length `ℓ = ⌈2 + 2/ρ⌉` of the proof of Theorem 15. -/
noncomputable def girthL (ρ : ℝ) : ℕ := ⌈2 + 2 / ρ⌉₊

lemma three_le_girthL {ρ : ℝ} (hρ : 0 < ρ) : 3 ≤ girthL ρ := by
  have : (2 : ℝ) < 2 + 2 / ρ := by have := div_pos two_pos hρ; linarith
  have h := Nat.lt_ceil.2 (show ((2 : ℕ) : ℝ) < 2 + 2 / ρ by exact_mod_cast this)
  exact h

lemma inv_half_girthL_le {ρ : ℝ} (hρ : 0 < ρ) : 1 / ((girthL ρ / 2 : ℕ) : ℝ) ≤ ρ := by
  have hl := Nat.le_ceil (2 + 2 / ρ)
  have h1 : (1 : ℝ) / ρ ≤ ((girthL ρ / 2 : ℕ) : ℝ) := by
    have h2 : ((girthL ρ : ℕ) : ℝ) ≤ 2 * ((girthL ρ / 2 : ℕ) : ℝ) + 1 := by
      have : girthL ρ ≤ 2 * (girthL ρ / 2) + 1 := by omega
      exact_mod_cast this
    have : 2 + 2 / ρ ≤ 2 * ((girthL ρ / 2 : ℕ) : ℝ) + 1 := hl.trans h2
    rw [div_eq_mul_one_div 2 ρ] at this
    linarith
  have hpos : (0 : ℝ) < ((girthL ρ / 2 : ℕ) : ℝ) := by
    have := three_le_girthL hρ
    exact_mod_cast (by omega : 0 < girthL ρ / 2)
  rw [div_le_iff₀ hpos]
  rw [div_le_iff₀ hρ] at h1
  linarith

/-- Theorem 15, dense case: with `ℓ = ⌈2 + 2/ρ⌉` (`ρ > 0`), a graph with more than
`n^{1 + 1/⌊ℓ/2⌋} + n` edges has girth at most `ℓ` (by Lemma 14), so its girth is found by
searching for `k`-cycles, `3 ≤ k ≤ ℓ`. -/
theorem theorem_15_dense {ρ : ℝ} (hρ : 0 < ρ)
    (h : (Fintype.card V : ℝ) ^ (1 + 1 / ((girthL ρ / 2 : ℕ) : ℝ)) + Fintype.card V <
      G.edgeSet.ncard) :
    G.egirth ≤ girthL ρ := by
  by_contra hc
  push Not at hc
  have h3 := three_le_girthL hρ
  have := lemma_14_of_le G (g := girthL ρ + 1) (by omega) (by push_cast; exact Order.add_one_le_of_lt hc)
  have he : (girthL ρ + 1 - 1) / 2 = girthL ρ / 2 := by omega
  rw [he] at this
  linarith

/-- Theorem 15, sparse case: with `ℓ = ⌈2 + 2/ρ⌉` (`ρ > 0`) and `n ≥ 1`, the threshold
`n^{1 + 1/⌊ℓ/2⌋} + n` is at most `2 n^{1+ρ} = O(n^{1+ρ})`, so a graph below it can be collected
at every node in `O(n^ρ)` rounds. -/
theorem theorem_15_sparse {ρ : ℝ} (hρ : 0 < ρ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (1 + 1 / ((girthL ρ / 2 : ℕ) : ℝ)) + n ≤ 2 * (n : ℝ) ^ (1 + ρ) := by
  have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : (n : ℝ) ^ (1 + 1 / ((girthL ρ / 2 : ℕ) : ℝ)) ≤ (n : ℝ) ^ (1 + ρ) :=
    Real.rpow_le_rpow_of_exponent_le hn' (by linarith [inv_half_girthL_le hρ])
  have h2 : (n : ℝ) ≤ (n : ℝ) ^ (1 + ρ) := by
    calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hn' (by linarith)
  linarith

end Podc.AlgebraicCongestedClique
