import Mathlib
import Cslib.Foundations.Combinatorics.SimpleGraph.Orientation
import Papers.PODC2017.LCLGrids.TorusGraph

/-!
# No `{1,3}`-orientation of an odd 2-dimensional torus (Lemma 24)

Lemma 24 of Brandt et al., *LCL Problems on Grids* (PODC 2017): for odd `n`, the 2-dimensional
torus `(ℤ/n)^2` has no orientation in which every vertex has in-degree `1` or `3`.

We use CSLib's `SimpleGraph.Orientation` (every edge gets exactly one direction).

## Proof

In a `k`-regular finite graph, in-degree plus out-degree is `k` at every vertex and the in-degrees
and out-degrees have the same sum, so `2 · Σ indeg = k · |V|` (`two_mul_sum_inDeg`). For the
`n × n` torus (`n ≥ 3`, `k = 4`) this gives `Σ indeg = 2 n²`, which is even; but a sum of `n²` odd
numbers is odd for odd `n`. For `n = 1` the torus has no edges, so all in-degrees are `0`.
-/

namespace Podc.LCLGrids

open Finset SimpleGraph

section General

variable {V : Type*} {G : SimpleGraph V}

/-- The in-degree of `v` under the orientation `o`: the number of edges oriented towards `v`. -/
noncomputable def inDeg (o : G.Orientation) (v : V) : ℕ := {u | o.out u v}.ncard

variable [Fintype V] {k : ℕ}

lemma inDeg_eq_sum (o : G.Orientation) (v : V) [DecidablePred (o.out · v)] :
    inDeg o v = ∑ u, if o.out u v then 1 else 0 := by
  rw [inDeg, ← card_filter]
  convert Set.ncard_coe_finset (univ.filter (o.out · v))
  ext; simp

variable [DecidableRel G.Adj]

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/Orientation.lean
/-- In a `k`-regular finite graph, twice the sum of the in-degrees of any orientation is
`k · |V|` (in-degree plus out-degree is `k`, and both degree sums count the edges). -/
theorem two_mul_sum_inDeg (o : G.Orientation) (hG : G.IsRegularOfDegree k) :
    2 * ∑ v, inDeg o v = k * Fintype.card V := by
  classical
  have hk : ∀ v, k = ∑ u, ((if o.out u v then 1 else 0) + (if o.out v u then 1 else 0)) := by
    intro v
    rw [← hG v, ← card_neighborFinset_eq_degree, neighborFinset_eq_filter, card_filter]
    refine sum_congr rfl fun u _ => ?_
    by_cases h : G.Adj v u
    · rcases o.out_or_out h with h' | h'
      · simp [h, h', o.not_out_of_out h']
      · simp [h, h', o.not_out_of_out h']
    · have h1 : ¬ o.out u v := fun h' => h (o.adj_of_out h').symm
      have h2 : ¬ o.out v u := fun h' => h (o.adj_of_out h')
      simp [h, h1, h2]
  simp only [inDeg_eq_sum]
  calc 2 * ∑ v, ∑ u, (if o.out u v then 1 else 0)
      = ∑ v, ∑ u, (if o.out u v then 1 else 0) + ∑ v, ∑ u, (if o.out v u then 1 else 0) := by
        rw [two_mul]; congr 1; exact sum_comm
    _ = ∑ v, ∑ u, ((if o.out u v then 1 else 0) + (if o.out v u then 1 else 0)) := by
        simp only [← sum_add_distrib]
    _ = k * Fintype.card V := by
        simp only [← hk, sum_const, card_univ, smul_eq_mul, mul_comm]

end General

variable {n : ℕ}

/-- **Lemma 24** of [Brandt et al., *LCL Problems on Grids*, PODC 2017]: for odd `n`, there is no
orientation of the 2-dimensional torus `(ℤ/n)^2` in which every vertex has in-degree `1` or `3`.

(This holds for every odd `n`, including the degenerate `n = 1`, where the torus has no edges.) -/
theorem not_exists_oneThreeOrientation_torus (hodd : Odd n) :
    ¬ ∃ o : (torusGraph 2 n).Orientation, ∀ v, inDeg o v = 1 ∨ inDeg o v = 3 := by
  rintro ⟨o, ho⟩
  obtain ⟨m, rfl⟩ := hodd
  have : NeZero (2 * m + 1) := ⟨by omega⟩
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- `n = 1`: no edges, so every in-degree is `0`.
    have h0 : inDeg o 0 = 0 := by
      rw [inDeg, Set.ncard_eq_zero]
      ext u
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h => (o.adj_of_out h).1 (funext fun i => Subsingleton.elim (α := ZMod 1) _ _)
    have := ho 0
    omega
  · have hsum := two_mul_sum_inDeg o (torusGraph_isRegularOfDegree (d := 2) (by omega))
    rw [card_torus] at hsum
    have hmod : (∑ v, inDeg o v) % 2 = ((2 * m + 1) ^ 2) % 2 := by
      rw [sum_nat_mod, ← card_torus (d := 2), Fintype.card_eq_sum_ones, sum_nat_mod]
      congr 1
      refine sum_congr rfl fun v _ => ?_
      rcases ho v with h | h <;> rw [h]
    have hodd2 : ((2 * m + 1) ^ 2) % 2 = 1 := Nat.odd_iff.1 (Odd.pow ⟨m, rfl⟩)
    omega

end Podc.LCLGrids
