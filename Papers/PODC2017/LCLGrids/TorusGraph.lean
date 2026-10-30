import Mathlib

/-!
# The `d`-dimensional toroidal grid

Brandt et al., *LCL Problems on Grids* (PODC 2017), work on the `d`-dimensional `n × ⋯ × n` torus.
We model its vertex set as `Fin d → ZMod n`; two vertices are adjacent iff they differ by a unit
vector `±e_i`.

## Main definitions

* `torusGraph d n`: the `d`-dimensional toroidal grid with side length `n`.

## Main results

* `torusGraph_isRegularOfDegree`: for `3 ≤ n` every vertex has degree `2 * d`.
* `card_torus`: the torus has `n ^ d` vertices.
-/

namespace Podc.LCLGrids

open Finset

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/Torus.lean
/-- The `d`-dimensional toroidal grid `(ℤ/n)^d`: `v` and `w` are adjacent iff they are distinct and
differ by a unit vector `e_i = Pi.single i 1` (in either direction). -/
def torusGraph (d n : ℕ) : SimpleGraph (Fin d → ZMod n) where
  Adj v w := v ≠ w ∧ ∃ i, w = v + Pi.single i 1 ∨ v = w + Pi.single i 1
  symm := ⟨fun _ _ ⟨h, i, hi⟩ => ⟨Ne.symm h, i, hi.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

variable {d n : ℕ}

lemma torusGraph_adj {v w : Fin d → ZMod n} :
    (torusGraph d n).Adj v w ↔ v ≠ w ∧ ∃ i, w = v + Pi.single i 1 ∨ v = w + Pi.single i 1 :=
  Iff.rfl

instance [NeZero n] : DecidableRel (torusGraph d n).Adj := fun _ _ => by
  unfold torusGraph; infer_instance

/-- The torus has `n ^ d` vertices. -/
lemma card_torus [NeZero n] : Fintype.card (Fin d → ZMod n) = n ^ d := by
  simp [ZMod.card]

/-- The `2d` neighbours `v + e_i` (`Sum.inl i`) and `v - e_i` (`Sum.inr i`) of `v`. -/
def nbr (v : Fin d → ZMod n) : Fin d ⊕ Fin d → (Fin d → ZMod n)
  | .inl i => v + Pi.single i 1
  | .inr i => v - Pi.single i 1

/-- For `3 ≤ n` the `2d` vectors `v ± e_i` are pairwise distinct. -/
lemma nbr_injective (hn : 3 ≤ n) (v : Fin d → ZMod n) : Function.Injective (nbr v) := by
  have : Fact (1 < n) := ⟨by omega⟩
  have h2 : (2 : ZMod n) ≠ 0 := by
    intro h
    have := (ZMod.natCast_eq_zero_iff 2 n).1 (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) this
    omega
  rintro (i | i) (j | j) h <;> simp only [nbr] at h
  · have := congrFun (add_left_cancel h) i
    by_contra hij
    have hij' : i ≠ j := fun e => hij (congrArg _ e)
    simp [hij'] at this
  · have := congrFun h i
    by_cases hij : i = j
    · subst hij; simp at this
      exact absurd (by linear_combination this) h2
    · simp [hij] at this
  · have := congrFun h i
    by_cases hij : i = j
    · subst hij; simp at this
      exact absurd (by linear_combination -this) h2
    · simp [hij] at this
  · have := congrFun (sub_right_injective h) i
    by_contra hij
    have hij' : i ≠ j := fun e => hij (congrArg _ e)
    simp [hij'] at this

lemma nbr_ne (hn : 3 ≤ n) (v : Fin d → ZMod n) (s : Fin d ⊕ Fin d) : nbr v s ≠ v := by
  have : Fact (1 < n) := ⟨by omega⟩
  rcases s with i | i <;> intro h <;> simp only [nbr] at h
  · have := congrFun h i; simp at this
  · have := congrFun h i; simp at this

/-- For `3 ≤ n`, the neighbours of `v` are exactly the `2d` vertices `v ± e_i`. -/
lemma neighborFinset_torusGraph [NeZero n] (hn : 3 ≤ n) (v : Fin d → ZMod n) :
    (torusGraph d n).neighborFinset v = univ.image (nbr v) := by
  ext w
  simp only [SimpleGraph.mem_neighborFinset, torusGraph_adj, mem_image, mem_univ, true_and]
  constructor
  · rintro ⟨-, i, rfl | rfl⟩
    · exact ⟨.inl i, rfl⟩
    · exact ⟨.inr i, by simp [nbr]⟩
  · rintro ⟨s, rfl⟩
    refine ⟨(nbr_ne hn v s).symm, ?_⟩
    rcases s with i | i
    · exact ⟨i, Or.inl rfl⟩
    · exact ⟨i, Or.inr (by simp [nbr])⟩

/-- For `3 ≤ n`, every vertex of the `d`-dimensional torus has degree `2 * d`. -/
theorem torusGraph_isRegularOfDegree [NeZero n] (hn : 3 ≤ n) :
    (torusGraph d n).IsRegularOfDegree (2 * d) := by
  intro v
  rw [← SimpleGraph.card_neighborFinset_eq_degree, neighborFinset_torusGraph hn,
    card_image_of_injective _ (nbr_injective hn v)]
  simp [two_mul]

end Podc.LCLGrids
