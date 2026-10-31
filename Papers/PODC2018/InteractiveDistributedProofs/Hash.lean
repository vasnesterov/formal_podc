import Mathlib

/-!
# The linear hash family (Theorem 3.2)

For a prime `p` and a finite index type `ι` with `m = |ι|` coordinates, the polynomial hash
`h_s(x) = ∑_i x_i · s^{e(i)}` (`e : ι ≃ Fin m` a fixed enumeration, seed `s ∈ ZMod p`) is additive on
`ι → ZMod p`, and two distinct vectors collide for at most `m - 1` seeds (a nonzero polynomial of
degree `< m` has `< m` roots).

The paper states Theorem 3.2 for inputs in `{0,1}^m`, but its linearity clause adds vectors modulo
`p`, and the protocols hash matrices with entries in `{0, …, n}` (for a non-injective `ρ`). We prove
the theorem on all of `(ZMod p)^m`, which contains the paper's statement (`{0,1}^m ⊆ (ZMod p)^m`).
-/

open Finset

namespace Podc.InteractiveDistributedProofs

variable {ι : Type*} [Fintype ι] {p : ℕ}

-- CSLib candidate
/-- The polynomial hash with seed `s`, as an additive map `(ι → ZMod p) →+ ZMod p`. -/
noncomputable def polyHash (s : ZMod p) : (ι → ZMod p) →+ ZMod p where
  toFun x := ∑ i, x i * s ^ ((Fintype.equivFin ι i : ℕ))
  map_zero' := by simp
  map_add' x y := by simp [add_mul, Finset.sum_add_distrib]

theorem polyHash_apply (s : ZMod p) (x : ι → ZMod p) :
    polyHash s x = ∑ i, x i * s ^ ((Fintype.equivFin ι i : ℕ)) := rfl

open Polynomial in
/-- The collision polynomial of `x` and `y`. -/
noncomputable def collPoly (x y : ι → ZMod p) : (ZMod p)[X] :=
  ∑ i, C (x i - y i) * X ^ ((Fintype.equivFin ι i : ℕ))

open Polynomial in
theorem eval_collPoly (x y : ι → ZMod p) (s : ZMod p) :
    (collPoly x y).eval s = polyHash s x - polyHash s y := by
  simp [collPoly, polyHash_apply, eval_finsetSum, sub_mul, Finset.sum_sub_distrib]

open Polynomial in
theorem collPoly_coeff (x y : ι → ZMod p) (i : ι) :
    (collPoly x y).coeff (Fintype.equivFin ι i : ℕ) = x i - y i := by
  simp only [collPoly, finsetSum_coeff, coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    have : ((Fintype.equivFin ι i : ℕ)) ≠ (Fintype.equivFin ι j : ℕ) := by
      intro h; exact hj ((Fintype.equivFin ι).injective (Fin.ext h)).symm
    simp [this]
  · simp

open Polynomial in
theorem collPoly_natDegree_le (x y : ι → ZMod p) :
    (collPoly x y).natDegree ≤ Fintype.card ι - 1 := by
  unfold collPoly
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  refine (natDegree_C_mul_X_pow_le _ _).trans ?_
  have := (Fintype.equivFin ι i).isLt
  omega

/-- **Collision bound.** Two distinct vectors of `(ZMod p)^ι` collide for at most `|ι| - 1` seeds. -/
theorem card_collision_le [Fact p.Prime] {x y : ι → ZMod p} (hxy : x ≠ y) :
    #(univ.filter fun s : ZMod p => polyHash s x = polyHash s y) ≤ Fintype.card ι - 1 := by
  classical
  have hne : collPoly x y ≠ 0 := by
    intro h0
    apply hxy
    funext i
    have := collPoly_coeff x y i
    rw [h0, Polynomial.coeff_zero] at this
    exact (sub_eq_zero.1 this.symm)
  refine le_trans ?_ (collPoly_natDegree_le x y)
  refine Polynomial.card_le_degree_of_subset_roots ?_
  intro s hs
  have hs' : s ∈ univ.filter fun s : ZMod p => polyHash s x = polyHash s y := hs
  rw [Polynomial.mem_roots hne, Polynomial.IsRoot, eval_collPoly]
  simp only [Finset.mem_filter] at hs'
  rw [hs'.2, sub_self]

/-- **Theorem 3.2** (on `(ZMod p)^m`). For a prime `p` and `m ∈ ℕ` there is a family of `p` additive
hash functions `(ZMod p)^m → ZMod p` (indexed by `ZMod p`) such that two distinct inputs collide
for at most `m` members of the family, i.e. with probability at most `m / p`. -/
theorem theorem_3_2 (m : ℕ) [Fact p.Prime] :
    ∃ H : ZMod p → ((Fin m → ZMod p) →+ ZMod p),
      ∀ x x' : Fin m → ZMod p, x ≠ x' →
        #(univ.filter fun i : ZMod p => H i x = H i x') ≤ m :=
  ⟨polyHash, fun _ _ h => (card_collision_le h).trans (by simp)⟩

end Podc.InteractiveDistributedProofs
