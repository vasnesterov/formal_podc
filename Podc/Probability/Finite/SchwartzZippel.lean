import Cslib.Probability.Finite.Uniform
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

-- CSLib candidate: Cslib/Probability/Finite/SchwartzZippel.lean

/-!
# Schwartz–Zippel for uniformly random points of `σ → R`

Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` is stated for polynomials in the variables
`Fin n` and points drawn from `S ^ n` for a finset `S`. In applications (random linear network
coding, polynomial identity testing) the variables usually carry structure (`σ` = coded symbols ×
coordinates, …) and the random point is uniform on the whole finite ring. This file restates the
lemma for an arbitrary finite variable type `σ`, with probabilities computed by counting
(`Cslib.Probability.uprob`).

## Main statements

* `card_filter_eval_eq_zero_mul_le`: `#{x | p(x) = 0} · |R| ≤ deg p · |R| ^ |σ|`.
* `uprob_eval_eq_zero_le`: `Pr_x[p(x) = 0] ≤ deg p / |R|`.
* `one_sub_le_uprob_eval_ne_zero`: `1 - deg p / |R| ≤ Pr_x[p(x) ≠ 0]`.
-/

namespace Cslib.Probability

open Finset MvPolynomial

variable {σ R : Type*} [Fintype σ] [DecidableEq σ] [CommRing R] [IsDomain R] [Fintype R] [DecidableEq R]

/-- **Schwartz–Zippel** (counting form, arbitrary finite set of variables): a nonzero polynomial
vanishes on at most a `deg p / |R|` fraction of the points of `σ → R`. -/
theorem card_filter_eval_eq_zero_mul_le {p : MvPolynomial σ R} (hp : p ≠ 0) :
    (#(univ.filter fun x : σ → R => eval x p = 0) : ℚ≥0) * Fintype.card R ≤
      p.totalDegree * (Fintype.card R : ℚ≥0) ^ Fintype.card σ := by
  classical
  set N := Fintype.card σ
  let e : σ ≃ Fin N := Fintype.equivFin σ
  set q : MvPolynomial (Fin N) R := rename e p with hq_def
  have hq : q ≠ 0 := fun h => hp (rename_injective _ e.injective (by simpa [hq_def] using h))
  have hdeg : (q.totalDegree : ℚ≥0) ≤ p.totalDegree := by
    exact_mod_cast totalDegree_rename_le _ _
  have hsz := schwartz_zippel_totalDegree hq (univ : Finset R)
  rw [Fintype.piFinset_univ, card_univ] at hsz
  have hcard : #(univ.filter fun x : σ → R => eval x p = 0) =
      #(univ.filter fun f : Fin N → R => eval f q = 0) := by
    refine card_bij' (fun x _ => x ∘ e.symm) (fun f _ => f ∘ e) ?_ ?_ ?_ ?_
    · intro x hx
      simp only [mem_filter, mem_univ, true_and] at hx ⊢
      rw [hq_def, eval_rename]; simpa [Function.comp_def] using hx
    · intro f hf
      simp only [mem_filter, mem_univ, true_and] at hf ⊢
      rwa [hq_def, eval_rename] at hf
    · intro x _; ext; simp
    · intro f _; ext; simp
  rw [hcard]
  have hR : (0 : ℚ≥0) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  rw [div_le_div_iff₀ (by positivity) hR] at hsz
  exact hsz.trans (by gcongr)

/-- **Schwartz–Zippel** (probability form): for a nonzero polynomial `p` and a uniformly random
point `x : σ → R`, `Pr[p(x) = 0] ≤ deg p / |R|`. -/
theorem uprob_eval_eq_zero_le {p : MvPolynomial σ R} (hp : p ≠ 0) :
    uprob (fun x : σ → R => eval x p = 0) ≤ p.totalDegree / Fintype.card R := by
  classical
  have h := card_filter_eval_eq_zero_mul_le hp
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have h' : (#(univ.filter fun x : σ → R => eval x p = 0) : ℝ) * Fintype.card R ≤
      p.totalDegree * (Fintype.card R : ℝ) ^ Fintype.card σ := by exact_mod_cast h
  rw [uprob_eq_card_filter, Fintype.card_fun, div_le_div_iff₀ (by push_cast; positivity) hR]
  push_cast
  linarith

/-- **Schwartz–Zippel** (success probability): `1 - deg p / |R| ≤ Pr[p(x) ≠ 0]`. -/
theorem one_sub_le_uprob_eval_ne_zero {p : MvPolynomial σ R} (hp : p ≠ 0) :
    1 - p.totalDegree / (Fintype.card R : ℝ) ≤ uprob (fun x : σ → R => eval x p ≠ 0) := by
  rw [uprob_not]
  linarith [uprob_eval_eq_zero_le hp]

end Cslib.Probability
