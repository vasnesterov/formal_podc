/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2021.ApproxByzantineOptimization.Basic

/-!
# Lemma 1 and the uniform reading of Theorem 1 (quadratic costs)

Quadratic costs `Q i x = ‖x - c i‖²` on a real inner product space (e.g. `ℝ^d`): every non-empty
aggregate has the unique minimum point `mean_T c` (`argminSet_quadratic`), so these profiles
satisfy Assumption 1 with unique minima, the setting of the paper's proofs.

* `no_uniform_resilience`: for `1 ≤ f < n` and every deterministic algorithm there is a quadratic
  profile on which it is not `(f, ε)`-resilient.
* `lemma_1`: Lemma 1 of the paper (`n/2 ≤ f < n`), as a corollary; `lemma_1_false_of_le` shows
  that it fails in the degenerate case `f ≥ n`.
* `theorem_1_uniform`: Theorem 1 read with the algorithm required to work for *all* profiles
  satisfying Assumption 1 (the reading in which the paper's proof is valid): true, but vacuous
  for `f ≥ 1`, because its hypothesis never holds.
-/

open Finset Metric
open scoped ENNReal NNReal RealInnerProductSpace

namespace Podc.ApproxByzantineOptimization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-- The quadratic profile `Q i x = ‖x - c i‖²`. -/
def quadProfile (c : Fin n → E) : Profile n E := fun i x => ‖x - c i‖ ^ 2

/-- The mean of the points `c i`, `i ∈ T`. -/
noncomputable def mean (c : Fin n → E) (T : Finset (Fin n)) : E :=
  (T.card : ℝ)⁻¹ • ∑ i ∈ T, c i

lemma sum_quad_eq (c : Fin n → E) {T : Finset (Fin n)} (hT : T.Nonempty) (x : E) :
    ∑ i ∈ T, ‖x - c i‖ ^ 2 =
      T.card * ‖x - mean c T‖ ^ 2 + ∑ i ∈ T, ‖mean c T - c i‖ ^ 2 := by
  set m := mean c T with hm
  have hcard : (T.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.2 hT).ne'
  have hsum : ∑ i ∈ T, (m - c i) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, hm, mean,
      ← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hcard, one_smul, sub_self]
  have h : ∀ i ∈ T, ‖x - c i‖ ^ 2 = ‖x - m‖ ^ 2 + 2 * ⟪x - m, m - c i⟫ + ‖m - c i‖ ^ 2 := by
    intro i _
    rw [← norm_add_sq_real]; congr 2; abel
  rw [Finset.sum_congr rfl h, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
    nsmul_eq_mul, ← Finset.mul_sum, ← inner_sum, hsum, inner_zero_right, mul_zero, add_zero]

/-- The aggregate of quadratic costs over a non-empty `T` has the unique minimum point
`mean c T`. -/
theorem argminSet_quadratic (c : Fin n → E) {T : Finset (Fin n)} (hT : T.Nonempty) :
    argminSet (quadProfile c) T = {mean c T} := by
  apply argminSet_eq_singleton
  intro y hy
  simp only [quadProfile]
  have e1 := sum_quad_eq c hT y
  have e2 := sum_quad_eq c hT (mean c T)
  rw [sub_self, norm_zero] at e2
  rw [e1, e2]
  have hcard : (0 : ℝ) < T.card := by exact_mod_cast Finset.card_pos.2 hT
  have : 0 < ‖y - mean c T‖ := norm_pos_iff.2 (sub_ne_zero.2 hy)
  nlinarith [pow_pos this 2]

/-- Quadratic profiles satisfy Assumption 1 (with unique minimum points). -/
theorem assumption1_quadratic (c : Fin n → E) : Assumption1 (quadProfile c) := fun T hT => by
  rw [argminSet_quadratic c hT]
  exact ⟨Set.singleton_nonempty _, isClosed_singleton⟩

variable [Nontrivial E]

/-- **No uniform resilience.** For `1 ≤ f < n`, every `ε ≥ 0` and every deterministic algorithm
there is a quadratic profile (hence satisfying Assumption 1, with unique minima) on which the
algorithm is not `(f, ε)`-resilient. Agent `0` has its minimum far away and all others at `0`; a set
of `n - f` agents avoiding agent `0` and one containing it have `arg min`s more than `2ε` apart. -/
theorem no_uniform_resilience {f : ℕ} (hf1 : 1 ≤ f) (hfn : f < n) (ε : ℝ≥0)
    (alg : Algorithm n E) :
    ∃ c : Fin n → E, ¬ IsResilient f ε alg (quadProfile c) := by
  have hn : 0 < n := by omega
  let i₀ : Fin n := ⟨0, hn⟩
  obtain ⟨u, hu⟩ := exists_norm_eq E (show (0 : ℝ) ≤ ((n - f : ℕ) : ℝ) * (2 * ε + 1) by positivity)
  let c : Fin n → E := fun i => if i = i₀ then u else 0
  refine ⟨c, ?_⟩
  -- `S₁` avoids agent `i₀`, `S₂ = {i₀} ∪ S₀` contains it
  obtain ⟨S₁, hS₁, hS₁c⟩ := Finset.exists_subset_card_eq (s := univ.erase i₀) (n := n - f)
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin];
        omega)
  obtain ⟨S₀, hS₀, hS₀c⟩ := Finset.exists_subset_card_eq (s := univ.erase i₀) (n := n - f - 1)
    (by rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin];
        omega)
  have hi₀S₀ : i₀ ∉ S₀ := fun h => by simpa using hS₀ h
  have hS₂c : (insert i₀ S₀).card = n - f := by
    rw [Finset.card_insert_of_notMem hi₀S₀, hS₀c]; omega
  have hS₁ne : S₁.Nonempty := Finset.card_pos.1 (by omega)
  have hS₂ne : (insert i₀ S₀).Nonempty := Finset.insert_nonempty _ _
  have hm₁ : mean c S₁ = 0 := by
    have : ∀ i ∈ S₁, c i = 0 := fun i hi => by
      have : i ≠ i₀ := by simpa using hS₁ hi
      simp [c, this]
    simp [mean, Finset.sum_eq_zero this]
  have hm₂ : mean c (insert i₀ S₀) = ((n - f : ℕ) : ℝ)⁻¹ • u := by
    have : ∀ i ∈ S₀, c i = 0 := fun i hi => by
      have : i ≠ i₀ := fun h => hi₀S₀ (h ▸ hi)
      simp [c, this]
    rw [mean, Finset.sum_insert hi₀S₀, Finset.sum_eq_zero this, add_zero, hS₂c]
    simp [c]
  refine not_isResilient_of_far (S := S₁) (T := insert i₀ S₀) (by omega) (by omega)
    (argminSet_quadratic c hS₁ne) (argminSet_quadratic c hS₂ne) ?_ alg
  rw [hm₁, hm₂, edist_dist, dist_zero_left, norm_smul, hu, norm_inv, Real.norm_natCast]
  have hnf : (0 : ℝ) < ((n - f : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - f by omega)
  rw [← mul_assoc, inv_mul_cancel₀ hnf.ne', one_mul]
  rw [show (2 : ℝ≥0∞) * ε = ENNReal.ofReal (2 * ε) by
    rw [ENNReal.ofReal_mul (by norm_num)]; simp]
  exact (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 (by linarith)

/-- **Lemma 1** of the paper: if `n/2 ≤ f < n` there is no deterministic algorithm that is
`(f, ε)`-resilient for all profiles satisfying Assumption 1 (even with unique minima; quadratic
costs suffice). The lemma holds already for every `1 ≤ f < n` (`no_uniform_resilience`); for
`f ≥ n` it is false (`lemma_1_false_of_le`). -/
theorem lemma_1 {f : ℕ} (hf : n ≤ 2 * f) (hfn : f < n) (ε : ℝ≥0) (alg : Algorithm n E) :
    ¬ ∀ Q : Profile n E, Assumption1 Q → IsResilient f ε alg Q := by
  intro h
  obtain ⟨c, hc⟩ := no_uniform_resilience (E := E) (show 1 ≤ f by omega) hfn ε alg
  exact hc (h _ (assumption1_quadratic c))

omit [InnerProductSpace ℝ E] [Nontrivial E] in
/-- Lemma 1 is false in the degenerate case `f ≥ n` (all agents may be faulty): then every
algorithm is `(f, 0)`-resilient for every profile. -/
theorem lemma_1_false_of_le {f : ℕ} (hf : n ≤ f) (alg : Algorithm n E) :
    ∀ Q : Profile n E, Assumption1 Q → IsResilient f 0 alg Q :=
  fun Q _ => isResilient_of_le hf 0 alg Q

/-- **Theorem 1, uniform reading.** If a deterministic algorithm is `(f, ε)`-resilient for *every*
profile satisfying Assumption 1, then every such profile is `(2f, ε)`-redundant. This is the
reading under which the paper's proof is valid (it lets the faulty agents' fabricated functions be
the true costs of another execution). It holds vacuously for `1 ≤ f < n`: the hypothesis is never
satisfied (`no_uniform_resilience`), whatever the redundancy of the profiles. -/
theorem theorem_1_uniform {f : ℕ} (hf1 : 1 ≤ f) (hfn : f < n) (ε : ℝ≥0) (alg : Algorithm n E)
    (h : ∀ Q : Profile n E, Assumption1 Q → IsResilient f ε alg Q) :
    ∀ Q : Profile n E, Assumption1 Q → IsRedundant f ε Q := by
  obtain ⟨c, hc⟩ := no_uniform_resilience (E := E) hf1 hfn ε alg
  exact absurd (h _ (assumption1_quadratic c)) hc

end Podc.ApproxByzantineOptimization
