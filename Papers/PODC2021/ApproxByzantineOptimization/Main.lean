/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2021.ApproxByzantineOptimization.Sufficiency
import Papers.PODC2021.ApproxByzantineOptimization.Quadratic
import Papers.PODC2021.ApproxByzantineOptimization.PerProfile
import Papers.PODC2021.ApproxByzantineOptimization.Tightness

/-!
# Approximate Byzantine fault-tolerance in distributed optimization (PODC 2021): summary

S. Liu, N. Gupta, N. H. Vaidya, *Approximate Byzantine Fault-Tolerance in Distributed
Optimization*, PODC 2021 (arXiv:2101.09337v5), Section 3.

* Lemma 1: `lemma_1` (`Quadratic.lean`); degenerate `f ≥ n`: `lemma_1_false_of_le`.
* Theorem 1: literal reading false (`theorem_1_false_per_profile`), uniform reading vacuous
  (`theorem_1_uniform`, `no_uniform_resilience`), class reading proved (`theorem_1_class`,
  `theorem_1_corrected`).
* Theorem 2: `theorem_2`, `theorem_2_strong`.

`resilience_window` combines Theorems 1 and 2 on the class of `(2f, ε')`-redundant profiles: the
best achievable resilience lies in `[ε', 2ε']`.
-/

open scoped NNReal

namespace Podc.ApproxByzantineOptimization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E] {n f : ℕ}

/-- **Theorems 1 and 2 together.** On the class of profiles satisfying Assumption 1 and
`(2f, ε')`-redundancy (`1 ≤ f`, `2f < n`): the algorithm of Theorem 2 is `(f, 2ε')`-resilient,
no deterministic algorithm is `(f, ε)`-resilient for `ε < ε'`, and the class is non-empty. -/
theorem resilience_window (hf1 : 1 ≤ f) (hfn : 2 * f < n) (ε' : ℝ≥0) :
    (∀ Q : Profile n E, Assumption1 Q → IsRedundant f ε' Q →
      IsResilient f (2 * ε') (algorithm f) Q) ∧
    (∀ ε : ℝ≥0, ε < ε' → ∀ alg : Algorithm n E,
      ¬ ∀ Q : Profile n E, Assumption1 Q → IsRedundant f ε' Q → IsResilient f ε alg Q) ∧
    (∃ Q : Profile n E, Assumption1 Q ∧ IsRedundant f ε' Q) := by
  refine ⟨fun Q hA hR => theorem_2 (by omega) hA hR, fun ε hε alg h => ?_, ?_⟩
  · exact absurd (theorem_1_class hf1 hfn alg h) (not_le.2 hε)
  · rcases eq_or_ne ε' 0 with rfl | hε'
    · -- constant costs: every `arg min` is the whole space
      refine ⟨fun _ _ => 0, fun T _ => ?_, fun S S' _ _ _ => ?_⟩
      · have : argminSet (fun (_ : Fin n) (_ : E) => (0 : ℝ)) T = Set.univ := by
          ext x; simp [argminSet]
        rw [this]; exact ⟨Set.univ_nonempty, isClosed_univ⟩
      · have : ∀ T, argminSet (fun (_ : Fin n) (_ : E) => (0 : ℝ)) T = Set.univ := fun T => by
          ext x; simp [argminSet]
        rw [this, this, Metric.hausdorffEDist_self]; exact le_rfl
    · obtain ⟨Q, hA, hR, -⟩ := theorem_1_corrected (E := E) hf1 hfn
        (pos_iff_ne_zero.2 hε') (fun _ => 0)
      exact ⟨Q, hA, hR⟩

/-- The results apply to `ℝ^d` for `d ≥ 1`. -/
example (d : ℕ) [NeZero d] (hf1 : 1 ≤ f) (hfn : 2 * f < n) {ε : ℝ≥0} (hε : 0 < ε) :
    ¬ ∀ Q : Profile n (EuclideanSpace ℝ (Fin d)), Assumption1 Q →
      IsRedundant f ε Q → IsResilient f (ε / 2) (fun _ => 0) Q := by
  intro h
  have := theorem_1_class hf1 hfn _ h
  have h2 : (ε : ℝ) ≤ ε / 2 := by exact_mod_cast this
  have h3 : (0 : ℝ) < ε := by exact_mod_cast hε
  linarith

end Podc.ApproxByzantineOptimization
