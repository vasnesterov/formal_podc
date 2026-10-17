/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Papers.PODC2020.RedundantOptimization.Necessity
import Papers.PODC2020.RedundantOptimization.Examples

/-!
# Gupta–Vaidya, *Fault-Tolerance in Distributed Optimization: The Case of Redundancy* (PODC 2020)

Main results (see `README.md`):

* Lemma 1: `RedundantOptimization.lemma1`.
* Theorem 1 (literal reading, vacuous): `RedundantOptimization.theorem1`,
  `RedundantOptimization.no_resilient_allExecs`; Part I of its proof: `RedundantOptimization.partI`.
* Theorem 1 repaired (indistinguishability form, both directions, exactly `f` faults):
  `RedundantOptimization.theorem1_indistinguishable`; fails with fewer faults:
  `RedundantOptimization.theorem1_indistinguishable_false_fewer_faults`.
* Why the literal reading is vacuous: `RedundantOptimization.redundant_execution_confusable`
  (partner without a common minimum point); degenerate `n = f = 1`:
  `RedundantOptimization.theorem1_false_n_eq_one`.
* A stronger reading not claimed by the paper is false: `RedundantOptimization.sharp_necessity_false`,
  `RedundantOptimization.not_sharp_theorem1`.
* Sufficiency (existence): `RedundantOptimization.exists_resilient_redundant`.
* Theorem 2: `RedundantOptimization.Assumptions.theorem2`, `…theorem2_rho_nonneg`,
  `…theorem2_tendsto`, `…mem_Wstar_of_threshold_eq_zero`; non-vacuity
  `RedundantOptimization.example_assumptions`; (i) fails in the degenerate case
  `RedundantOptimization.theorem2_rho_nonneg_false`.
-/
