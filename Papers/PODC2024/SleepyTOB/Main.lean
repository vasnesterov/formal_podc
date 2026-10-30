import Papers.PODC2024.SleepyTOB.Resilience
import Papers.PODC2024.SleepyTOB.Counterexample
import Papers.PODC2024.SleepyTOB.Examples
import Papers.PODC2024.SleepyTOB.Adversary

/-!
# Asynchrony-Resilient Sleepy Total-Order Broadcast Protocols (PODC 2024) — main results

D'Amato, Losa, Zanolini. arXiv:2309.05347v2.

* Lemma 1: `Podc.SleepyTOB.lemma_1`, `Podc.SleepyTOB.lemma_1_clique_validity`
  (generalised: `Podc.SleepyTOB.clique_validity`); correspondence with the modified Algorithm 1:
  `Podc.SleepyTOB.Exec.tally_eq_ga_M`, `Podc.SleepyTOB.Exec.isGA`.
* Lemma 2: `Podc.SleepyTOB.Exec.lemma_2`.
* Lemma 3: `Podc.SleepyTOB.Exec.lemma_3` (base case: `Podc.SleepyTOB.Exec.Follows.decision_lock`).
* Theorem 2: `Podc.SleepyTOB.Exec.theorem_2`; non-vacuity:
  `Podc.SleepyTOB.theorem_2_hypotheses_satisfiable`.
* Theorem 1, safety half (no asynchrony): `Podc.SleepyTOB.Exec.theorem_1_safety`.
* Algorithm 1 as printed is unsafe: `Podc.SleepyTOB.algorithm_1_literal_unsafe`,
  `Podc.SleepyTOB.theorem_1_false_for_literal_algorithm`,
  `Podc.SleepyTOB.theorem_2_false_for_literal_algorithm`.
* Definition 4's literal integrity fails: `Podc.SleepyTOB.integrity_literal_false`; graded
  consistency alone does not give Lemma 3's base case: `Podc.SleepyTOB.graded_consistency_insufficient`.
* Section 2.3: `Podc.SleepyTOB.Exec.sleepy_of_churn_of_failure`, `Podc.SleepyTOB.Exec.footnote_7`,
  `Podc.SleepyTOB.betaTilde_identity`.
-/
