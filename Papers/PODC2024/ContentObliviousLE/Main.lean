import Papers.PODC2024.ContentObliviousLE.Alg1
import Papers.PODC2024.ContentObliviousLE.Theorem1
import Papers.PODC2024.ContentObliviousLE.Theorem2
import Papers.PODC2024.ContentObliviousLE.LowerBound
import Papers.PODC2024.ContentObliviousLE.IdZero

/-!
# Content-Oblivious Leader Election on Rings (PODC 2024) — main results

Frei, Gelles, Ghazy, Nolin. *Brief Announcement: Content-Oblivious Leader Election on Rings.*
PODC 2024; full version arXiv 2405.03646.

* Algorithm 1 (quiescent stabilization, Lemma 15): `Podc.ContentOblivious.Alg1.algorithm_1`
* Theorem 1 (Algorithm 2): `Podc.ContentOblivious.Alg2.theorem_1`
* Theorem 2 / Proposition 14 (Algorithm 3): `Podc.ContentOblivious.Alg3.theorem_2`,
  `Podc.ContentOblivious.Alg3.proposition_14`
* Theorem 3 / Theorem 17 and Lemmas 19–21: `Podc.ContentOblivious.LowerBound.theorem_3`,
  `theorem_17`, `lemma_19`, `lemma_20`, `corollary_21`, `unbounded_single_node`
* Non-vacuity: `LowerBound.alg2_solves`; per-instance reading of Theorem 3 is false:
  `LowerBound.theorem_3_per_instance_false`
* IDs must be positive: `Podc.ContentOblivious.Alg2.infinite_execution_id_zero`
-/
