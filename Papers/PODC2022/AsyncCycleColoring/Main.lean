import Papers.PODC2022.AsyncCycleColoring.Alg1Extreme
import Papers.PODC2022.AsyncCycleColoring.Alg2
import Papers.PODC2022.AsyncCycleColoring.Alg3
import Papers.PODC2022.AsyncCycleColoring.Alg3Proper
import Papers.PODC2022.AsyncCycleColoring.ColeVishkin
import Papers.PODC2022.AsyncCycleColoring.CounterexampleAllN

/-!
# Fault Tolerant Coloring of the Asynchronous Cycle — main results

Fraigniaud, Lambein-Monette, Rabie, PODC 2022 (arXiv:2207.11198).

* `AsyncCycle.theorem_3_1` — Algorithm 1 (6 colours) is wait-free (≤ ⌊3n/2⌋ + 4 activations;
  sharper: `alg1_workActs_le`, `max 4 n`), correct, 6-colour palette. Also `lemma_3_9`
  (`ℓ + ℓ' + 1`), `workActs_le_four_of_max/min` (local extrema), `lemma_3_2`.
* `AsyncCycle.theorem_3_11_false`, `theorem_3_11_false_all` — Algorithm 2 (5 colours) is **not**
  wait-free, on every cycle `C_n`, `n ≥ 3`; `lemma_3_13_false`. Correctness and palette hold:
  `alg2_properOutputs`, `alg2_outputs_lt_five`.
* `AsyncCycle.theorem_4_4_false`, `theorem_4_4_false_all` — Algorithm 3 (fast 5 colours) is
  **not** wait-free; correctness/palette hold: `alg3_properOutputs`, `alg3_outputs_lt_five`.
* `AsyncCycle.lemma_4_1`, `lemma_4_2`, `lemma_4_3` (Cole–Vishkin reduction function),
  `lemma_4_5` (+ `alg3_X_proper`, `alg3_X_ne_reg`): identifiers of Algorithm 3 stay proper.
-/
