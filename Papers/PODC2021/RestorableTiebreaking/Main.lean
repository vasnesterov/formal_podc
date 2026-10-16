import Papers.PODC2021.RestorableTiebreaking.ATWPaths
import Papers.PODC2021.RestorableTiebreaking.Random
import Papers.PODC2021.RestorableTiebreaking.Counterexamples
import Papers.PODC2021.RestorableTiebreaking.Corollary22
import Papers.PODC2021.RestorableTiebreaking.Spanner

/-!
# Bodwin–Parter, *Restorable Shortest Path Tiebreaking for Edge-Faulty Graphs* (PODC 2021)

Entry point. Main results (see `README.md` for the full paper ↔ Lean table):

* `RestorableTiebreaking.theorem2` / `theorem2_single` — Theorem 2 (main result).
* `RestorableTiebreaking.theorem19` / `theorem19_path` — Theorem 19.
* `RestorableTiebreaking.theorem20`, `theorem23`, `corollary22` — existence of ATW functions.
* `RestorableTiebreaking.theorem37` — Theorem 37 (no symmetric restorable scheme on `C₄`).
* `RestorableTiebreaking.theorem31_correct`, `theorem31_f0`, `theorem30`, `theorem29_correct`,
  `lemma32_correct` — applications.
* `RestorableTiebreaking.theorem19_literal_false`, `paper_count_false` — errors in the paper.
-/
