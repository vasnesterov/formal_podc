import Papers.PODC2019.AbortableMutexAmortized.PaperInv
import Papers.PODC2019.AbortableMutexAmortized.NotInductive
import Papers.PODC2019.AbortableMutexAmortized.AFCFS
import Papers.PODC2019.AbortableMutexAmortized.Starvation
import Papers.PODC2019.AbortableMutexAmortized.RMRTheorem

/-!
# Jayanti & Jayanti, *Constant Amortized RMR Abortable Mutex for CC and DSM* (PODC 2019)

Index of the main results (see `README.md`):

* Theorem 4.1: `theorem_4_1`, `theorem_4_1_unique` (`PaperInv.lean`); the paper's invariant is not
  inductive: `paperInv_not_inductive` (`NotInductive.lean`); strengthened inductive invariant:
  `inv_step`, `Reachable.inv` (`Invariant.lean`).
* Corollary 4.1.1: `mutual_exclusion`.
* Theorem 4.2 (AFCFS): false as stated, `afcfs_literal_false`; corrected, `theorem_4_2`.
* Lemmas 4.3, 4.4, Theorem 4.5: `lemma_4_3`, `lemma_4_4_part1`, `lemma_4_4_part2`,
  `promoters_spec`, `theorem_4_5`.
* Theorem 5.1: `theorem_5_1`; Lemmas 5.2, 5.3: `lemma_5_2`, `lemma_5_3`; Theorem 5.4:
  `theorem_5_4_dsm`, `theorem_5_4_cc`, `theorem_5_4_exit`, `theorem_5_4_fastAbort`.
-/
