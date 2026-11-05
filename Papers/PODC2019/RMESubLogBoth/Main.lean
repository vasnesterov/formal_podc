import Papers.PODC2019.RMESubLogBoth.NonVacuity
import Papers.PODC2019.RMESubLogBoth.PaperInv
import Papers.PODC2019.RMESubLogBoth.Signal

/-!
# Main results for [JJJ19] (PODC 2019)

P. Jayanti, S. Jayanti, A. Joshi. *A Recoverable Mutex Algorithm with Sub-logarithmic RMR on Both
CC and DSM.* PODC 2019 (arXiv 1904.02124v2).

The correctness part of Theorem 2 for the `k`-ported algorithm of Figures 3–4:

* Lemma 4 (Mutual Exclusion): `mutual_exclusion`.
* Lemma 5 (Starvation Freedom, finitely many crashes, fair runs): `starvation_freedom`.
* Lemma 6 (Wait-free Exit): `wait_free_exit`.
* Lemma 7 (Wait-free CSR): `wait_free_csr`.
* Lemma 8 (Critical Section Reentry): `cs_reentry`.
* Our replacement for Lemma 9: `inv_reach` (the invariant `Inv`, `InvDefs.lean`).
* Lemma 9 is false as stated: `PaperInv.cond5_csSignal_false`, `PaperInv.cond5_nonNil_false`,
  `PaperInv.cond4_false`.
* Non-vacuity: `step_total`, `exists_run`, `exists_fair_run`.

Theorem 1 (Signal object, Figure 2): `Signal.theorem1_i_linearization_point`,
`Signal.theorem1_i_set_completes`, `Signal.theorem1_ii`, `Signal.theorem1_iii`,
`Signal.theorem1_iv`, `Signal.theorem1_v_set`, `Signal.theorem1_v_wait_dsm`,
`Signal.theorem1_v_wait_cc`.
-/
