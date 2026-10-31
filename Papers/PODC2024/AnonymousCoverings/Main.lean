import Papers.PODC2024.AnonymousCoverings.WriteScan
import Papers.PODC2024.AnonymousCoverings.Lemmas
import Papers.PODC2024.AnonymousCoverings.Counterexamples
import Papers.PODC2024.AnonymousCoverings.WaitFree
import Papers.PODC2024.AnonymousCoverings.Groups
import Papers.PODC2024.AnonymousCoverings.Examples
import Papers.PODC2024.AnonymousCoverings.Safety

/-!
# Losa–Gafni, *Understanding Read-Write Wait-Free Coverings in the Fully-Anonymous Shared-Memory
Model* (PODC 2024)

Entry point. Main results:

* `Podc.AnonymousCoverings.theorem_4_8`, `theorem_4_8_unique_source` — Theorem 4.8.
* `Podc.AnonymousCoverings.Exec.lemma_4_5`, `Exec.lemma_4_6`, `Exec.lemma_4_7` — Lemmas 4.5–4.7
  as printed (4.6 and 4.7 with `N ≤ |R|`); `Exec.false_of_two_closed` — the two-group form used for
  Theorem 4.8.
* `Podc.AnonymousCoverings.theorem_4_8_needs_registers`, `theorem_4_8_needs_registers'`,
  `lemma_4_6_needs_registers` —
  counterexamples with fewer registers than processors.
* `Podc.AnonymousCoverings.snapshot_safety_paper`, `snapshot_safety`, `snapshot_safety_outputs` —
  safety of the snapshot algorithm (§5.3.2, new proof; also footnote 4).
* `Podc.AnonymousCoverings.snapshot_live_false`, `snapshot_waitFree` — wait-freedom (§5.3.3).
* `Podc.AnonymousCoverings.renaming_of_groupSnapshot` — Section 6; `example_3_2` — Section 3.2;
  `figure_2` — Figure 2.
-/
