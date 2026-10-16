import Papers.PODC2021.AllYouNeedIsDAG.Liveness
import Papers.PODC2021.AllYouNeedIsDAG.NonVacuity
import Papers.PODC2021.AllYouNeedIsDAG.Coin
import Papers.PODC2021.AllYouNeedIsDAG.ChainQuality
import Papers.PODC2021.AllYouNeedIsDAG.ChainQualityCounterexample
import Papers.PODC2021.AllYouNeedIsDAG.Lemma1Counterexample

/-!
# All You Need is DAG (PODC 2021) — summary

Keidar, Kokoris-Kogias, Naor, Spiegelman. Main results (see `README.md` for the table):

* `DagRider.run_integrity`, `DagRider.run_total_order` (Propositions 1–2, every valid run),
* `DagRider.run_agreement`, `DagRider.run_validity` (Propositions 3–4, given infinitely many
  good waves),
* `DagRider.delivered_prefix`, `DagRider.lemma1_direct` (safety core, arbitrary local views),
* `DagRider.lemma2`, `DagRider.core_card`, `DagRider.sPath_of_mem_core`, `DagRider.core_congr`,
  `DagRider.goodWave_of_core` (Lemma 2, robust form), `DagRider.Coin.dagRider_expected_waves`
  (Claim 6),
* `DagRider.chain_quality` (chain quality for round-major orders),
* counterexamples: `DagRider.Lemma1Counterexample.lemma1_false`,
  `DagRider.ChainQualityCounterexample.chain_quality_false`.

Non-vacuity: the lock-step run of `NonVacuity.lean` is valid and all its waves are good, so the
hypotheses of Agreement and Validity are satisfiable (`nonVacuity`).
-/

namespace DagRider

/-- The hypotheses of `run_agreement` and `run_validity` hold in the lock-step run
`NonVacuity.R` (for any coin and any deterministic order). -/
theorem nonVacuity (coin : ℕ → Fin 4) :
    NonVacuity.R.Valid 1 NonVacuity.G0 NonVacuity.blk ∧
      ∀ w₀, ∃ w, w₀ ≤ w ∧ 1 ≤ w ∧ NonVacuity.R.GoodWave 1 NonVacuity.G0 coin w :=
  ⟨NonVacuity.valid, fun w₀ => ⟨w₀ + 1, by omega, by omega,
    fun _ _ u _ hu => NonVacuity.good_waves _ u hu _⟩⟩

end DagRider
