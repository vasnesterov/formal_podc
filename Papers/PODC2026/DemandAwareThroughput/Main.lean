import Papers.PODC2026.DemandAwareThroughput.Separation
import Papers.PODC2026.DemandAwareThroughput.DependentRounding

/-!
# Theorem 5 and Theorem 2, unconditionally

Bentert, Avin, Schmid, PODC 2026. Combining the proof of Theorem 5 (`theorem_5_of_rounding` in
`Separation.lean`) with our proofs of Theorem 3 (`dependentRounding`) and Theorem 4
(`negCorrChernoff`).
-/

namespace Podc.DemandAwareThroughput

/-- **Theorem 5.** For each `κ < 5/8` there exists `n_κ` such that for all `n ≥ n_κ` and each
doubly stochastic `n × n` matrix `M`, `(M, κ)` is a yes-instance of Demand-Aware Throughput. -/
theorem theorem_5 {κ : ℝ} (hκ : κ < 5 / 8) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ M : Matrix (Fin n) (Fin n) ℝ, M ∈ doublyStochastic ℝ (Fin n) →
      DAThroughput M κ :=
  theorem_5_of_rounding dependentRounding hκ

/-- **Theorem 2.** For each `ε > 0` there exists `n_ε` such that for each `n ≥ n_ε` and each
doubly stochastic `n × n` matrix `M` there is a directed `(2n-1)`-regular graph that achieves
throughput `5/8 - ε` for `M`. -/
theorem theorem_2 {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ M : Matrix (Fin n) (Fin n) ℝ, M ∈ doublyStochastic ℝ (Fin n) →
      DAThroughput M (5 / 8 - ε) :=
  theorem_5 (by linarith)

end Podc.DemandAwareThroughput
