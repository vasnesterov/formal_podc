import Papers.PODC2026.CanonicalRoundByzantine.LowerBound

/-!
# Main results of Section 3 of [AFW26]

[AFW26] H. Attiya, I. Flam, J. L. Welch. *Why Canonical-Round Algorithms Fail for Optimal Byzantine
Resilience.* PODC 2026, doi:10.1145/3796701.3815948.

All statements are about canonical-round algorithms in the asynchronous Byzantine model of
`Cslib.Byzantine.CanonicalRounds` (see `Cslib/Computability/Distributed/Byzantine/CanonicalRounds/Model.lean` and the README for the modelling
choices). `Safe f S` is "the safety properties of `S` hold in every admissible execution, for every
tape"; `ncSpec x₀ x₁ d₀ d₁` is the nontrivial convergence problem.

* `theorem1` (Theorem 1): randomized, `3f < n ≤ 5f`: the expected round complexity is not bounded
  by any `K` (`theorem1_unbounded`).
* `corollary6` (Corollary 6): deterministic: the worst-case round complexity exceeds every `K`.
* `theorem7` (Theorem 7): communication-closed, randomized: some adversary prevents termination
  with probability `1` (in fact for every tape).
* `corollary8` (Corollary 8): no deterministic communication-closed algorithm solves the problem.
* Section 3.3: the same for consensus, approximate agreement (on `ℝ` and on graphs) and connected
  consensus / crusader agreement (`consensus_unbounded`, …).
-/

namespace Podc2026.CanonicalRound

open Cslib.Byzantine.CanonicalRounds MeasureTheory

variable {n : ℕ} {V R M O : Type*}

section

variable (alg : CanonAlg n V R M O) {f : ℕ}

/-- Not all correct processes decide by round `K` ⇒ round complexity `> K`. -/
theorem lt_rounds_of_not_allDecideBy {I : Fin n → V} {ρ : Tape n R} {A : Adversary n R M} {K : ℕ}
    (h : ¬ alg.AllDecideBy f I ρ A K) : (K : ℕ∞) < alg.rounds f I ρ A := by
  have : ((K + 1 : ℕ) : ℕ∞) ≤ alg.rounds f I ρ A := by
    refine le_iInf₂ fun r hr => ?_
    by_contra hlt
    push Not at hlt
    have hlt' : r < K + 1 := by exact_mod_cast hlt
    exact h fun p hp => by
      obtain ⟨k, hk⟩ := hr p hp
      exact ⟨k, decidesBy_mono alg (by omega) hk⟩
  exact lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self K) this

theorem nonempty_R_of_measure [MeasurableSpace R] (hn : 0 < n) (μ : Measure (Tape n R))
    [IsProbabilityMeasure μ] : Nonempty R := by
  obtain ⟨ρ⟩ := nonempty_of_isProbabilityMeasure μ
  exact ⟨ρ ⟨0, hn⟩ 0⟩

/-- **Theorem 1 of [AFW26].** For `3f < n ≤ 5f`, for any randomized canonical-round algorithm
whose decisions satisfy the safety properties (agreement, validity) of a nontrivial convergence
problem in every admissible execution, and any distribution `μ` of the random choices, the
expected number of rounds until all correct processes decide is greater than `K`, for any
`K ∈ ℕ`: some inputs and admissible adversary achieve expected round complexity `> K`. -/
theorem theorem1 [MeasurableSpace R] (μ : Measure (Tape n R)) [IsProbabilityMeasure μ]
    (h3f : 3 * f < n) (h5f : n ≤ 5 * f) {x₀ x₁ : V} {d₀ d₁ : O}
    (hsafe : alg.Safe f (ncSpec x₀ x₁ d₀ d₁)) (K : ℕ) :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      (K : ENNReal) < alg.expRounds f I μ A := by
  have := nonempty_R_of_measure (by omega) μ
  obtain ⟨I, A, hA, hK⟩ := thm1_core alg (by omega) (by omega) h5f hsafe K
  refine ⟨I, A, hA, ?_⟩
  have hle : ∀ ρ, ((K + 1 : ℕ) : ENNReal) ≤ ((alg.rounds f I ρ A : ℕ∞) : ENNReal) := fun ρ => by
    have := lt_rounds_of_not_allDecideBy alg (hK ρ)
    have h' : ((K + 1 : ℕ) : ℕ∞) ≤ alg.rounds f I ρ A := Order.add_one_le_of_lt this
    exact_mod_cast ENat.toENNReal_le.2 h'
  calc (K : ENNReal) < ((K + 1 : ℕ) : ENNReal) := by exact_mod_cast Nat.lt_succ_self K
    _ = ∫⁻ _, ((K + 1 : ℕ) : ENNReal) ∂μ := by simp
    _ ≤ alg.expRounds f I μ A := lintegral_mono hle

/-- Theorem 1, restated: the expected round complexity of a safe algorithm admits no bound. -/
theorem theorem1_unbounded [MeasurableSpace R] (μ : Measure (Tape n R)) [IsProbabilityMeasure μ]
    (h3f : 3 * f < n) (h5f : n ≤ 5 * f) {x₀ x₁ : V} {d₀ d₁ : O}
    (hsafe : alg.Safe f (ncSpec x₀ x₁ d₀ d₁)) :
    ¬ ∃ K : ℕ, ∀ I (A : Adversary n R M), alg.Admissible f I A → alg.expRounds f I μ A ≤ K := by
  rintro ⟨K, hK⟩
  obtain ⟨I, A, hA, hlt⟩ := theorem1 alg μ h3f h5f hsafe K
  exact absurd (hK I A hA) (not_le.2 hlt)

/-- **Corollary 6 of [AFW26].** For a deterministic canonical-round algorithm (`R = Unit`;
the statement holds for every tape type) that satisfies the safety properties of a nontrivial
convergence problem with `3f < n ≤ 5f`, the worst-case number of rounds until all correct
processes decide is greater than `K`, for any `K`. -/
theorem corollary6 [Nonempty R] (h3f : 3 * f < n) (h5f : n ≤ 5 * f) {x₀ x₁ : V} {d₀ d₁ : O}
    (hsafe : alg.Safe f (ncSpec x₀ x₁ d₀ d₁)) (K : ℕ) :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      ∀ ρ, (K : ℕ∞) < alg.rounds f I ρ A := by
  obtain ⟨I, A, hA, hK⟩ := thm1_core alg (by omega) (by omega) h5f hsafe K
  exact ⟨I, A, hA, fun ρ => lt_rounds_of_not_allDecideBy alg (hK ρ)⟩

/-- **Theorem 7 of [AFW26].** For a randomized *communication-closed* canonical-round algorithm
satisfying the safety properties of a nontrivial convergence problem with `3f < n ≤ 5f`, there
are an admissible adversary and inputs such that the probability that all correct processes
eventually decide is `0` (in fact, termination fails for every tape). -/
theorem theorem7 [MeasurableSpace R] (μ : Measure (Tape n R)) [IsProbabilityMeasure μ]
    (hcc : alg.CommClosed) (h3f : 3 * f < n) (h5f : n ≤ 5 * f) {x₀ x₁ : V} {d₀ d₁ : O}
    (hsafe : alg.Safe f (ncSpec x₀ x₁ d₀ d₁)) :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      μ {ρ | alg.AllDecide f I ρ A} = 0 ∧ ∀ ρ, ¬ alg.AllDecide f I ρ A := by
  have := nonempty_R_of_measure (by omega) μ
  obtain ⟨I, A, hA, h⟩ := thm7_core alg hcc (by omega) (by omega) h5f hsafe
  refine ⟨I, A, hA, ?_, h⟩
  rw [show {ρ | alg.AllDecide f I ρ A} = ∅ from Set.eq_empty_of_forall_notMem h, measure_empty]

/-- **Corollary 8 of [AFW26].** No deterministic communication-closed canonical-round algorithm
solves a nontrivial convergence problem when `3f < n ≤ 5f`: safety and termination (all correct
processes decide in every admissible execution) cannot both hold. -/
theorem corollary8 [Nonempty R] (hcc : alg.CommClosed) (h3f : 3 * f < n) (h5f : n ≤ 5 * f)
    {x₀ x₁ : V} {d₀ d₁ : O} :
    ¬ (alg.Safe f (ncSpec x₀ x₁ d₀ d₁) ∧
      ∀ I (A : Adversary n R M), alg.Admissible f I A → ∀ ρ, alg.AllDecide f I ρ A) := by
  rintro ⟨hsafe, hterm⟩
  obtain ⟨I, A, hA, h⟩ := thm7_core alg hcc (by omega) (by omega) h5f hsafe
  obtain ⟨ρ⟩ : Nonempty (Tape n R) := inferInstance
  exact h ρ (hterm I A hA ρ)

/-! ### Section 3.3: consequences for specific problems -/

/-- Theorem 1 for any problem implying nontrivial convergence. -/
theorem theorem1_of_implies [MeasurableSpace R] (μ : Measure (Tape n R)) [IsProbabilityMeasure μ]
    (h3f : 3 * f < n) (h5f : n ≤ 5 * f) {S : Spec n V O} {x₀ x₁ : V} {d₀ d₁ : O}
    (hS : SpecImplies S (ncSpec x₀ x₁ d₀ d₁)) (hsafe : alg.Safe f S) (K : ℕ) :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      (K : ENNReal) < alg.expRounds f I μ A :=
  theorem1 alg μ h3f h5f (hsafe.mono hS) K

/-- Corollary 8 for any problem implying nontrivial convergence. -/
theorem corollary8_of_implies [Nonempty R] (hcc : alg.CommClosed) (h3f : 3 * f < n)
    (h5f : n ≤ 5 * f) {S : Spec n V O} {x₀ x₁ : V} {d₀ d₁ : O}
    (hS : SpecImplies S (ncSpec x₀ x₁ d₀ d₁)) :
    ¬ (alg.Safe f S ∧
      ∀ I (A : Adversary n R M), alg.Admissible f I A → ∀ ρ, alg.AllDecide f I ρ A) :=
  fun ⟨hs, ht⟩ => corollary8 alg hcc h3f h5f ⟨hs.mono hS, ht⟩

end

/-- Section 3.3: randomized **consensus** (with at least two values) has unbounded expected
canonical round complexity for `3f < n ≤ 5f`. -/
theorem consensus_unbounded {f : ℕ} (alg : CanonAlg n V R M V) [MeasurableSpace R]
    (μ : Measure (Tape n R)) [IsProbabilityMeasure μ] (h3f : 3 * f < n) (h5f : n ≤ 5 * f)
    {x₀ x₁ : V} (hx : x₀ ≠ x₁) (hsafe : alg.Safe f consensusSpec) (K : ℕ) :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      (K : ENNReal) < alg.expRounds f I μ A :=
  theorem1_of_implies alg μ h3f h5f (consensus_nc hx) hsafe K

/-- Section 3.3: no communication-closed canonical-round **consensus** algorithm. -/
theorem consensus_not_commClosed {f : ℕ} (alg : CanonAlg n V R M V) [Nonempty R]
    (hcc : alg.CommClosed) (h3f : 3 * f < n) (h5f : n ≤ 5 * f) {x₀ x₁ : V} (hx : x₀ ≠ x₁) :
    ¬ (alg.Safe f consensusSpec ∧
      ∀ I (A : Adversary n R M), alg.Admissible f I A → ∀ ρ, alg.AllDecide f I ρ A) :=
  corollary8_of_implies alg hcc h3f h5f (consensus_nc hx)

/-- Section 3.3: deterministic `ε`-**approximate agreement** on `ℝ` has unbounded worst-case
canonical round complexity for `3f < n ≤ 5f`. -/
theorem approx_unbounded {f : ℕ} {ε : ℝ} (alg : CanonAlg n ℝ R M ℝ) [Nonempty R]
    (h3f : 3 * f < n) (h5f : n ≤ 5 * f) (hsafe : alg.Safe f (approxSpec ε)) (K : ℕ) :
    ∃ (I : Fin n → ℝ) (A : Adversary n R M), alg.Admissible f I A ∧
      ∀ ρ, (K : ℕ∞) < alg.rounds f I ρ A := by
  refine corollary6 alg h3f h5f (x₀ := 0) (x₁ := |ε| + 1) (hsafe.mono (approx_nc ?_)) K
  rw [zero_sub, abs_neg, abs_of_pos (by positivity)]; linarith [le_abs_self ε]

/-- Section 3.3: deterministic **approximate agreement on a graph** with two vertices at distance
`2` has unbounded worst-case canonical round complexity for `3f < n ≤ 5f`. -/
theorem graphApprox_unbounded {f : ℕ} {W : Type*} {G : SimpleGraph W} {u w : W}
    (huw : G.edist u w = 2) (alg : CanonAlg n W R M W) [Nonempty R]
    (h3f : 3 * f < n) (h5f : n ≤ 5 * f) (hsafe : alg.Safe f (graphApproxSpec G)) (K : ℕ) :
    ∃ (I : Fin n → W) (A : Adversary n R M), alg.Admissible f I A ∧
      ∀ ρ, (K : ℕ∞) < alg.rounds f I ρ A :=
  corollary6 alg h3f h5f (hsafe.mono (graphApprox_nc huw)) K

/-- Section 3.3: deterministic **connected consensus** with parameter `R ≥ 1` (crusader agreement
for `R = 1`, gradecast for `R = 2`) with two input values has unbounded worst-case canonical
round complexity for `3f < n ≤ 5f`. -/
theorem connectedConsensus_unbounded {f Rg : ℕ} (hR : 1 ≤ Rg) {v v' : V} (hv : v ≠ v')
    (alg : CanonAlg n V R M (Option V × ℕ)) [Nonempty R] (h3f : 3 * f < n) (h5f : n ≤ 5 * f)
    (hsafe : alg.Safe f (connectedConsensusSpec Rg)) (K : ℕ) :
    ∃ (I : Fin n → V) (A : Adversary n R M), alg.Admissible f I A ∧
      ∀ ρ, (K : ℕ∞) < alg.rounds f I ρ A :=
  corollary6 alg h3f h5f (hsafe.mono (connectedConsensus_nc hR hv)) K

/-- Section 3.3: no communication-closed canonical-round **connected consensus** (in particular
crusader agreement) algorithm for `3f < n ≤ 5f`. -/
theorem connectedConsensus_not_commClosed {f Rg : ℕ} (hR : 1 ≤ Rg) {v v' : V} (hv : v ≠ v')
    (alg : CanonAlg n V R M (Option V × ℕ)) [Nonempty R] (hcc : alg.CommClosed)
    (h3f : 3 * f < n) (h5f : n ≤ 5 * f) :
    ¬ (alg.Safe f (connectedConsensusSpec Rg) ∧
      ∀ I (A : Adversary n R M), alg.Admissible f I A → ∀ ρ, alg.AllDecide f I ρ A) :=
  corollary8_of_implies alg hcc h3f h5f (connectedConsensus_nc hR hv)

/-! ### The literal statement "`n ≤ 5f`" needs `n ≥ 2` -/

/-- The one-process algorithm that decides its own input immediately (messages are `()`). -/
def decideInput (R : Type*) : CanonAlg 1 Bool R Unit Bool := ⟨fun _ _ _ => (), fun _ v _ => some v⟩

theorem decision_decideInput {R : Type*} (p : Fin 1) (v : Bool) (l : Log 1 R Unit) :
    (decideInput R).decision p v l = some v := by
  cases l <;> simp [CanonAlg.decision, decideInput, List.inits]

/-- Theorem 1 / Corollary 6 as literally stated ("`n ≤ 5f`") fail for `n = 1`, `f = 1`: the single
process can decide its input in round `0`; this solves the nontrivial convergence problem
(`x₀ = d₀ = false`, `x₁ = d₁ = true`) with round complexity `0` under every admissible adversary.
The paper's setting is `3f < n ≤ 5f`; our proof needs `2f ≤ n`. -/
theorem literal_theorem1_fails_n1 {R : Type*} :
    (decideInput R).Safe 1 (ncSpec false true false true) ∧
      ∀ I (A : Adversary 1 R Unit) ρ, (decideInput R).rounds 1 I ρ A = 0 := by
  refine ⟨fun I A _ ρ k => ?_, fun I A ρ => ?_⟩
  · simp only [decision_decideInput]
    refine ⟨fun p _ q _ h1 h2 => ?_, fun p hp _ hall => by beta_reduce; rw [hall p hp],
      fun p hp _ hall => by beta_reduce; rw [hall p hp]⟩
    have : p = q := Subsingleton.elim _ _
    subst this; simp_all
  · refine le_antisymm (iInf₂_le 0 fun p _ => ⟨0, [], by simp, by simp, by simp [decideInput]⟩)
      zero_le

end Podc2026.CanonicalRound
