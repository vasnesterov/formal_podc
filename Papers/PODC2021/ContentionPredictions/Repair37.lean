import Papers.PODC2021.ContentionPredictions.Randomized
import Mathlib.Probability.ProductMeasure

/-!
# Repaired lower bound of Theorem 3.7 (randomized, collision detection, advice)

The paper's proof of Theorem 3.7 simulates a CD algorithm with expected time `t` without
collision detection "in `2^t` rounds"; but the simulation costs `E[2^T]`, which can be much larger
than `2^{E[T]}` (see `theorem_3_7_lower_exp` in `Randomized.lean`). We repair it:

* **Markov**: with `M = 2t`, a block of `K = 2^M - 1` simulated rounds (one per history of length
  `< M`) fails only if the CD execution needs more than `M` rounds, which has probability
  `≤ t / (2t + 1) ≤ 1/2` (`mul_measure_blockFail_le`).
* **Independent restarts**: each player draws a sequence of independent strategies
  (`Measure.infinitePi`) and runs the blocks one after another (`restartSched`). After swapping
  the product over players and copies (`pi_infinitePi_map_swap`), the block failures are
  independent, so the expected time is `≤ K ∑ 2^{-j} ≤ 2^{2t+1}` (`expTime_restart_le`).
  (No deterministic fallback is needed: infinitely many copies fail together with probability 0.)
* Combined with the interleaving of all advice values (`theorem_3_6_lower`), the bound of [18]
  gives `c log₂ n ≤ |A| · 2^{2t+1}` (`theorem_3_7_lower`), i.e. with `b` bits of advice
  `2t ≥ log₂ (c log₂ n) - b - 3` (`theorem_3_7_lower_bits`; the paper claims
  `t ≥ log₂ (c log₂ n) - b`, the same order `Θ(log log n - b)`).
-/

namespace Podc.ContentionPredictions

open MeasureTheory Finset
open scoped ENNReal

variable {n : ℕ}

/-- Swapping the two indices of a product of independent copies. -/
theorem pi_infinitePi_map_swap {X : Type*} [MeasurableSpace X] (μ : Fin n → Measure X)
    [∀ v, IsProbabilityMeasure (μ v)] :
    (Measure.pi fun v => Measure.infinitePi fun _ : ℕ => μ v).map (fun x j v => x v j) =
      Measure.infinitePi fun _ : ℕ => Measure.pi μ := by
  rw [← Measure.infinitePi_eq_pi]
  have h1 := Measure.infinitePi_map_curry (fun (v : Fin n) (_ : ℕ) => μ v)
  have h2 := Measure.infinitePi_map_curry (fun (_ : ℕ) (v : Fin n) => μ v)
  have h3 := Measure.infinitePi_map_piCongrLeft (X := fun _ : ℕ × Fin n => X)
    (fun p : ℕ × Fin n => μ p.2) (Equiv.prodComm (Fin n) ℕ)
  simp only [← Measure.infinitePi_eq_pi] at *
  rw [← h1, ← h2, ← h3, Measure.map_map (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl


/-! ### Restarts -/

/-- Run independent copies of a CD strategy, one after another, each simulated without collision
detection over a block of `K` rounds (one per history of length `< M`, `K = 2^M - 1`): round
`j * K + i` follows copy `j` after the `i`-th history. -/
def restartSched (K : ℕ) (ω : ℕ → List Bool → Bool) (r : ℕ) : Bool :=
  ω (r / K) (histOfIndex (r % K))

theorem measurable_restartSched (K : ℕ) : Measurable (restartSched K) := by
  unfold restartSched; fun_prop

/-- The block of `K` simulated rounds of the strategies `σ` contains no successful round. -/
def blockFail (P : Finset (Fin n)) (K : ℕ) : Set (Fin n → List Bool → Bool) :=
  {σ | ∀ i < K, (P.filter fun v => σ v (histOfIndex i)).card ≠ 1}

theorem measurableSet_blockFail (P : Finset (Fin n)) (K : ℕ) :
    MeasurableSet (blockFail P K) := by
  unfold blockFail
  simp only [Set.ofPred_forall]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ => ?_
  have hm : Measurable fun (σ : Fin n → List Bool → Bool) (v : Fin n) => σ v (histOfIndex i) := by
    fun_prop
  exact hm (Set.toFinite {x : Fin n → Bool | (P.filter fun v => x v).card ≠ 1}).measurableSet

/-- If the block of `2^M - 1` simulated rounds fails, the CD execution needs more than `M`
rounds. -/
theorem le_cdTime_of_mem_blockFail (P : Finset (Fin n)) (M : ℕ) {σ : Fin n → List Bool → Bool}
    (hσ : σ ∈ blockFail P (2 ^ M - 1)) : ((M + 1 : ℕ) : ℝ≥0∞) ≤ cdTime P σ := by
  refine le_iInf₂ fun r hr => ?_
  by_contra hlt
  have hrM : r < M := by
    by_contra h; exact hlt (by exact_mod_cast (by omega : M + 1 ≤ r + 1))
  set h := history true (stratAlg σ) () P r
  have hi := indexOfHist_lt h
  rw [history_length] at hi
  have : 2 ^ (r + 1) ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) hrM
  refine hσ (indexOfHist h) (by omega) ?_
  rw [histOfIndex_indexOfHist]
  exact hr

/-- Markov's inequality for the failure of one block. -/
theorem mul_measure_blockFail_le (D : Fin n → Measure (List Bool → Bool))
    (P : Finset (Fin n)) (M : ℕ) :
    ((M + 1 : ℕ) : ℝ≥0∞) * Measure.pi D (blockFail P (2 ^ M - 1)) ≤ expTimeCD D P := by
  unfold expTimeCD
  rw [← lintegral_indicator_const (measurableSet_blockFail P _)]
  refine lintegral_mono fun σ => ?_
  exact Set.indicator_apply_le' (fun hσ => le_cdTime_of_mem_blockFail P M hσ) (fun _ => zero_le)

/-- Pathwise: the restarted simulation succeeds in the first block that succeeds. -/
theorem succTime_restart_le (P : Finset (Fin n)) {K : ℕ} (hK : 0 < K)
    (y : ℕ → Fin n → List Bool → Bool) :
    succTime P (fun v => restartSched K (fun j => y j v)) ≤
      ∑' j, (Set.pi (↑(Finset.range j)) fun _ => blockFail P K).indicator
        (fun _ => (K : ℝ≥0∞)) y := by
  by_cases hall : ∀ j, y j ∈ blockFail P K
  · have : ∀ j, (Set.pi (↑(Finset.range j)) fun _ => blockFail P K).indicator
        (fun _ => (K : ℝ≥0∞)) y = K := fun j => by
      rw [Set.indicator_of_mem]; exact fun i _ => hall i
    simp only [this]
    rw [ENNReal.tsum_const_eq_top_of_ne_zero (by exact_mod_cast hK.ne')]
    exact le_top
  push Not at hall
  classical
  let j0 := Nat.find hall
  have hj0 : y j0 ∉ blockFail P K := Nat.find_spec hall
  have hmin : ∀ i < j0, y i ∈ blockFail P K := fun i hi => by
    by_contra h; exact Nat.find_min hall hi h
  simp only [blockFail, Set.mem_ofPred_eq, not_forall, not_not] at hj0
  obtain ⟨i, hiK, hi⟩ := hj0
  have hr1 : (j0 * K + i) / K = j0 := by
    rw [Nat.mul_comm, Nat.mul_add_div hK, Nat.div_eq_of_lt hiK, add_zero]
  have hr2 : (j0 * K + i) % K = i := by
    rw [Nat.mul_comm, Nat.mul_add_mod, Nat.mod_eq_of_lt hiK]
  refine (succTime_le (r := j0 * K + i) ?_).trans ?_
  · simp only [restartSched, hr1, hr2]; exact hi
  calc ((j0 * K + i + 1 : ℕ) : ℝ≥0∞) ≤ ∑ j ∈ Finset.range (j0 + 1), (K : ℝ≥0∞) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        exact_mod_cast (by nlinarith : j0 * K + i + 1 ≤ (j0 + 1) * K)
    _ = ∑ j ∈ Finset.range (j0 + 1), (Set.pi (↑(Finset.range j)) fun _ => blockFail P K).indicator
        (fun _ => (K : ℝ≥0∞)) y := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Set.indicator_of_mem]
        intro i hi
        simp only [Finset.coe_range, Set.mem_Iio] at hi
        simp only [Finset.mem_range] at hj
        exact hmin i (by omega)
    _ ≤ _ := ENNReal.sum_le_tsum _

/-- The restarted simulation of a CD algorithm with expected time `≤ t` (on `P`) has expected
time `≤ 2 (2^{2t} - 1)` on `P` without collision detection. -/
theorem expTime_restart_le (D : Fin n → Measure (List Bool → Bool))
    [∀ v, IsProbabilityMeasure (D v)] (P : Finset (Fin n)) (t : ℕ)
    (ht : expTimeCD D P ≤ t) :
    expTime (fun v => (Measure.infinitePi fun _ : ℕ => D v).map (restartSched (2 ^ (2 * t) - 1))) P
      ≤ 2 * ((2 ^ (2 * t) - 1 : ℕ) : ℝ≥0∞) := by
  have ht1 : 1 ≤ t := by
    have := (one_le_expTimeCD D P).trans ht
    exact_mod_cast this
  set K := 2 ^ (2 * t) - 1 with hKdef
  have hK : 0 < K := by
    have : 2 ^ 1 < 2 ^ (2 * t) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  set G := blockFail P K
  set q := Measure.pi D G
  -- Markov: `q ≤ 1/2`
  have hq : q ≤ 2⁻¹ := by
    have hM : ((2 * t + 1 : ℕ) : ℝ≥0∞) * q ≤ t := (mul_measure_blockFail_le D P (2 * t)).trans ht
    have hq1 : q ≠ ⊤ := measure_ne_top _ _
    lift q to NNReal using hq1 with q' hq'
    have : ((2 * t + 1 : ℕ) : NNReal) * q' ≤ (t : NNReal) := by exact_mod_cast hM
    have : (q' : ℝ) ≤ 2⁻¹ := by
      have := NNReal.coe_le_coe.mpr this
      push_cast at this
      have ht0 : (1 : ℝ) ≤ t := by exact_mod_cast ht1
      nlinarith [q'.coe_nonneg]
    have h2 : q' ≤ 2⁻¹ := by
      rw [← NNReal.coe_le_coe]; simpa using this
    simpa using ENNReal.coe_le_coe.mpr h2
  have hgeom : (1 - q)⁻¹ ≤ 2 := by
    have : 2⁻¹ ≤ 1 - q := by
      calc (2⁻¹ : ℝ≥0∞) = 1 - 2⁻¹ := ENNReal.one_sub_inv_two.symm
        _ ≤ 1 - q := tsub_le_tsub_left hq 1
    simpa using ENNReal.inv_le_inv.mpr this
  -- the restarted execution, as a function of the swapped randomness
  set H : (ℕ → Fin n → List Bool → Bool) → ℝ≥0∞ := fun y =>
    ∑' j, (Set.pi (↑(Finset.range j)) fun _ => G).indicator (fun _ => (K : ℝ≥0∞)) y with hH
  have hboxes : ∀ j, MeasurableSet (Set.pi (↑(Finset.range j) : Set ℕ) fun _ => G) := fun j =>
    MeasurableSet.pi (Finset.countable_toSet _) fun _ _ => measurableSet_blockFail P K
  have hHm : Measurable H := Measurable.tsum fun j =>
    measurable_const.indicator (hboxes j)
  unfold expTime
  rw [← Measure.pi_map_pi (fun v => (measurable_restartSched K).aemeasurable)]
  have hmeas : Measurable fun (x : Fin n → ℕ → List Bool → Bool) v => restartSched K (x v) :=
    Measurable.of_eval fun v => (measurable_restartSched K).comp (measurable_pi_apply v)
  have hswap : Measurable fun (x : Fin n → ℕ → List Bool → Bool) (j : ℕ) (v : Fin n) => x v j := by
    fun_prop
  rw [lintegral_map (measurable_succTime P) hmeas]
  calc ∫⁻ x, succTime P (fun v => restartSched K (x v))
        ∂Measure.pi (fun v => Measure.infinitePi fun _ : ℕ => D v)
      ≤ ∫⁻ x, H (fun j v => x v j) ∂Measure.pi (fun v => Measure.infinitePi fun _ : ℕ => D v) :=
        lintegral_mono fun x => succTime_restart_le P hK (fun j v => x v j)
    _ = ∫⁻ y, H y ∂(Measure.pi (fun v => Measure.infinitePi fun _ : ℕ => D v)).map
          (fun x j v => x v j) := (lintegral_map hHm hswap).symm
    _ = ∫⁻ y, H y ∂Measure.infinitePi (fun _ : ℕ => Measure.pi D) := by
        rw [pi_infinitePi_map_swap]
    _ = ∑' j, (K : ℝ≥0∞) * q ^ j := by
        rw [hH, lintegral_tsum fun j => (measurable_const.indicator (hboxes j)).aemeasurable]
        congr 1; funext j
        rw [lintegral_indicator_const (hboxes j), Measure.infinitePi_pi _
          (fun _ _ => measurableSet_blockFail P K), Finset.prod_const, Finset.card_range]
    _ = K * (1 - q)⁻¹ := by rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
    _ ≤ K * 2 := by gcongr
    _ = 2 * K := mul_comm _ _


/-! ### The repaired lower bound -/

variable {A : Type*} [Fintype A] [Nonempty A]

/-- The no-CD algorithm with advice obtained from a CD algorithm with advice by simulating
independent restarts of the CD algorithm (block length `2^{2t} - 1`). -/
noncomputable def restartAlg (D : A → Fin n → Measure (List Bool → Bool)) (t : ℕ) (a : A)
    (v : Fin n) : Measure (ℕ → Bool) :=
  (Measure.infinitePi fun _ : ℕ => D a v).map (restartSched (2 ^ (2 * t) - 1))

instance (D : A → Fin n → Measure (List Bool → Bool)) [∀ a v, IsProbabilityMeasure (D a v)]
    (t : ℕ) (a : A) (v : Fin n) : IsProbabilityMeasure (restartAlg D t a v) := by
  unfold restartAlg; infer_instance

/-- **Theorem 3.7 of [Gilbert–Newport–Vaidya–Weaver, PODC 2021], lower bound, repaired**
(conditional on the lower bound of [18]): if a randomized algorithm *with* collision detection and
advice from `A` has expected time `≤ t` on every nonempty participant set, then
`c log₂ n ≤ |A| · 2^{2t+1}`. -/
theorem theorem_3_7_lower {c : ℝ} (hN : NewportBound n c)
    (D : A → Fin n → Measure (List Bool → Bool)) [∀ a v, IsProbabilityMeasure (D a v)]
    (f : Finset (Fin n) → A) (t : ℕ)
    (ht : ∀ P : Finset (Fin n), P.Nonempty → expTimeCD (D (f P)) P ≤ t) :
    ENNReal.ofReal (c * Real.logb 2 n) ≤ Fintype.card A * 2 ^ (2 * t + 1) := by
  obtain ⟨P, hP, h⟩ := theorem_3_6_lower hN (restartAlg D t) f
  rw [ENNReal.div_le_iff (by simp) (by simp)] at h
  refine h.trans ?_
  rw [mul_comm]
  gcongr
  refine (expTime_restart_le (D (f P)) P t (ht P hP)).trans ?_
  have : 2 * (2 ^ (2 * t) - 1) ≤ 2 ^ (2 * t + 1) := by rw [pow_succ]; omega
  exact_mod_cast this

/-- **Theorem 3.7, lower bound, repaired, with `b` bits of advice**: if a randomized CD algorithm
with `b`-bit advice has expected time `≤ t` on every nonempty participant set, then
`t ≥ (log₂ (c log₂ n) - b - 3) / 2`, i.e. `t = Ω(log log n - b)` for `b ≤ log log n - O(1)`.
(The paper claims `t ≥ log₂ (c log₂ n) - b`.) -/
theorem theorem_3_7_lower_bits {c : ℝ} (hc : 0 < c) (hn : 2 ≤ n) (hN : NewportBound n c) {b : ℕ}
    (D : Bits b → Fin n → Measure (List Bool → Bool)) [∀ a v, IsProbabilityMeasure (D a v)]
    (f : Finset (Fin n) → Bits b) (t : ℝ)
    (ht : ∀ P : Finset (Fin n), P.Nonempty → expTimeCD (D (f P)) P ≤ ENNReal.ofReal t) :
    Real.logb 2 (c * Real.logb 2 n) - b - 3 ≤ 2 * t := by
  have h0 : 0 ≤ t := by
    have hP : ({⟨0, by omega⟩} : Finset (Fin n)).Nonempty := Finset.singleton_nonempty _
    have := (one_le_expTimeCD _ _).trans (ht _ hP)
    rw [ENNReal.one_le_ofReal] at this
    linarith
  set T := ⌈t⌉₊
  have hT : (T : ℝ) < t + 1 := Nat.ceil_lt_add_one h0
  have h := theorem_3_7_lower hN D f T fun P hP =>
    (ht P hP).trans (by rw [← ENNReal.ofReal_natCast]; exact ENNReal.ofReal_le_ofReal (Nat.le_ceil t))
  rw [card_bits] at h
  have hlog : 0 < Real.logb 2 n := Real.logb_pos (by norm_num) (by exact_mod_cast hn)
  have hpos : 0 < c * Real.logb 2 n := mul_pos hc hlog
  have h' : c * Real.logb 2 n ≤ (2 : ℝ) ^ (b + (2 * T + 1)) := by
    have : ENNReal.ofReal (c * Real.logb 2 n) ≤
        ENNReal.ofReal (((2 ^ (b + (2 * T + 1)) : ℕ) : ℝ)) := by
      rw [ENNReal.ofReal_natCast, pow_add]
      push_cast at h ⊢
      exact h
    have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp this
    exact_mod_cast this
  have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hpos h'
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num)] at this
  push_cast at this
  linarith

end Podc.ContentionPredictions
