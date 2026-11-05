import Papers.PODC2010.ModularConsensus.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Recomposing consensus (Section 4)

The consensus object `U = A₋₁; A₀; C₁; A₁; C₂; A₂; …` (Section 4.1.1) and its truncation
`B = (A₋₁; A₀; C₁; A₁; …; C_k; A_k; K)` (Section 4.1.2), at the level of input/output behaviours
(`DObj`, see `Basic.lean`).

An execution of an (infinite) chain `X 0; X 1; X 2; …` of deciding objects (`ChainExec`) consists
of an execution of every stage `j`, where the participants of stage `j + 1` are processes that
adopted at stage `j`, with the adopted value as input. A process *decides* `v` if it commits `v`
at some stage.

## Main results

* `ChainExec.validity`, `ChainExec.agreement` — **safety of `U` and `B`** (Section 4.1): if every
  stage is a weak consensus object (validity and coherence), then decisions are inputs and no
  two processes decide differently (the paper derives this from Theorem 4 applied to the prefix in
  which everybody commits; we prove it directly for the whole chain);
* `ChainExec.no_next_of_agreement` — the deterministic half of the termination argument: if the
  outputs of stage `j` (a conciliator) agree and stage `j + 1` (an adopt-commit object) is
  convergent, every process that reaches stage `j + 1` commits there, so nobody reaches stage
  `j + 2`;
* `ChainExec.no_next_of_commit` — the fast path `A₋₁; A₀`: once a process commits at stage `j`,
  everybody commits at stage `j + 1` if it is convergent (with `fastPath` in `FastPath.lean`, a
  process that finishes `A₋₁` before any process with a different input arrives commits);
* `stages_prob` — the probabilistic half, abstractly: if the probability of reaching conciliator
  stage `k + 1` is at most `(1 - δ)` times that of reaching stage `k`, then the chain terminates
  with probability 1 and the expected number of conciliator stages is at most `1 / δ`
  (hence `E[T(U)] ≤ 2T(A) + (1/δ)(T(C) + T(A))`, `expected_cost_le`).
-/

namespace Podc.ModularConsensus

variable {P V : Type}

/-- An execution of the chain `X 0; X 1; X 2; …` with inputs `inp`. -/
structure ChainExec (X : ℕ → DObj P V) (inp : P → Option V) where
  /-- The inputs of stage `j`. -/
  i : ℕ → P → Option V
  /-- The outputs of stage `j`. -/
  o : ℕ → P → Option (Decision × V)
  /-- Every stage behaves as its object. -/
  exec : ∀ j, X j (i j) (o j)
  /-- Stage `0` gets the inputs of the chain. -/
  init : i 0 = inp
  /-- Only processes that adopted `v` at stage `j` invoke stage `j + 1`, with input `v`. -/
  link : ∀ j p v, i (j + 1) p = some v → o j p = some (.adopt, v)

namespace ChainExec

variable {X : ℕ → DObj P V} {inp : P → Option V}

/-- Process `p` decides `v`: it commits `v` at some stage. -/
def Decides (E : ChainExec X inp) (p : P) (v : V) : Prop := ∃ j, E.o j p = some (.commit, v)

/-- Every input of stage `j` is the input of some process. -/
lemma input_valid (E : ChainExec X inp) (hv : ∀ j, (X j).Valid) :
    ∀ j p v, E.i j p = some v → ∃ q, inp q = some v := by
  intro j
  induction j with
  | zero => intro p v h; exact ⟨p, E.init ▸ h⟩
  | succ j ih =>
    intro p v h
    obtain ⟨q, hq⟩ := hv j _ _ (E.exec j) p _ _ (E.link j p v h)
    exact ih q v hq

/-- **Validity of `U`.** If every stage satisfies validity, every decision is an input. -/
theorem validity (E : ChainExec X inp) (hv : ∀ j, (X j).Valid) {p : P} {v : V}
    (h : E.Decides p v) : ∃ q, inp q = some v := by
  obtain ⟨j, hj⟩ := h
  obtain ⟨q, hq⟩ := hv j _ _ (E.exec j) p _ _ hj
  exact E.input_valid hv j q v hq

/-- Once a process commits `v` at stage `j`, every output of every later stage has value `v`
(coherence of stage `j`, then validity of the following stages). -/
lemma later_outputs (E : ChainExec X inp) (hv : ∀ j, (X j).Valid) (hc : ∀ j, (X j).Coherent)
    {p : P} {j : ℕ} {v : V} (hp : E.o j p = some (.commit, v)) :
    ∀ n q d w, E.o (j + n) q = some (d, w) → w = v := by
  intro n
  induction n with
  | zero => intro q d w h; exact hc j _ _ (E.exec j) p q v d w hp h
  | succ n ih =>
    intro q d w h
    obtain ⟨q', hq'⟩ := hv (j + n + 1) _ _ (E.exec (j + n + 1)) q d w h
    exact ih q' .adopt w (E.link (j + n) q' w hq')

/-- **Agreement of `U`.** If every stage satisfies validity and coherence (weak consensus
objects: conciliators and adopt-commit objects), no two processes decide differently. -/
theorem agreement (E : ChainExec X inp) (hv : ∀ j, (X j).Valid) (hc : ∀ j, (X j).Coherent)
    {p q : P} {v w : V} (hp : E.Decides p v) (hq : E.Decides q w) : v = w := by
  obtain ⟨j, hj⟩ := hp
  obtain ⟨j', hj'⟩ := hq
  rcases le_total j j' with h | h
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    exact (E.later_outputs hv hc hj n q _ w hj').symm
  · obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le h
    exact E.later_outputs hv hc hj' n p _ v hj

/-- If all inputs of a convergent stage are equal, nobody proceeds past it. -/
lemma no_next_of_inputs_eq (E : ChainExec X inp) {j : ℕ} (hconv : (X j).Convergent) {v : V}
    (h : ∀ p x, E.i j p = some x → x = v) : ∀ p, E.i (j + 1) p = none := by
  intro p
  by_contra hne
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hne
  have := hconv _ _ (E.exec j) v h p _ _ (E.link j p x hx)
  exact absurd this.1 (by simp)

/-- **Termination, deterministic half.** If the outputs of stage `j` agree (the conciliator
`C_i` produced agreement) and stage `j + 1` is convergent (an adopt-commit object), then every
process reaching stage `j + 1` commits there: nobody reaches stage `j + 2`. -/
theorem no_next_of_agreement (E : ChainExec X inp) {j : ℕ} (hag : Agreement (E.o j))
    (hconv : (X (j + 1)).Convergent) : ∀ p, E.i (j + 2) p = none := by
  intro p
  by_contra hne
  obtain ⟨x, hx⟩ := Option.ne_none_iff_exists'.1 hne
  obtain ⟨v, hv⟩ : ∃ v, ∀ q z, E.i (j + 1) q = some z → z = v := by
    by_cases hex : ∃ q₀ x₀, E.i (j + 1) q₀ = some x₀
    · obtain ⟨q₀, x₀, h₀⟩ := hex
      exact ⟨x₀, fun q z hz => hag q q₀ _ _ z x₀ (E.link j q z hz) (E.link j q₀ x₀ h₀)⟩
    · push Not at hex
      exact ⟨x, fun q z hz => absurd hz (hex q z)⟩
  exact absurd (hconv _ _ (E.exec (j + 1)) v hv p _ _ (E.link (j + 1) p x hx)).1 (by simp)

/-- **Fast path.** If some process commits `v` at stage `j` and stage `j + 1` is convergent,
then every process reaching stage `j + 1` commits there. With `A₋₁; A₀` and `fastPath`, a
process that finishes `A₋₁` before any process with a different input arrives commits, and then
everybody commits in `A₀`, without running a conciliator. -/
theorem no_next_of_commit (E : ChainExec X inp) (hv : ∀ j, (X j).Valid)
    (hc : ∀ j, (X j).Coherent) {p : P} {j : ℕ} {v : V} (hp : E.o j p = some (.commit, v))
    (hconv : (X (j + 1)).Convergent) : ∀ q, E.i (j + 2) q = none :=
  E.no_next_of_inputs_eq hconv (v := v) fun q x hx =>
    E.later_outputs hv hc hp 0 q .adopt x (E.link j q x hx)

end ChainExec

/-! ### The probabilistic half (abstract) -/

open MeasureTheory ENNReal

/-- **Termination with probability 1 and the expected number of stages.** Let `E k` be the event
that some process reaches conciliator stage `k` (so `E (k + 1) ⊆ E k`). If, whenever stage `k`
is reached, its conciliator fails to produce agreement with probability at most `1 - δ`
(so that `μ (E (k + 1)) ≤ (1 - δ) μ (E k)` by `ChainExec.no_next_of_agreement`), then
`μ (E k) ≤ (1 - δ)^k`, the chain terminates with probability 1, and the expected number of
conciliator stages reached is at most `1 / δ`. -/
theorem stages_prob {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Set Ω) {δ : ℝ≥0∞} (hδ0 : δ ≠ 0) (hδ1 : δ ≤ 1)
    (hE : ∀ k, μ (E (k + 1)) ≤ (1 - δ) * μ (E k)) :
    (∀ k, μ (E k) ≤ (1 - δ) ^ k) ∧ μ (⋂ k, E k) = 0 ∧ ∑' k, μ (E k) ≤ δ⁻¹ := by
  have hk : ∀ k, μ (E k) ≤ (1 - δ) ^ k := by
    intro k
    induction k with
    | zero => simpa using prob_le_one
    | succ k ih =>
      calc μ (E (k + 1)) ≤ (1 - δ) * μ (E k) := hE k
        _ ≤ (1 - δ) * (1 - δ) ^ k := by gcongr
        _ = (1 - δ) ^ (k + 1) := by ring
  have hlt : 1 - δ < 1 := ENNReal.sub_lt_self one_ne_top one_ne_zero hδ0
  refine ⟨hk, ?_, ?_⟩
  · refine le_antisymm ?_ (zero_le)
    refine le_of_forall_pos_le_add fun ε hε _ => ?_
    have htend := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hlt
    obtain ⟨k, hk'⟩ := (htend.eventually (gt_mem_nhds (show (0 : ℝ≥0∞) < ε from ENNReal.coe_pos.2 hε))).exists
    calc μ (⋂ k, E k) ≤ μ (E k) := measure_mono (Set.iInter_subset _ k)
      _ ≤ (1 - δ) ^ k := hk k
      _ ≤ 0 + ε := by rw [zero_add]; exact hk'.le
  · calc ∑' k, μ (E k) ≤ ∑' k, (1 - δ) ^ k := ENNReal.tsum_le_tsum hk
      _ = (1 - (1 - δ))⁻¹ := ENNReal.tsum_geometric _
      _ = δ⁻¹ := by rw [ENNReal.sub_sub_cancel one_ne_top hδ1]

/-- **Expected cost of `U`** (Section 4.1.1): if the cost of an execution is at most
`2 T(A) + N (T(C) + T(A))`, where `N = ∑ₖ 1_{E (k+1)}` is the number of conciliator stages
reached, then `E[T(U)] ≤ 2 T(A) + (1/δ)(T(C) + T(A))`. -/
theorem expected_cost_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (E : ℕ → Set Ω) (hmeas : ∀ k, MeasurableSet (E k)) {δ : ℝ≥0∞} (hδ0 : δ ≠ 0) (hδ1 : δ ≤ 1)
    (hE : ∀ k, μ (E (k + 1)) ≤ (1 - δ) * μ (E k)) (T : Ω → ℝ≥0∞) (TA TC : ℝ≥0∞)
    (hT : ∀ ω, T ω ≤ 2 * TA + (∑' k, (E (k + 1)).indicator 1 ω) * (TC + TA)) :
    ∫⁻ ω, T ω ∂μ ≤ 2 * TA + δ⁻¹ * (TC + TA) := by
  obtain ⟨-, -, hsum⟩ := stages_prob μ E hδ0 hδ1 hE
  have hN : ∫⁻ ω, ∑' k, (E (k + 1)).indicator 1 ω ∂μ = ∑' k, μ (E (k + 1)) := by
    rw [lintegral_tsum (fun k => (measurable_one.indicator (hmeas _)).aemeasurable)]
    congr 1; funext k
    rw [lintegral_indicator_one (hmeas _)]
  have hsum' : ∑' k, μ (E (k + 1)) ≤ δ⁻¹ := by
    refine le_trans (ENNReal.tsum_le_tsum fun k => ?_) hsum
    calc μ (E (k + 1)) ≤ (1 - δ) * μ (E k) := hE k
      _ ≤ 1 * μ (E k) := by gcongr; exact tsub_le_self
      _ = μ (E k) := one_mul _
  have hmN : Measurable fun ω => ∑' k, (E (k + 1)).indicator (1 : Ω → ℝ≥0∞) ω :=
    Measurable.tsum fun k => measurable_one.indicator (hmeas _)
  calc ∫⁻ ω, T ω ∂μ ≤ ∫⁻ ω, 2 * TA + (∑' k, (E (k + 1)).indicator 1 ω) * (TC + TA) ∂μ :=
        lintegral_mono hT
    _ = 2 * TA + (∑' k, μ (E (k + 1))) * (TC + TA) := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_mul_const _ hmN, hN]
    _ ≤ 2 * TA + δ⁻¹ * (TC + TA) := by gcongr

/-- **Expected cost of the bounded construction `B`** (Section 4.1.2): if the cost of an execution
is at most `2 T(A) + N (T(C) + T(A)) + 1_{E (k+1)} T(K)`, where `E (k + 1)` is the event that the
fallback consensus protocol `K` is reached (after `k` conciliator stages), then
`E[T(B)] ≤ 2 T(A) + (1/δ)(T(C) + T(A)) + (1 - δ)^(k+1) T(K)`. -/
theorem expected_cost_bounded_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : ℕ → Set Ω) (hmeas : ∀ k, MeasurableSet (E k)) {δ : ℝ≥0∞}
    (hδ0 : δ ≠ 0) (hδ1 : δ ≤ 1) (hE : ∀ k, μ (E (k + 1)) ≤ (1 - δ) * μ (E k)) (k : ℕ)
    (T : Ω → ℝ≥0∞) (TA TC TK : ℝ≥0∞)
    (hT : ∀ ω, T ω ≤ 2 * TA + (∑' j, (E (j + 1)).indicator 1 ω) * (TC + TA) +
      (E (k + 1)).indicator (fun _ => TK) ω) :
    ∫⁻ ω, T ω ∂μ ≤ 2 * TA + δ⁻¹ * (TC + TA) + (1 - δ) ^ (k + 1) * TK := by
  obtain ⟨hk, -, -⟩ := stages_prob μ E hδ0 hδ1 hE
  have h1 := expected_cost_le μ E hmeas hδ0 hδ1 hE
    (fun ω => 2 * TA + (∑' j, (E (j + 1)).indicator 1 ω) * (TC + TA)) TA TC (fun _ => le_rfl)
  have hmN : Measurable fun ω => 2 * TA + (∑' j, (E (j + 1)).indicator (1 : Ω → ℝ≥0∞) ω) *
      (TC + TA) :=
    measurable_const.add
      ((Measurable.tsum fun j => measurable_one.indicator (hmeas _)).mul_const _)
  calc ∫⁻ ω, T ω ∂μ ≤ ∫⁻ ω, (2 * TA + (∑' j, (E (j + 1)).indicator 1 ω) * (TC + TA)) +
        (E (k + 1)).indicator (fun _ => TK) ω ∂μ := lintegral_mono hT
    _ = ∫⁻ ω, 2 * TA + (∑' j, (E (j + 1)).indicator 1 ω) * (TC + TA) ∂μ + TK * μ (E (k + 1)) := by
        rw [lintegral_add_left hmN, lintegral_indicator_const (hmeas _)]
    _ ≤ 2 * TA + δ⁻¹ * (TC + TA) + (1 - δ) ^ (k + 1) * TK := by
        rw [mul_comm TK]
        gcongr
        exact hk _

/-- Choice of `k` in Theorem 5: if `T(K) ≤ M` (e.g. `M = n^c` for the polynomial-work protocol
of [5]) then `k = ⌈ln M / δ⌉ = O(log n)` conciliator stages make the fallback term
`(1 - δ)^k T(K)` at most `1`. -/
theorem exists_k_fallback_le_one {δ M : ℝ} (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hM : 1 ≤ M) :
    (1 - δ) ^ (Nat.ceil (Real.log M / δ)) * M ≤ 1 := by
  set k := Nat.ceil (Real.log M / δ)
  have hM0 : 0 < M := by linarith
  have h1 : (1 - δ) ^ k ≤ Real.exp (-δ * k) := by
    rw [show -δ * (k : ℝ) = k * (-δ) by ring, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-δ)]) k
  have h2 : Real.log M ≤ δ * k := by
    have := Nat.le_ceil (Real.log M / δ)
    rw [div_le_iff₀ hδ0] at this; linarith
  have h3 : Real.exp (-δ * k) * M ≤ 1 := by
    rw [← Real.exp_log hM0, ← Real.exp_add]
    exact Real.exp_le_one_iff.2 (by linarith)
  calc (1 - δ) ^ k * M ≤ Real.exp (-δ * k) * M := by gcongr
    _ ≤ 1 := h3

end Podc.ModularConsensus
