import Papers.PODC2022.DominatingSetArboricity.Deterministic

/-!
# The gap in the proof of Theorem 1.3

Theorem 1.3 claims an expected approximation factor `Δ^{1/k}(Δ^{1/k}+1)(k+1)` in `O(k²)` rounds.
The proof applies Lemma 4.6 with `γ = Δ^{1/k}`, `λ = 1/(Δ+1)`, which gives the factor
`γ(γ+1)⌈log_γ(Δ+1)⌉`; but `⌈log_γ(Δ+1)⌉ = ⌈k log_Δ(Δ+1)⌉ ≤ k + 1` only when
`(Δ+1)^k ≤ Δ^{k+1}` (and `γ > 1` needs `Δ ≥ 2`).

* `logb_gap`: for `Δ = 2`, `k = 2`: `⌈log_{√2} 3⌉ = 4 > k + 1 = 3`, so the proof only gives
  `(2+√2)·4 ≈ 13.7`, not the claimed `(2+√2)·3 ≈ 10.2`.
* The statement is nevertheless true: in the remaining regime `(Δ+1)^k > Δ^{k+1}` the claimed
  factor is at least `Δ + 1` (`claimed_factor_ge`), and the trivial one-round algorithm "every node
  picks a minimum-weight node of `N⁺_v`" is a `(Δ+1)`-approximation (`trivial_approx`).
-/

set_option linter.unusedSectionVars false

namespace DominatingSetArboricity

open Finset SimpleGraph

/-- For `Δ = 2`, `k = 2`: `⌈log_{2^{1/2}} 3⌉ = 4`. -/
theorem logb_gap : ⌈Real.logb ((2 : ℝ) ^ (1 / (2 : ℝ))) 3⌉₊ = 4 := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : Real.logb ((2 : ℝ) ^ (1 / (2 : ℝ))) 3 = 2 * (Real.log 3 / Real.log 2) := by
    rw [Real.logb, Real.log_rpow (by norm_num)]
    field_simp
  rw [hb, Nat.ceil_eq_iff (by norm_num)]
  have e8 : Real.log ((2 : ℝ) ^ 3) = 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have e9 : Real.log ((3 : ℝ) ^ 2) = 2 * Real.log 3 := by rw [Real.log_pow]; norm_num
  have e16 : Real.log ((2 : ℝ) ^ 4) = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have h8 : 3 * Real.log 2 < 2 * Real.log 3 := by
    rw [← e8, ← e9]; exact Real.log_lt_log (by norm_num) (by norm_num)
  have h16 : 2 * Real.log 3 ≤ 4 * Real.log 2 := by
    rw [← e9, ← e16]; exact Real.log_le_log (by norm_num) (by norm_num)
  constructor
  · norm_num
    rw [mul_div_assoc', lt_div_iff₀ hl2]
    linarith
  · rw [mul_div_assoc', div_le_iff₀ hl2]
    push_cast
    linarith

/-- In the regime `(Δ+1)^k > Δ^{k+1}` not covered by the proof, the claimed factor
`Δ^{1/k}(Δ^{1/k}+1)(k+1)` is at least `Δ + 1`. -/
theorem claimed_factor_ge {Δ k : ℕ} (hΔ : 1 ≤ Δ) (hk : 1 ≤ k)
    (hgap : (Δ : ℝ) ^ (k + 1) < ((Δ : ℝ) + 1) ^ k) :
    (Δ : ℝ) + 1 ≤ (Δ : ℝ) ^ (1 / (k : ℝ)) * ((Δ : ℝ) ^ (1 / (k : ℝ)) + 1) * (k + 1) := by
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hγ : 1 ≤ (Δ : ℝ) ^ (1 / (k : ℝ)) := Real.one_le_rpow hΔr (by positivity)
  -- `k ≥ Δ`: otherwise `(1 + 1/Δ)^k ≤ e^{k/Δ} ≤ e^{1 - 1/Δ} ≤ Δ`
  have hkΔ : (Δ : ℝ) ≤ k := by
    by_contra hlt
    push Not at hlt
    have hkint : k + 1 ≤ Δ := by exact_mod_cast hlt
    have hpos : (0 : ℝ) < Δ := by linarith
    -- `(Δ+1)^k = Δ^k (1+1/Δ)^k ≤ Δ^k · e^{k/Δ}` and `e^{k/Δ} ≤ e^{(Δ-1)/Δ} ≤ Δ`
    have h1 : ((Δ : ℝ) + 1) ^ k ≤ (Δ : ℝ) ^ k * Real.exp (k / Δ) := by
      have : ((Δ : ℝ) + 1) = Δ * (1 + 1 / Δ) := by field_simp
      rw [this, mul_pow]
      gcongr
      calc (1 + 1 / (Δ : ℝ)) ^ k ≤ Real.exp (1 / Δ) ^ k := by
            gcongr; linarith [Real.add_one_le_exp (1 / (Δ : ℝ))]
        _ = Real.exp (k / Δ) := by rw [← Real.exp_nat_mul]; ring_nf
    have h2 : Real.exp (k / Δ) ≤ Δ := by
      have hk' : (k : ℝ) ≤ Δ - 1 := by
        have : ((k + 1 : ℕ) : ℝ) ≤ Δ := by exact_mod_cast hkint
        push_cast at this; linarith
      have hlog : 1 - 1 / (Δ : ℝ) ≤ Real.log Δ := by
        have := Real.add_one_le_exp (-Real.log Δ)
        rw [Real.exp_neg, Real.exp_log hpos] at this
        have : 1 / (Δ : ℝ) = (Δ : ℝ)⁻¹ := one_div _
        linarith
      calc Real.exp (k / Δ) ≤ Real.exp (1 - 1 / Δ) := by
            gcongr
            rw [div_le_iff₀ hpos, sub_mul, one_div_mul_cancel hpos.ne']; linarith
        _ ≤ Real.exp (Real.log Δ) := Real.exp_le_exp.2 hlog
        _ = Δ := Real.exp_log hpos
    have : ((Δ : ℝ) + 1) ^ k ≤ (Δ : ℝ) ^ (k + 1) := by
      calc ((Δ : ℝ) + 1) ^ k ≤ (Δ : ℝ) ^ k * Real.exp (k / Δ) := h1
        _ ≤ (Δ : ℝ) ^ k * Δ := by gcongr
        _ = (Δ : ℝ) ^ (k + 1) := by ring
    linarith
  have h2 : 2 ≤ (Δ : ℝ) ^ (1 / (k : ℝ)) * ((Δ : ℝ) ^ (1 / (k : ℝ)) + 1) := by nlinarith
  have hk0 : (0 : ℝ) ≤ k + 1 := by positivity
  nlinarith

/-- The trivial one-round algorithm (every vertex adds a minimum-weight vertex of `N⁺_v`, i.e.
`completion G w ∅`) is a dominating set of weight at most `(Δ+1)` times the weight of any
dominating set. -/
theorem trivial_approx {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {D : Finset V} (hD : IsDominating G D) :
    IsDominating G (completion G w ∅) ∧
      wt w (completion G w ∅) ≤ (G.maxDegree + 1) * wt w D := by
  refine ⟨by simpa using isDominating_union_completion (G := G) w ∅, ?_⟩
  have hI := inv_init (G := G) hw 1
  have hpack : IsPacking G w (init G w).x := ⟨hI.nonneg, hI.feas⟩
  have hdual := sum_le_wt_of_isPacking G hpack hD
  calc wt w (completion G w ∅) ≤ ∑ v ∈ univ.filter (fun v => v ∉ dom G ∅), tau G w v :=
        wt_completion_le hw ∅
    _ ≤ ∑ v, tau G w v := sum_le_sum_of_subset_of_nonneg (subset_univ _)
        fun v _ _ => le_inf' _ _ fun u _ => hw u
    _ = (G.maxDegree + 1) * ∑ v, (init G w).x v := by
        rw [mul_sum]; refine sum_congr rfl fun v _ => ?_
        simp only [init]; field_simp
    _ ≤ (G.maxDegree + 1) * wt w D := by gcongr

end DominatingSetArboricity
