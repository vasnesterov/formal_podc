import Papers.PODC2012.WirelessPacketScheduling.Model

/-!
# Numerical facts for the counterexample to Theorem 1

Network: `m = |E| = 200` links, `5100` packets per link, `n = 1 020 000`, `I = 5100`, `φ = 1`.
Then `85 < χ < 86`, `ψ₁ = 60`, `ξ = 1` and `2φχ log n < 5100` for `log = log₂` and `log = ln`.
-/

namespace Podc.WirelessPacketScheduling

lemma log_two_bounds : 0.6931471803 < Real.log 2 ∧ Real.log 2 < 0.6931471808 :=
  ⟨Real.log_two_gt_d9, Real.log_two_lt_d9⟩

/-- `5.26 < ln 200 < 5.33`, from `ln 200 = 8 ln 2 + ln (200/256)`. -/
lemma log_200_bounds : 5.26 < Real.log 200 ∧ Real.log 200 < 5.33 := by
  have h256 : Real.log 256 = 8 * Real.log 2 := by
    rw [show (256 : ℝ) = 2 ^ 8 by norm_num, Real.log_pow]; norm_num
  have hsplit : Real.log 200 = Real.log 256 + Real.log (200 / 256) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 200 / 256 by norm_num)
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 200 / 256 by norm_num)
  obtain ⟨l1, l2⟩ := log_two_bounds
  constructor
  · rw [hsplit, h256]; norm_num at h2; linarith
  · rw [hsplit, h256]; norm_num at h1; linarith

lemma chi_200_bounds : 85 < chi 200 ∧ chi 200 < 86 := by
  obtain ⟨h1, h2⟩ := log_200_bounds
  unfold chi
  push_cast
  constructor <;> linarith

lemma psi_200_5100_one : psi 200 5100 1 = 60 := by
  obtain ⟨h1, h2⟩ := chi_200_bounds
  unfold psi
  rw [Nat.ceil_eq_iff (by norm_num)]
  have hc : 0 < chi 200 := by linarith
  norm_num
  constructor
  · rw [lt_div_iff₀ hc]; linarith
  · rw [div_le_iff₀ hc]; linarith

/-- `19 < log₂ 1 020 000 < 20`. -/
lemma logb_two_n_bounds : 19 < Real.logb 2 (1020000 : ℕ) ∧ Real.logb 2 (1020000 : ℕ) < 20 := by
  constructor
  · rw [Real.lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num
  · rw [Real.logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]; norm_num

/-- `13.8 < ln 1 020 000 < 13.9`. -/
lemma log_n_bounds : 13.8 < Real.log (1020000 : ℕ) ∧ Real.log (1020000 : ℕ) < 13.9 := by
  have h20 : Real.log (2 ^ 20) = 20 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hsplit : Real.log (1020000 : ℕ) = Real.log (2 ^ 20) + Real.log (1020000 / 2 ^ 20) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h1 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1020000 / 2 ^ 20 by norm_num)
  have h2 := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 1020000 / 2 ^ 20 by norm_num)
  obtain ⟨l1, l2⟩ := log_two_bounds
  constructor
  · rw [hsplit, h20]; norm_num at h2; linarith
  · rw [hsplit, h20]; norm_num at h1; linarith

lemma finalParam_two_bounds :
    3230 < finalParam 2 200 1020000 1 ∧ finalParam 2 200 1020000 1 < 3440 := by
  obtain ⟨c1, c2⟩ := chi_200_bounds
  obtain ⟨l1, l2⟩ := logb_two_n_bounds
  unfold finalParam
  constructor
  · nlinarith [mul_pos (sub_pos.2 c1) (sub_pos.2 l1)]
  · nlinarith [mul_pos (sub_pos.2 c2) (sub_pos.2 l2)]

lemma finalParam_e_bounds :
    2346 < finalParam (Real.exp 1) 200 1020000 1 ∧ finalParam (Real.exp 1) 200 1020000 1 < 2391 := by
  obtain ⟨c1, c2⟩ := chi_200_bounds
  obtain ⟨l1, l2⟩ := log_n_bounds
  unfold finalParam
  rw [Real.logb, Real.log_exp, div_one]
  norm_num at l1 l2 ⊢
  constructor
  · nlinarith [mul_pos (sub_pos.2 c1) (sub_pos.2 l1)]
  · nlinarith [mul_pos (sub_pos.2 c2) (sub_pos.2 l2)]

lemma xi_two : xi 2 200 1020000 5100 1 = 1 := by
  obtain ⟨f1, f2⟩ := finalParam_two_bounds
  unfold xi
  rw [show 2 * 1 * chi 200 * Real.logb 2 (1020000 : ℕ) = finalParam 2 200 1020000 1 by
    unfold finalParam; ring]
  rw [Int.ceil_eq_iff]
  have hf : 0 < finalParam 2 200 1020000 1 := by linarith
  constructor
  · norm_num
    apply Real.logb_pos (by norm_num)
    rw [one_lt_div hf]; linarith
  · norm_num
    rw [Real.logb_le_iff_le_rpow (by norm_num) (by positivity)]
    rw [div_le_iff₀ hf]; norm_num; linarith

lemma xi_e : xi (Real.exp 1) 200 1020000 5100 1 = 1 := by
  obtain ⟨f1, f2⟩ := finalParam_e_bounds
  unfold xi
  rw [show 2 * 1 * chi 200 * Real.logb (Real.exp 1) (1020000 : ℕ) =
      finalParam (Real.exp 1) 200 1020000 1 by unfold finalParam; ring]
  rw [Int.ceil_eq_iff]
  have hf : 0 < finalParam (Real.exp 1) 200 1020000 1 := by linarith
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  constructor
  · norm_num
    apply Real.logb_pos (by linarith)
    rw [one_lt_div hf]; linarith
  · norm_num
    rw [Real.logb_le_iff_le_rpow (by linarith) (by positivity), Real.rpow_one]
    rw [div_le_iff₀ hf]; nlinarith

end Podc.WirelessPacketScheduling
