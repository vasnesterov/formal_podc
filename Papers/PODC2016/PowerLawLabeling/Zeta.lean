import Papers.PODC2016.PowerLawLabeling.Defs

/-!
# Analytic facts about `ζ(α)`, `C = 1/ζ(α)` and `i₁`

* `summable_zeta`, `one_le_zeta`, `C_pos`, `C_le_one`, `C_mul_zeta`;
* `sum_Icc_rpow_neg_le`: `∑_{i=k+1}^{N} i^{-α} ≤ k^{1-α}/(α-1)` (telescoping, no integrals);
* `C_mul_sum_Icc_le_one`, `one_sub_C_mul_sum_Icc_le`: `1 - C ∑_{i=1}^k i^{-α} ≤ C k^{1-α}/(α-1)`;
* facts about `i₁`: `i₁_spec`, `two_le_floor_of_lt_i₁`, `i₁_le`, `lt_i₁`.
-/

namespace Podc.PowerLawLabeling

open Finset

variable {α : ℝ}

theorem summable_zeta (hα : 1 < α) : Summable (fun i : ℕ => 1 / ((i : ℝ) + 1) ^ α) := by
  have := (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ) ^ α) 1).2
    (Real.summable_one_div_nat_rpow.2 hα)
  simpa using this

theorem one_le_zeta (hα : 1 < α) : 1 ≤ zeta α := by
  have h := (summable_zeta hα).le_tsum 0 (fun j _ => by positivity)
  simpa [zeta] using h

theorem zeta_pos (hα : 1 < α) : 0 < zeta α := lt_of_lt_of_le one_pos (one_le_zeta hα)

theorem C_pos (hα : 1 < α) : 0 < C α := by
  unfold C; exact div_pos one_pos (zeta_pos hα)

theorem C_le_one (hα : 1 < α) : C α ≤ 1 := by
  unfold C; rw [div_le_one (zeta_pos hα)]; exact one_le_zeta hα

theorem C_mul_zeta (hα : 1 < α) : C α * zeta α = 1 := by
  unfold C; field_simp [(zeta_pos hα).ne']

/-- One telescoping step: `(x+1)^{-α} ≤ (x^{1-α} - (x+1)^{1-α})/(α-1)` for `x > 0`. -/
theorem rpow_neg_le_sub_div (hα : 1 < α) {x : ℝ} (hx : 0 < x) :
    (x + 1) ^ (-α) ≤ (x ^ (1 - α) - (x + 1) ^ (1 - α)) / (α - 1) := by
  open Real in
  have hβ : 0 < α - 1 := by linarith
  have hx1 : 0 < x + 1 := by linarith
  have key : 1 + (α - 1) / (x + 1) ≤ ((x + 1) / x) ^ (α - 1) := by
    rw [Real.rpow_def_of_pos (div_pos hx1 hx)]
    have h1 := Real.add_one_le_exp (Real.log ((x + 1) / x) * (α - 1))
    have h2 := Real.one_sub_inv_le_log_of_pos (div_pos hx1 hx)
    have h3 : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by field_simp; ring
    rw [h3] at h2
    have : (α - 1) / (x + 1) ≤ Real.log ((x + 1) / x) * (α - 1) := by
      rw [div_eq_mul_one_div, mul_comm]; exact mul_le_mul_of_nonneg_right h2 hβ.le
    linarith
  rw [Real.div_rpow hx1.le hx.le] at key
  have e1 : (x + 1) ^ (-α) = 1 / ((x + 1) ^ (α - 1) * (x + 1)) := by
    rw [show -α = -(α - 1) - 1 by ring, Real.rpow_sub_one hx1.ne', Real.rpow_neg hx1.le]
    field_simp
  have e2 : x ^ (1 - α) = 1 / x ^ (α - 1) := by
    rw [show 1 - α = -(α - 1) by ring, Real.rpow_neg hx.le]; simp
  have e3 : (x + 1) ^ (1 - α) = 1 / (x + 1) ^ (α - 1) := by
    rw [show 1 - α = -(α - 1) by ring, Real.rpow_neg hx1.le]; simp
  rw [e1, e2, e3]
  generalize hA : (x + 1) ^ (α - 1) = A at *
  generalize hB : x ^ (α - 1) = B at *
  have hA0 : 0 < A := hA ▸ Real.rpow_pos_of_pos hx1 _
  have hB0 : 0 < B := hB ▸ Real.rpow_pos_of_pos hx _
  rw [le_div_iff₀ hB0] at key
  have k2 : (α - 1) * B ≤ (A - B) * (x + 1) := by
    have : (1 + (α - 1) / (x + 1)) * B * (x + 1) ≤ A * (x + 1) :=
      mul_le_mul_of_nonneg_right key hx1.le
    have e : (1 + (α - 1) / (x + 1)) * B * (x + 1) = B * (x + 1) + (α - 1) * B := by
      field_simp
    linarith
  rw [le_div_iff₀ hβ, div_sub_div _ _ hB0.ne' hA0.ne', div_mul_eq_mul_div,
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hA0 hB0]

theorem sum_Ioc_add_rpow_neg_le (hα : 1 < α) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    ∑ i ∈ Ioc k (k + N), (i : ℝ) ^ (-α) ≤
      ((k : ℝ) ^ (1 - α) - ((k + N : ℕ) : ℝ) ^ (1 - α)) / (α - 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [← add_assoc, sum_Ioc_succ_top (by omega)]
    have hx : (0 : ℝ) < ((k + N : ℕ) : ℝ) := by exact_mod_cast (show 0 < k + N by omega)
    have := rpow_neg_le_sub_div hα hx
    push_cast at this ih ⊢
    have e : ((k : ℝ) ^ (1 - α) - ((k : ℝ) + N + 1) ^ (1 - α)) / (α - 1) =
      ((k : ℝ) ^ (1 - α) - ((k : ℝ) + N) ^ (1 - α)) / (α - 1) +
        (((k : ℝ) + N) ^ (1 - α) - ((k : ℝ) + N + 1) ^ (1 - α)) / (α - 1) := by ring
    rw [e]; linarith

/-- Telescoping tail bound: `∑_{i=k+1}^{N} i^{-α} ≤ k^{1-α}/(α-1)` for `k ≥ 1`. -/
theorem sum_Ioc_rpow_neg_le (hα : 1 < α) {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    ∑ i ∈ Ioc k N, (i : ℝ) ^ (-α) ≤ (k : ℝ) ^ (1 - α) / (α - 1) := by
  have hβ : 0 < α - 1 := by linarith
  rcases le_or_gt N k with h | h
  · rw [Ioc_eq_empty (by omega), sum_empty]; positivity
  · obtain ⟨M, rfl⟩ : ∃ M, N = k + M := ⟨N - k, by omega⟩
    refine (sum_Ioc_add_rpow_neg_le hα hk M).trans ?_
    have : (0 : ℝ) ≤ ((k + M : ℕ) : ℝ) ^ (1 - α) := by positivity
    rw [div_le_div_iff_of_pos_right hβ]; linarith

theorem sum_Icc_eq_sum_range (k : ℕ) :
    ∑ i ∈ Icc 1 k, (i : ℝ) ^ (-α) = ∑ j ∈ range k, 1 / ((j : ℝ) + 1) ^ α := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  refine sum_congr (by simp) fun j _ => ?_
  rw [Real.rpow_neg (by positivity), one_div]; push_cast; ring_nf

/-- Partial sums of `C ∑ i^{-α}` are at most `1`. -/
theorem C_mul_sum_Icc_le_one (hα : 1 < α) (k : ℕ) :
    C α * ∑ i ∈ Icc 1 k, (i : ℝ) ^ (-α) ≤ 1 := by
  rw [sum_Icc_eq_sum_range]
  calc C α * ∑ j ∈ range k, 1 / ((j : ℝ) + 1) ^ α ≤ C α * zeta α :=
        mul_le_mul_of_nonneg_left
          ((summable_zeta hα).sum_le_tsum _ (fun _ _ => by positivity)) (C_pos hα).le
    _ = 1 := C_mul_zeta hα

/-- The tail of the normalised power law: `1 - C ∑_{i=1}^k i^{-α} ≤ C k^{1-α}/(α-1)`. -/
theorem one_sub_C_mul_sum_Icc_le (hα : 1 < α) {k : ℕ} (hk : 1 ≤ k) :
    1 - C α * ∑ i ∈ Icc 1 k, (i : ℝ) ^ (-α) ≤ C α * (k : ℝ) ^ (1 - α) / (α - 1) := by
  have hs := (summable_zeta hα).sum_add_tsum_nat_add k
  have htail : ∑' i : ℕ, 1 / (((i + k : ℕ) : ℝ) + 1) ^ α ≤ (k : ℝ) ^ (1 - α) / (α - 1) := by
    refine Real.tsum_le_of_sum_range_le (fun _ => by positivity) fun N => ?_
    refine le_trans (le_of_eq ?_) (sum_Ioc_rpow_neg_le hα hk (k + N))
    rw [← Finset.Ico_add_one_add_one_eq_Ioc, sum_Ico_eq_sum_range]
    refine sum_congr (by simp) fun j _ => ?_
    rw [Real.rpow_neg (by positivity), one_div]; push_cast; ring_nf
  rw [sum_Icc_eq_sum_range, mul_div_assoc, ← sub_nonneg]
  have h1 := C_mul_zeta hα
  unfold zeta at h1
  rw [← hs] at h1
  have hC := C_pos hα
  nlinarith [mul_le_mul_of_nonneg_left htail hC.le]

theorem floor_le_one_iff {x : ℝ} (hx : 0 ≤ x) : ⌊x⌋₊ ≤ 1 ↔ x < 2 := by
  rw [show (⌊x⌋₊ ≤ 1) ↔ ⌊x⌋₊ < 2 by omega, Nat.floor_lt hx]; norm_num

theorem C_mul_div_nonneg (hα : 1 < α) (n : ℕ) (i : ℕ) : 0 ≤ C α * n / (i : ℝ) ^ α :=
  div_nonneg (mul_nonneg (C_pos hα).le (Nat.cast_nonneg _)) (by positivity)

theorem mem_i₁_set (hα : 1 < α) (n : ℕ) {j : ℕ} (hj : 1 ≤ j) (h : C α * n / (j : ℝ) ^ α < 2) :
    j ∈ {i : ℕ | 1 ≤ i ∧ ⌊C α * n / (i : ℝ) ^ α⌋₊ ≤ 1} :=
  ⟨hj, (floor_le_one_iff (C_mul_div_nonneg hα n j)).2 h⟩

theorem i₁_set_nonempty (hα : 1 < α) (n : ℕ) :
    {i : ℕ | 1 ≤ i ∧ ⌊C α * n / (i : ℝ) ^ α⌋₊ ≤ 1}.Nonempty := by
  refine ⟨⌊(C α * n / 2) ^ (1 / α)⌋₊ + 1, mem_i₁_set hα n (by omega) ?_⟩
  have hα0 : 0 < α := by linarith
  have hy0 : 0 ≤ C α * n / 2 := by have := C_pos hα; positivity
  have hlt : (C α * n / 2) ^ (1 / α) < ((⌊(C α * n / 2) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  simp only [one_div] at hlt ⊢
  have := Real.rpow_lt_rpow (by positivity) hlt hα0
  rw [Real.rpow_inv_rpow hy0 hα0.ne'] at this
  rw [div_lt_iff₀ (by positivity)]; linarith

theorem one_le_i₁ (hα : 1 < α) (n : ℕ) : 1 ≤ i₁ α n :=
  (Nat.sInf_mem (i₁_set_nonempty hα n)).1

theorem i₁_spec (hα : 1 < α) (n : ℕ) : ⌊C α * n / (i₁ α n : ℝ) ^ α⌋₊ ≤ 1 :=
  (Nat.sInf_mem (i₁_set_nonempty hα n)).2

/-- `C n / i₁^α < 2`. -/
theorem C_mul_div_i₁_lt_two (hα : 1 < α) (n : ℕ) : C α * n / (i₁ α n : ℝ) ^ α < 2 :=
  (floor_le_one_iff (C_mul_div_nonneg hα n _)).1 (i₁_spec hα n)

theorem two_le_floor_of_lt_i₁ (hα : 1 < α) (n : ℕ) {i : ℕ} (hi : 1 ≤ i) (hi' : i < i₁ α n) :
    2 ≤ ⌊C α * n / (i : ℝ) ^ α⌋₊ := by
  have := Nat.notMem_of_lt_sInf hi'
  simp only [Set.mem_setOf_eq, not_and, not_le] at this
  exact this hi

theorem i₁_le (hα : 1 < α) (n : ℕ) : (i₁ α n : ℝ) ≤ (C α * n / 2) ^ (1 / α) + 1 := by
  have hα0 : 0 < α := by linarith
  have hy0 : 0 ≤ C α * n / 2 := by have := C_pos hα; positivity
  have hlt : (C α * n / 2) ^ (1 / α) < ((⌊(C α * n / 2) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
    push_cast; exact Nat.lt_floor_add_one _
  have hmem : ⌊(C α * n / 2) ^ (1 / α)⌋₊ + 1 ∈
      {i : ℕ | 1 ≤ i ∧ ⌊C α * n / (i : ℝ) ^ α⌋₊ ≤ 1} := by
    refine mem_i₁_set hα n (by omega) ?_
    simp only [one_div] at hlt ⊢
    have := Real.rpow_lt_rpow (by positivity) hlt hα0
    rw [Real.rpow_inv_rpow hy0 hα0.ne'] at this
    rw [div_lt_iff₀ (by positivity)]; linarith
  have h := Nat.sInf_le hmem
  have h' : (i₁ α n : ℝ) ≤ ((⌊(C α * n / 2) ^ (1 / α)⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast h
  push_cast at h'
  have := Nat.floor_le (show 0 ≤ (C α * n / 2) ^ (1 / α) by positivity)
  linarith

theorem lt_i₁ (hα : 1 < α) (n : ℕ) : (C α * n / 2) ^ (1 / α) < i₁ α n := by
  have hα0 : 0 < α := by linarith
  have h := C_mul_div_i₁_lt_two hα n
  have hi : (0 : ℝ) < (i₁ α n : ℝ) ^ α := by
    have := one_le_i₁ hα n; positivity
  rw [div_lt_iff₀ hi] at h
  have h2 : C α * n / 2 < (i₁ α n : ℝ) ^ α := by linarith
  have := Real.rpow_lt_rpow (by have := C_pos hα; positivity) h2 (by positivity : 0 < 1 / α)
  rw [one_div, Real.rpow_rpow_inv (by positivity) hα0.ne'] at this
  rwa [one_div]

/-- A crude uniform bound: `i₁ ≤ n^{1/α} + 1`. -/
theorem i₁_le_rpow_add_one (hα : 1 < α) (n : ℕ) : (i₁ α n : ℝ) ≤ (n : ℝ) ^ (1 / α) + 1 := by
  have hα0 : 0 < α := by linarith
  have hC := C_pos hα
  have hC1 := C_le_one hα
  have : (C α * n / 2) ^ (1 / α) ≤ (n : ℝ) ^ (1 / α) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith
  linarith [i₁_le hα n]

end Podc.PowerLawLabeling
