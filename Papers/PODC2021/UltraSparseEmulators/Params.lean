import Mathlib

/-!
# Parameters of the centralized construction (Section 2.1.2, Lemmas 2.6, 2.12, eqs. (1), (5), (12), (13))

Elkin, Matar. *Ultra-Sparse Near-Additive Emulators.* PODC 2021 (arXiv:2106.01036v1).

* `R ε i`: the radius bounds, `R_0 = 0`, `R_{i+1} = 2δ_i + R_i = 2(1/ε)^i + 5R_i`.
* `δ ε i = (1/ε)^i + 2R_i`: the distance thresholds.
* `segLen ε i = ⌊(1/ε)^i⌋`: the segment length in the proof of Lemma 2.10.
* `beta ε i`, `alpha ε i`: the stretch parameters, `β_0 = 0`, `α_0 = 1`,
  `β_i = 2β_{i-1} + 6R_i`, `α_i = α_{i-1} + ε^i/(1-ε^i) · β_i`.
* `numPhases κ = ⌈log₂((κ+1)/2)⌉` (the paper's `ℓ`) and `deg κ n i = n^{2^i/κ}`.
-/

namespace Podc.UltraSparseEmulators

open Real Finset

variable (ε : ℝ)

/-- The radius bound `R_i` of Section 2.1.2: `R_0 = 0`, `R_{i+1} = 2(1/ε)^i + 5R_i`
(equivalently `R_{i+1} = 2δ_i + R_i`, see `R_succ`). -/
noncomputable def R : ℕ → ℝ
  | 0 => 0
  | i + 1 => 2 * (1 / ε) ^ i + 5 * R i

/-- The distance threshold `δ_i = (1/ε)^i + 2R_i` of Section 2.1.2. -/
noncomputable def δ (i : ℕ) : ℝ := (1 / ε) ^ i + 2 * R ε i

/-- The segment length `⌊(1/ε)^i⌋` used in the proof of Lemma 2.10. -/
noncomputable def segLen (i : ℕ) : ℕ := ⌊(1 / ε) ^ i⌋₊

/-- The additive stretch `β_i` of Lemma 2.10: `β_0 = 0`, `β_i = 2β_{i-1} + 6R_i`. -/
noncomputable def beta : ℕ → ℝ
  | 0 => 0
  | i + 1 => 2 * beta i + 6 * R ε (i + 1)

/-- The multiplicative stretch `α_i` of Lemma 2.10: `α_0 = 1`,
`α_i = α_{i-1} + ε^i/(1-ε^i) · β_i`. -/
noncomputable def alpha : ℕ → ℝ
  | 0 => 1
  | i + 1 => alpha i + ε ^ (i + 1) / (1 - ε ^ (i + 1)) * beta ε (i + 1)

/-- The number of the last phase, `ℓ = ⌈log₂((κ+1)/2)⌉` (Section 2.1.2). -/
noncomputable def numPhases (κ : ℝ) : ℕ := ⌈logb 2 ((κ + 1) / 2)⌉₊

/-- The degree parameter `deg_i = n^{2^i/κ}` (Section 2.1.2). -/
noncomputable def deg (κ : ℝ) (n : ℕ) (i : ℕ) : ℝ := (n : ℝ) ^ ((2 : ℝ) ^ i / κ)

variable {ε}

/-! ### Elementary facts -/

lemma R_zero : R ε 0 = 0 := rfl

lemma R_succ (i : ℕ) : R ε (i + 1) = 2 * δ ε i + R ε i := by
  simp only [R, δ]; ring

lemma R_nonneg (hε : 0 < ε) (i : ℕ) : 0 ≤ R ε i := by
  induction i with
  | zero => simp [R]
  | succ i ih =>
    simp only [R]
    have : 0 ≤ (1 / ε) ^ i := pow_nonneg (by positivity) _
    linarith

/-- `(1/ε)^i ≥ 1` for `0 < ε ≤ 1`. -/
lemma one_le_inv_pow (hε0 : 0 < ε) (hε1 : ε ≤ 1) (i : ℕ) : 1 ≤ (1 / ε) ^ i :=
  one_le_pow₀ (by rw [le_div_iff₀ hε0]; linarith)

lemma R_le_R_succ (hε : 0 < ε) (i : ℕ) : R ε i ≤ R ε (i + 1) := by
  have h1 := R_nonneg hε i
  have : 0 ≤ (1 / ε) ^ i := pow_nonneg (by positivity) _
  simp only [R]; linarith

lemma R_mono (hε0 : 0 < ε) (_hε1 : ε ≤ 1) : Monotone (R ε) :=
  monotone_nat_of_le_succ (R_le_R_succ hε0)

/-- Used in the proof of Lemma 2.10 (before eq. (9)): `3R_j + 1 ≤ R_i` for `j < i`. -/
lemma three_R_add_one_le (hε0 : 0 < ε) (hε1 : ε ≤ 1) {i j : ℕ} (hji : j < i) :
    3 * R ε j + 1 ≤ R ε i := by
  have h1 : 3 * R ε j + 1 ≤ R ε (j + 1) := by
    have := one_le_inv_pow hε0 hε1 j
    have := R_nonneg hε0 j
    simp only [R]; linarith
  exact h1.trans (R_mono hε0 hε1 hji)

lemma one_le_segLen (hε0 : 0 < ε) (hε1 : ε ≤ 1) (i : ℕ) : 1 ≤ segLen ε i := by
  unfold segLen
  exact Nat.le_floor (by simpa using one_le_inv_pow hε0 hε1 i)

lemma segLen_add_le_δ (hε0 : 0 < ε) (i : ℕ) : (segLen ε i : ℝ) + 2 * R ε i ≤ δ ε i := by
  unfold segLen δ
  have := Nat.floor_le (pow_nonneg (le_of_lt (one_div_pos.mpr hε0)) i)
  linarith

lemma two_R_add_one_le_δ (hε0 : 0 < ε) (hε1 : ε ≤ 1) (i : ℕ) : 2 * R ε i + 1 ≤ δ ε i := by
  unfold δ
  have := one_le_inv_pow hε0 hε1 i
  linarith

/-- `q ≤ ⌈d/⌊(1/ε)^i⌋⌉ ≤ ⌈dε^i/(1-ε^i)⌉` in the proof of Lemma 2.10. -/
lemma inv_segLen_le (hε0 : 0 < ε) (hε1 : ε < 1) {i : ℕ} (hi : 1 ≤ i) :
    1 / (segLen ε i : ℝ) ≤ ε ^ i / (1 - ε ^ i) := by
  have hεi : 0 < ε ^ i := pow_pos hε0 i
  have hεi1 : ε ^ i < 1 := pow_lt_one₀ hε0.le hε1 (by omega)
  have hx : (1 / ε) ^ i = 1 / ε ^ i := by rw [one_div_pow]
  have hlt := Nat.lt_floor_add_one ((1 / ε) ^ i)
  rw [hx] at hlt
  unfold segLen
  rw [hx]
  set m := ⌊1 / ε ^ i⌋₊
  have h1 : 1 < 1 / ε ^ i := by rw [lt_div_iff₀ hεi]; linarith
  have hm : (0 : ℝ) < m := by
    have : 1 ≤ m := Nat.le_floor (by simpa using h1.le)
    exact_mod_cast this
  rw [div_le_div_iff₀ hm (by linarith)]
  have : 1 < (m + 1) * ε ^ i := by
    have := mul_lt_mul_of_pos_right hlt hεi
    rwa [div_mul_cancel₀ _ hεi.ne'] at this
  nlinarith

lemma beta_nonneg (hε : 0 < ε) (i : ℕ) : 0 ≤ beta ε i := by
  induction i with
  | zero => simp [beta]
  | succ i ih =>
    simp only [beta]
    have := R_nonneg hε (i + 1)
    linarith

lemma one_le_alpha (hε0 : 0 < ε) (hε1 : ε < 1) (i : ℕ) : 1 ≤ alpha ε i := by
  induction i with
  | zero => simp [alpha]
  | succ i ih =>
    simp only [alpha]
    have h1 : ε ^ (i + 1) < 1 := pow_lt_one₀ hε0.le hε1 (by omega)
    have : 0 ≤ ε ^ (i + 1) / (1 - ε ^ (i + 1)) * beta ε (i + 1) :=
      mul_nonneg (div_nonneg (pow_nonneg hε0.le _) (by linarith)) (beta_nonneg hε0 _)
    linarith

/-! ### Lemma 2.6, eq. (5) -/

/-- **Lemma 2.6.** `R_i = 2 · Σ_{j=0}^{i-1} ε^{-j} · 5^{i-1-j}`. -/
theorem lemma_2_6 (i : ℕ) :
    R ε i = 2 * ∑ j ∈ range i, (1 / ε) ^ j * 5 ^ (i - 1 - j) := by
  induction i with
  | zero => simp [R]
  | succ i ih =>
    rw [R, ih, sum_range_succ, mul_add, mul_sum, mul_sum, mul_sum]
    have : ∀ j ∈ range i, 5 * (2 * ((1 / ε) ^ j * 5 ^ (i - 1 - j))) =
        2 * ((1 / ε) ^ j * 5 ^ (i + 1 - 1 - j)) := by
      intro j hj
      have hj := mem_range.mp hj
      rw [show i + 1 - 1 - j = (i - 1 - j) + 1 by omega, pow_succ]; ring
    rw [sum_congr rfl this]
    simp; ring

/-- **Eq. (5).** For `ε ≤ 1/10` and `i ≥ 1`, `R_i ≤ 4(1/ε)^{i-1}`. -/
theorem eq_5 (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {i : ℕ} (hi : 1 ≤ i) :
    R ε i ≤ 4 * (1 / ε) ^ (i - 1) := by
  induction i, hi using Nat.le_induction with
  | base => simp [R]; norm_num
  | succ i hi ih =>
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    rw [R]
    have hp : 0 ≤ (1 / ε) ^ k := pow_nonneg (by positivity) _
    have h10 : 10 ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
    rw [pow_succ]
    nlinarith

/-! ### Lemma 2.12, eqs. (12), (13) -/

/-- **Lemma 2.12.** `β_i = Σ_{j=0}^{i} 2^{i-j} · 6R_j`. -/
theorem lemma_2_12 (i : ℕ) :
    beta ε i = ∑ j ∈ range (i + 1), 2 ^ (i - j) * (6 * R ε j) := by
  induction i with
  | zero => simp [beta, R]
  | succ i ih =>
    rw [beta, ih, sum_range_succ _ (i + 1), mul_sum]
    have : ∀ j ∈ range (i + 1), 2 * (2 ^ (i - j) * (6 * R ε j)) =
        2 ^ (i + 1 - j) * (6 * R ε j) := by
      intro j hj
      have hj := mem_range.mp hj
      rw [show i + 1 - j = (i - j) + 1 by omega, pow_succ]; ring
    rw [sum_congr rfl this]
    simp

/-- **Eq. (12).** For `ε ≤ 1/10` and `i ≥ 1`, `β_i ≤ 30(1/ε)^{i-1}`. -/
theorem eq_12 (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) {i : ℕ} (hi : 1 ≤ i) :
    beta ε i ≤ 30 * (1 / ε) ^ (i - 1) := by
  induction i, hi using Nat.le_induction with
  | base => simp [beta, R]; norm_num
  | succ i hi ih =>
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at ih ⊢
    have hR := eq_5 hε0 hε (i := k + 2) (by omega)
    simp only [show k + 2 - 1 = k + 1 by omega] at hR
    rw [beta]
    have hp : 0 ≤ (1 / ε) ^ k := pow_nonneg (by positivity) _
    have h10 : 10 ≤ 1 / ε := by rw [le_div_iff₀ hε0]; linarith
    rw [pow_succ] at hR ⊢
    nlinarith

/-- **Eq. (13)** (stated with `=` in the paper; it is an upper bound). For `ε ≤ 1/10`,
`α_i ≤ 1 + 34εi`. -/
theorem eq_13 (hε0 : 0 < ε) (hε : ε ≤ 1 / 10) (i : ℕ) : alpha ε i ≤ 1 + 34 * ε * i := by
  induction i with
  | zero => simp [alpha]
  | succ i ih =>
    rw [alpha]
    have hb := eq_12 hε0 hε (i := i + 1) (by omega)
    simp only [Nat.add_sub_cancel] at hb
    have hpos : 0 < ε ^ (i + 1) := pow_pos hε0 _
    have hle : ε ^ (i + 1) ≤ ε := pow_le_of_le_one hε0.le (by linarith) (by omega)
    have hden : 9 / 10 ≤ 1 - ε ^ (i + 1) := by linarith
    have hprod : ε ^ (i + 1) * (1 / ε) ^ i = ε := by
      rw [one_div_pow, pow_succ]; field_simp
    have key : ε ^ (i + 1) * beta ε (i + 1) ≤ 30 * ε := by
      calc ε ^ (i + 1) * beta ε (i + 1) ≤ ε ^ (i + 1) * (30 * (1 / ε) ^ i) :=
            mul_le_mul_of_nonneg_left hb hpos.le
        _ = 30 * ε := by rw [mul_left_comm, hprod]
    have : ε ^ (i + 1) / (1 - ε ^ (i + 1)) * beta ε (i + 1) ≤ 34 * ε := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
      nlinarith
    push_cast
    linarith

/-! ### The number of phases and the degree sequence (eq. (1), Lemma 2.3) -/

lemma one_le_numPhases {κ : ℝ} (hκ : 2 ≤ κ) : 1 ≤ numPhases κ := by
  unfold numPhases
  rw [Nat.one_le_iff_ne_zero, Ne, Nat.ceil_eq_zero, not_le]
  exact logb_pos (by norm_num) (by linarith)

/-- `(κ+1)/2 ≤ 2^ℓ`, the defining property of the ceiling `ℓ = ⌈log₂((κ+1)/2)⌉`. -/
lemma half_succ_le_two_pow_numPhases {κ : ℝ} (hκ : 0 < κ) :
    (κ + 1) / 2 ≤ (2 : ℝ) ^ numPhases κ := by
  have h := Nat.le_ceil (logb 2 ((κ + 1) / 2))
  rw [logb_le_iff_le_rpow (by norm_num) (by linarith)] at h
  simpa [numPhases, Real.rpow_natCast] using h

/-- Section 2.2.4 for integer `κ` (the paper's setting `κ = 1, 2, …`):
`⌈log₂((κ+1)/2)⌉ ≤ log₂ κ`, equivalently `2^ℓ ≤ κ`. -/
lemma two_pow_numPhases_le_natCast {k : ℕ} (hk : 2 ≤ k) : 2 ^ numPhases k ≤ k := by
  have hm := one_le_numPhases (κ := k) (by exact_mod_cast hk)
  have hlt : ((numPhases k - 1 : ℕ) : ℝ) < logb 2 (((k : ℝ) + 1) / 2) :=
    Nat.lt_ceil.mp (by unfold numPhases at hm ⊢; omega)
  rw [lt_logb_iff_rpow_lt (by norm_num) (by positivity), Real.rpow_natCast] at hlt
  have h2 : (2 : ℝ) ^ numPhases k < k + 1 := by
    rw [show numPhases k = (numPhases k - 1) + 1 by omega, pow_succ]; linarith
  have h3 : 2 ^ numPhases k < k + 1 := by exact_mod_cast h2
  omega

lemma numPhases_le_logb_natCast {k : ℕ} (hk : 2 ≤ k) :
    (numPhases k : ℝ) ≤ logb 2 k := by
  rw [le_logb_iff_rpow_le (by norm_num) (by positivity), Real.rpow_natCast]
  exact_mod_cast two_pow_numPhases_le_natCast hk

/-- The claim `⌈log₂((κ+1)/2)⌉ ≤ log₂ κ` of Section 2.2.4 fails for non-integer `κ`: for `κ = 7/2`,
`⌈log₂(9/4)⌉ = 2 > log₂(7/2)`. -/
lemma numPhases_seven_halves : numPhases (7 / 2) = 2 := by
  unfold numPhases
  rw [Nat.ceil_eq_iff (by norm_num)]
  constructor
  · rw [lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num
  · rw [logb_le_iff_le_rpow (by norm_num) (by norm_num)]; norm_num

lemma logb_seven_halves_lt_two : logb 2 (7 / 2 : ℝ) < 2 := by
  rw [logb_lt_iff_lt_rpow (by norm_num) (by norm_num)]; norm_num

lemma not_numPhases_le_logb : ¬ ((numPhases (7 / 2) : ℝ) ≤ logb 2 (7 / 2)) := by
  rw [numPhases_seven_halves]
  have := logb_seven_halves_lt_two
  push_cast
  linarith

/-- Eq. (1): `n^{1-(2^ℓ-1)/κ} ≤ n^{2^ℓ/κ} = deg_ℓ`. -/
lemma eq_1 {κ : ℝ} (hκ : 2 ≤ κ) {n : ℕ} (hn : 1 ≤ n) :
    (n : ℝ) ^ (1 - ((2 : ℝ) ^ numPhases κ - 1) / κ) ≤ deg κ n (numPhases κ) := by
  unfold deg
  have hκ0 : 0 < κ := by linarith
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
  have h := half_succ_le_two_pow_numPhases hκ0
  rw [← sub_nonneg]
  have : (2 : ℝ) ^ numPhases κ / κ - (1 - ((2 : ℝ) ^ numPhases κ - 1) / κ) =
      (2 * (2 : ℝ) ^ numPhases κ - 1 - κ) / κ := by field_simp; ring
  rw [this]
  apply div_nonneg _ hκ0.le
  linarith

lemma one_le_deg {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : 1 ≤ n) (i : ℕ) : 1 ≤ deg κ n i := by
  unfold deg
  exact Real.one_le_rpow (by exact_mod_cast hn) (by positivity)

lemma deg_succ {κ : ℝ} (n i : ℕ) : deg κ n (i + 1) = deg κ n i ^ 2 := by
  unfold deg
  rw [show (2 : ℝ) ^ (i + 1) / κ = 2 ^ i / κ * ((2 : ℕ) : ℝ) by push_cast; ring,
    Real.rpow_mul_natCast (Nat.cast_nonneg n)]

lemma deg_zero {κ : ℝ} (n : ℕ) : deg κ n 0 = (n : ℝ) ^ (1 / κ) := by
  simp [deg]

/-- The induction step of Lemma 2.3: if `|P_{i+1}| (deg_i + 1) ≤ |P_i| ≤ n^{1-(2^i-1)/κ}` then
`|P_{i+1}| ≤ n^{1-(2^{i+1}-1)/κ}`. -/
lemma lemma_2_3_step {κ : ℝ} (hκ : 0 < κ) {n : ℕ} (hn : 1 ≤ n) {i : ℕ} {a b : ℝ} (hb : 0 ≤ b)
    (hba : b * (deg κ n i + 1) ≤ a) (ha : a ≤ (n : ℝ) ^ (1 - ((2 : ℝ) ^ i - 1) / κ)) :
    b ≤ (n : ℝ) ^ (1 - ((2 : ℝ) ^ (i + 1) - 1) / κ) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hd := one_le_deg hκ hn i
  have hsplit : (n : ℝ) ^ (1 - ((2 : ℝ) ^ i - 1) / κ) =
      (n : ℝ) ^ (1 - ((2 : ℝ) ^ (i + 1) - 1) / κ) * deg κ n i := by
    unfold deg
    rw [← Real.rpow_add hn0]
    congr 1
    field_simp
    ring
  have hpos : 0 < (n : ℝ) ^ (1 - ((2 : ℝ) ^ (i + 1) - 1) / κ) := Real.rpow_pos_of_pos hn0 _
  have h1 : b * deg κ n i ≤ (n : ℝ) ^ (1 - ((2 : ℝ) ^ (i + 1) - 1) / κ) * deg κ n i := by
    nlinarith
  exact le_of_mul_le_mul_right h1 (by linarith)

/-! ### Rescaling (Section 2.2.4) -/

/-- **Rescaling** (Section 2.2.4), under the hypothesis `ℓ ≤ log₂ κ` (which holds for integer
`κ ≥ 2`, `numPhases_le_logb_natCast`, but not for every real `κ ≥ 2`, `not_numPhases_le_logb`). Run the construction with
`ε₀ = ε/(34ℓ)`. Then `ε₀ ≤ 1/10`, `1 + 34ε₀ℓ = 1 + ε`, and
`30(1/ε₀)^{ℓ-1} ≤ 30(34 log₂ κ / ε)^{log₂ κ - 1}`. -/
theorem rescale_of_numPhases_le {κ : ℝ} (hκ : 2 ≤ κ) (hℓ : (numPhases κ : ℝ) ≤ logb 2 κ)
    (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < ε / (34 * numPhases κ) ∧ ε / (34 * numPhases κ) ≤ 1 / 10 ∧
    1 + 34 * (ε / (34 * numPhases κ)) * numPhases κ = 1 + ε ∧
    30 * (1 / (ε / (34 * numPhases κ))) ^ (numPhases κ - 1) ≤
      30 * (34 * logb 2 κ / ε) ^ (logb 2 κ - 1) := by
  have hm := one_le_numPhases hκ
  have hm' : (1 : ℝ) ≤ numPhases κ := by exact_mod_cast hm
  have h34 : (0 : ℝ) < 34 * numPhases κ := by positivity
  refine ⟨div_pos hε0 h34, ?_, ?_, ?_⟩
  · rw [div_le_iff₀ h34]; linarith
  · field_simp
  · have hinv : 1 / (ε / (34 * numPhases κ)) = 34 * numPhases κ / ε := by
      field_simp
    rw [hinv]
    gcongr 30 * ?_
    have hbase : 1 ≤ 34 * logb 2 κ / ε := by
      rw [le_div_iff₀ hε0]; linarith
    calc (34 * (numPhases κ : ℝ) / ε) ^ (numPhases κ - 1)
        ≤ (34 * logb 2 κ / ε) ^ (numPhases κ - 1) := by gcongr
      _ = (34 * logb 2 κ / ε) ^ (((numPhases κ - 1 : ℕ) : ℝ)) := (Real.rpow_natCast _ _).symm
      _ ≤ (34 * logb 2 κ / ε) ^ (logb 2 κ - 1) := by
        apply Real.rpow_le_rpow_of_exponent_le hbase
        rw [Nat.cast_sub hm]; push_cast; linarith

/-- **Rescaling** (Section 2.2.4) for integer `κ ≥ 2`, the paper's setting. -/
theorem rescale_natCast {k : ℕ} (hk : 2 ≤ k) (hε0 : 0 < ε) (hε1 : ε < 1) :
    0 < ε / (34 * numPhases k) ∧ ε / (34 * numPhases k) ≤ 1 / 10 ∧
    1 + 34 * (ε / (34 * numPhases k)) * numPhases k = 1 + ε ∧
    30 * (1 / (ε / (34 * numPhases k))) ^ (numPhases k - 1) ≤
      30 * (34 * logb 2 k / ε) ^ (logb 2 k - 1) :=
  rescale_of_numPhases_le (by exact_mod_cast hk) (numPhases_le_logb_natCast hk) hε0 hε1

/-- The last bound of `rescale_of_numPhases_le` fails without `ℓ ≤ log₂ κ`: `κ = 7/2`, `ε = 1/2`:
`30 · 136 > 30 · (68 log₂(7/2))^{log₂(7/2) - 1}`. -/
lemma not_rescale_seven_halves :
    ¬ (30 * (1 / ((1 / 2 : ℝ) / (34 * numPhases (7 / 2)))) ^ (numPhases (7 / 2) - 1) ≤
      30 * (34 * logb 2 (7 / 2) / (1 / 2)) ^ (logb 2 (7 / 2 : ℝ) - 1)) := by
  rw [numPhases_seven_halves]
  have hL := logb_seven_halves_lt_two
  have hL1 : 1 < logb 2 (7 / 2 : ℝ) := by
    rw [lt_logb_iff_rpow_lt (by norm_num) (by norm_num)]; norm_num
  have hbase : 1 ≤ 34 * logb 2 (7 / 2 : ℝ) / (1 / 2) := by linarith
  have h : (34 * logb 2 (7 / 2 : ℝ) / (1 / 2)) ^ (logb 2 (7 / 2 : ℝ) - 1) ≤
      34 * logb 2 (7 / 2 : ℝ) / (1 / 2) := by
    conv_rhs => rw [← Real.rpow_one (34 * logb 2 (7 / 2 : ℝ) / (1 / 2))]
    exact Real.rpow_le_rpow_of_exponent_le hbase (by linarith)
  norm_num
  linarith

end Podc.UltraSparseEmulators
