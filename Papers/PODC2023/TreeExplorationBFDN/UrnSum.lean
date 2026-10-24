import Mathlib

/-!
# The sum `S_k(Δ) = ∑_{u=1}^{k} min(Δ, ⌈k/u⌉)` and its logarithmic bounds

Cosson, Massoulié, Viennot, *Efficient Collaborative Tree Exploration with Breadth-First
Depth-Next* (PODC 2023; full version arXiv:2301.13307).

Both the balls-in-urns game (Theorem 3.1) and the per-depth bound on anchor assignments of BFDN
(Lemma 2 of the full version) reduce to the quantity
`urnSum k Δ = ∑_{u=1}^{k} min(Δ, ⌈k/u⌉)`: when `u` urns (anchors) are still alive and the loads
are balanced, the urn removed next carries at most `min(Δ, ⌈k/u⌉)` balls.

## Main results

* `urnSum_le`: `S_k(Δ) ≤ k (min(log Δ, log k) + 2)` (used for Lemma 2 / Theorem 2.1).
* `urnSum_sub_le`: `S_k(Δ) - k ≤ k min(log Δ, log k) + k` (used for Theorem 3.1).

`log` is the natural logarithm (`Real.log`, with `Real.log 0 = 0`).
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset

/-- `⌈k / u⌉` for natural numbers (`u ≥ 1`). -/
def ceilDiv (k u : ℕ) : ℕ := (k + u - 1) / u

/-- `S_k(Δ) = ∑_{u=1}^{k} min(Δ, ⌈k/u⌉)`. -/
def urnSum (k Δ : ℕ) : ℕ := ∑ u ∈ Icc 1 k, min Δ (ceilDiv k u)


/-- The concave primitive `G(y) = y` for `y ≤ 1`, `1 + log y` for `y ≥ 1` of `min(1, 1/y)`,
used to telescope `∑ min(Δ, k/u)`. -/
noncomputable def primG (y : ℝ) : ℝ := if y ≤ 1 then y else 1 + Real.log y

lemma primG_step {a b : ℝ} (_ha : 0 ≤ a) (hab : a ≤ b) (hb : 0 < b) :
    (b - a) * min 1 (1 / b) ≤ primG b - primG a := by
  unfold primG
  by_cases hb1 : b ≤ 1
  · have ha1 : a ≤ 1 := hab.trans hb1
    simp only [hb1, ha1, ↓reduceIte]
    have : min 1 (1 / b) ≤ 1 := min_le_left _ _
    nlinarith
  · push Not at hb1
    have hmin : min 1 (1 / b) = 1 / b := min_eq_right (by rw [div_le_one hb]; linarith)
    simp only [not_le.mpr hb1, ↓reduceIte, hmin]
    have hlogb := Real.one_sub_inv_le_log_of_pos hb
    have h1 : (b - a) * (1 / b) = 1 - a * b⁻¹ := by field_simp
    rw [h1]
    by_cases ha1 : a ≤ 1
    · simp only [ha1, ↓reduceIte]
      have hb' : b⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hb1.le
      have : a * (1 - b⁻¹) ≤ 1 - b⁻¹ := by nlinarith
      nlinarith
    · push Not at ha1
      simp only [not_le.mpr ha1, ↓reduceIte]
      have ha0 : 0 < a := by linarith
      have h := Real.log_le_sub_one_of_pos (div_pos ha0 hb)
      rw [Real.log_div ha0.ne' hb.ne', div_eq_mul_inv] at h
      linarith

lemma sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (g : ℕ → M) (n : ℕ) :
    ∑ u ∈ Icc 1 n, g u = ∑ i ∈ range n, g (i + 1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]

/-- `∑_{u=1}^{k} min(D, k/u) ≤ k (1 + log D)` for real `D ≥ 1`. -/
lemma sum_min_div_le {D : ℝ} (hD : 1 ≤ D) {k : ℕ} (hk : 1 ≤ k) :
    ∑ u ∈ Icc 1 k, min D ((k : ℝ) / u) ≤ k * (1 + Real.log D) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hD0 : 0 < D := by linarith
  set f : ℕ → ℝ := fun i => primG (i * D / k) with hf
  have hterm : ∀ i : ℕ, min D ((k : ℝ) / ((i + 1 : ℕ) : ℝ)) ≤ k * (f (i + 1) - f i) := by
    intro i
    have ha : 0 ≤ (i : ℝ) * D / k := by positivity
    have hab : (i : ℝ) * D / k ≤ ((i + 1 : ℕ) : ℝ) * D / k := by
      push_cast; gcongr; linarith
    have hb : 0 < ((i + 1 : ℕ) : ℝ) * D / k := by positivity
    have key := primG_step ha hab hb
    have h1 : ((i + 1 : ℕ) : ℝ) * D / k - i * D / k = D / k := by push_cast; ring
    rw [h1] at key
    have heq : (k : ℝ) * (D / k * min 1 (1 / (((i + 1 : ℕ) : ℝ) * D / k))) =
        min D ((k : ℝ) / ((i + 1 : ℕ) : ℝ)) := by
      rw [← mul_assoc, mul_div_cancel₀ _ hk0.ne', mul_min_of_nonneg _ _ hD0.le, mul_one]
      congr 1
      field_simp
    rw [← heq]
    simp only [hf]
    exact mul_le_mul_of_nonneg_left key hk0.le
  rw [sum_Icc_one_eq_sum_range]
  calc ∑ i ∈ range k, min D ((k : ℝ) / ((i + 1 : ℕ) : ℝ))
      ≤ ∑ i ∈ range k, (k : ℝ) * (f (i + 1) - f i) := sum_le_sum fun i _ => hterm i
    _ = k * (f k - f 0) := by rw [← mul_sum, sum_range_sub]
    _ = k * (1 + Real.log D) := by
      congr 1
      simp only [hf, primG]
      rw [mul_div_cancel_left₀ _ hk0.ne', Nat.cast_zero, zero_mul, zero_div]
      by_cases h : D ≤ 1
      · have : D = 1 := le_antisymm h hD
        subst this; simp
      · simp [h]

lemma ceilDiv_le_self (k u : ℕ) (hu : 1 ≤ u) : ceilDiv k u ≤ k := by
  unfold ceilDiv
  obtain ⟨u, rfl⟩ : ∃ u', u = u' + 1 := ⟨u - 1, by omega⟩
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · apply Nat.div_le_of_le_mul
    have : k + (u + 1) - 1 = k + u := by omega
    rw [this]; nlinarith

lemma ceilDiv_cast_le (k u : ℕ) (hu : 1 ≤ u) (huk : u ≤ k) :
    (ceilDiv k u : ℝ) ≤ k / u + (1 - 1 / k) := by
  unfold ceilDiv
  have hu0 : (0 : ℝ) < u := by exact_mod_cast hu
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (hu.trans huk)
  have hku : (u : ℝ) ≤ k := by exact_mod_cast huk
  calc (((k + u - 1) / u : ℕ) : ℝ) ≤ ((k + u - 1 : ℕ) : ℝ) / u := Nat.cast_div_le
    _ = (k + u - 1) / u := by rw [Nat.cast_sub (by omega)]; push_cast; ring
    _ = k / u + (1 - 1 / u) := by field_simp; ring
    _ ≤ k / u + (1 - 1 / k) := by gcongr

lemma le_mul_ceilDiv (k : ℕ) {u : ℕ} (hu : 0 < u) : k ≤ u * ceilDiv k u := by
  unfold ceilDiv
  have h := Nat.lt_mul_div_succ (k + u - 1) hu
  rw [Nat.mul_add, Nat.mul_one] at h
  omega

lemma ceilDiv_le_of_le_mul {k u q : ℕ} (hu : 0 < u) (h : k ≤ u * q) : ceilDiv k u ≤ q := by
  unfold ceilDiv
  have : (k + u - 1) / u < q + 1 := by
    rw [Nat.div_lt_iff_lt_mul hu, Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  omega

/-- `⌈k/u⌉` is antitone in `u ≥ 1`. -/
lemma ceilDiv_anti (k : ℕ) {u c : ℕ} (hu : 0 < u) (huc : u ≤ c) :
    ceilDiv k c ≤ ceilDiv k u :=
  ceilDiv_le_of_le_mul (hu.trans_le huc)
    ((le_mul_ceilDiv k hu).trans (Nat.mul_le_mul_right _ huc))

/-- If the values `f j` (`j ∈ s`) differ from `f i` by at most one downwards and sum to at most
`k`, then `f i ≤ ⌈k / |s|⌉`. -/
lemma le_ceilDiv_of_balanced {α : Type*} [DecidableEq α] {s : Finset α} {f : α → ℕ} {i : α}
    {k : ℕ} (hi : i ∈ s) (hbal : ∀ j ∈ s, f i ≤ f j + 1) (hsum : ∑ j ∈ s, f j ≤ k) :
    f i ≤ ceilDiv k s.card := by
  obtain ⟨L, hL⟩ : ∃ L, f i = L + 1 ∨ f i = 0 := ⟨f i - 1, by omega⟩
  rcases hL with hL | hL
  · have h1 : ∑ j ∈ s, (L + if j = i then 1 else 0) ≤ ∑ j ∈ s, f j := by
      apply sum_le_sum
      intro j hj
      have := hbal j hj
      split_ifs with h
      · subst h; omega
      · omega
    rw [sum_add_distrib, sum_ite_eq' s i] at h1
    simp only [hi, ↓reduceIte, sum_const, smul_eq_mul] at h1
    have hc : 0 < s.card := card_pos.mpr ⟨i, hi⟩
    unfold ceilDiv
    rw [Nat.le_div_iff_mul_le hc, hL, Nat.add_mul, Nat.one_mul, Nat.mul_comm]
    omega
  · rw [hL]; exact Nat.zero_le _

/-- Sharpened form: `S_k(Δ) + 1 ≤ k (min(log Δ, log k) + 2)` for `k, Δ ≥ 1`. -/
lemma urnSum_add_one_le {k Δ : ℕ} (hk : 1 ≤ k) (hΔ : 1 ≤ Δ) :
    (urnSum k Δ : ℝ) + 1 ≤ k * (min (Real.log Δ) (Real.log k) + 2) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  set D : ℝ := ((min Δ k : ℕ) : ℝ) with hDdef
  have hD : 1 ≤ D := by
    simp only [hDdef]; exact_mod_cast le_min hΔ hk
  have hlogD : Real.log D = min (Real.log Δ) (Real.log k) := by
    simp only [hDdef, Nat.cast_min]
    have hΔ0 : (0 : ℝ) < Δ := by exact_mod_cast hΔ
    rcases le_total Δ k with h | h
    · have h' : (Δ : ℝ) ≤ k := by exact_mod_cast h
      rw [min_eq_left h', min_eq_left (Real.log_le_log hΔ0 h')]
    · have h' : (k : ℝ) ≤ Δ := by exact_mod_cast h
      rw [min_eq_right h', min_eq_right (Real.log_le_log hk0 h')]
  have he : 0 ≤ 1 - 1 / (k : ℝ) := by
    have : 1 / (k : ℝ) ≤ 1 := by rw [div_le_one hk0]; exact_mod_cast hk
    linarith
  have hterm : ∀ u ∈ Icc 1 k,
      ((min Δ (ceilDiv k u) : ℕ) : ℝ) ≤ min D ((k : ℝ) / u) + (1 - 1 / k) := by
    intro u hu
    rw [mem_Icc] at hu
    have hc := ceilDiv_le_self k u hu.1
    have : min Δ (ceilDiv k u) = min (min Δ k) (ceilDiv k u) := by omega
    rw [this, Nat.cast_min]
    have h2 := ceilDiv_cast_le k u hu.1 hu.2
    rcases le_total D (k / u) with h | h
    · rw [min_eq_left h]; exact (min_le_left _ _).trans (by linarith)
    · rw [min_eq_right h]; exact (min_le_right _ _).trans h2
  have hsum := sum_min_div_le hD hk
  unfold urnSum
  rw [Nat.cast_sum]
  calc ∑ u ∈ Icc 1 k, ((min Δ (ceilDiv k u) : ℕ) : ℝ) + 1
      ≤ ∑ u ∈ Icc 1 k, (min D ((k : ℝ) / u) + (1 - 1 / k)) + 1 := by
        gcongr with u hu; exact hterm u hu
    _ = ∑ u ∈ Icc 1 k, min D ((k : ℝ) / u) + k * (1 - 1 / k) + 1 := by
        rw [sum_add_distrib]; simp; ring
    _ ≤ k * (1 + Real.log D) + k * (1 - 1 / k) + 1 := by linarith
    _ = k * (min (Real.log Δ) (Real.log k) + 2) := by
        rw [← hlogD]; field_simp; ring

/-- `S_k(Δ) ≤ k (min(log Δ, log k) + 2)`. -/
theorem urnSum_le (k Δ : ℕ) :
    (urnSum k Δ : ℝ) ≤ k * (min (Real.log Δ) (Real.log k) + 2) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [urnSum]
  rcases Nat.eq_zero_or_pos Δ with rfl | hΔ
  · have : urnSum k 0 = 0 := by simp [urnSum]
    rw [this]
    have hlog : 0 ≤ Real.log (k : ℝ) := Real.log_natCast_nonneg k
    simp only [Nat.cast_zero, Real.log_zero, min_eq_left hlog]
    positivity
  linarith [urnSum_add_one_le hk hΔ]

/-- `S_k(Δ) - k ≤ k min(log Δ, log k) + k`. -/
theorem urnSum_sub_le (k Δ : ℕ) :
    (urnSum k Δ : ℝ) - k ≤ k * min (Real.log Δ) (Real.log k) + k := by
  linarith [urnSum_le k Δ]

end Podc.TreeExplorationBFDN
