import Mathlib

/-!
# The write probabilities of Algorithm 1 and their sum

Algorithm 1 of *Simple and Efficient Randomized Wait-Free Locks* (PODC 2026), line 6, writes with
probability `eps b = 1 / (7 b log₂² (b + 1))` after observing contention `b`.

This file proves the elementary analytic facts used in the paper's analysis:

* `eps_pos`, `eps_nonneg`, `eps_le_one`, `eps_le_seventh`, `eps_antitone`: basic bounds;
* `sum_eps_le_half`: `∑_{i ≥ 1} eps i ≤ 1/2` (in fact `≤ 3/7`);
* `sum_eps_le_of_rank`, `sum_eps_le_half_of_rank`: if every element `x` of a finite set `S` observes
  contention `b x` at least its rank (one plus the number of elements with smaller key), then
  `∑_{x ∈ S} eps (b x) ≤ 1/2`.
-/

namespace Podc.RandomizedWaitFreeLocks

/-- The write probability of Algorithm 1 (line 6) after observing contention `b`:
`ε(b) = 1 / (7 b log₂² (b + 1))`. For `b = 0` it is `0` (division by zero). -/
noncomputable def eps (b : ℕ) : ℝ := 1 / (7 * b * (Real.logb 2 (b + 1)) ^ 2)

lemma one_le_logb_two_add_one {b : ℕ} (hb : 1 ≤ b) : 1 ≤ Real.logb 2 ((b : ℝ) + 1) := by
  have h2 : (2 : ℝ) ≤ (b : ℝ) + 1 := by
    have : (1 : ℝ) ≤ b := by exact_mod_cast hb
    linarith
  calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
    _ ≤ Real.logb 2 ((b : ℝ) + 1) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) h2

lemma eps_denom_ge {b : ℕ} (hb : 1 ≤ b) : 7 ≤ 7 * (b : ℝ) * (Real.logb 2 (b + 1)) ^ 2 := by
  have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have h2 := one_le_logb_two_add_one hb
  have h3 : (1 : ℝ) ≤ (Real.logb 2 ((b : ℝ) + 1)) ^ 2 := one_le_pow₀ h2
  nlinarith

lemma eps_pos {b : ℕ} (hb : 1 ≤ b) : 0 < eps b := by
  unfold eps
  have := eps_denom_ge hb
  positivity

lemma eps_nonneg (b : ℕ) : 0 ≤ eps b := by
  unfold eps
  have : (0 : ℝ) ≤ b := b.cast_nonneg
  positivity

lemma eps_le_seventh (b : ℕ) : eps b ≤ 1 / 7 := by
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [eps]
  · unfold eps
    exact one_div_le_one_div_of_le (by norm_num) (eps_denom_ge hb)

lemma eps_le_one (b : ℕ) : eps b ≤ 1 :=
  (eps_le_seventh b).trans (by norm_num)

lemma eps_antitone {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) : eps b ≤ eps a := by
  unfold eps
  have hden := eps_denom_ge ha
  apply one_div_le_one_div_of_le (by linarith)
  have h1 : (a : ℝ) ≤ b := by exact_mod_cast hab
  have h0 : (0 : ℝ) ≤ a := a.cast_nonneg
  have hl0 : 0 ≤ Real.logb 2 ((a : ℝ) + 1) := by
    linarith [one_le_logb_two_add_one ha]
  have hl : Real.logb 2 ((a : ℝ) + 1) ≤ Real.logb 2 ((b : ℝ) + 1) :=
    Real.logb_le_logb_of_le (by norm_num) (by positivity) (by linarith)
  have hsq : (Real.logb 2 ((a : ℝ) + 1)) ^ 2 ≤ (Real.logb 2 ((b : ℝ) + 1)) ^ 2 :=
    pow_le_pow_left₀ hl0 hl 2
  have : (a : ℝ) * (Real.logb 2 ((a : ℝ) + 1)) ^ 2 ≤ b * (Real.logb 2 ((b : ℝ) + 1)) ^ 2 :=
    mul_le_mul h1 hsq (by positivity) (by positivity)
  nlinarith

/-- Telescoping bound: for `n ≥ 2`,
`ε(n) ≤ (2/7) (1 / log₂ n - 1 / log₂ (n + 1))`. -/
lemma eps_le_telescope {n : ℕ} (hn : 2 ≤ n) :
    eps n ≤ 2 / 7 * (1 / Real.logb 2 n - 1 / Real.logb 2 ((n : ℝ) + 1)) := by
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  set x := Real.logb 2 (n : ℝ) with hx
  set y := Real.logb 2 ((n : ℝ) + 1) with hy
  have hx1 : 1 ≤ x := by
    rw [hx]
    calc (1 : ℝ) = Real.logb 2 2 := (Real.logb_self_eq_one (by norm_num)).symm
      _ ≤ Real.logb 2 (n : ℝ) := Real.logb_le_logb_of_le (by norm_num) (by norm_num) hn'
  -- `y - x = log₂ ((n+1)/n) ≥ ln ((n+1)/n) ≥ 1/(n+1)`
  have hyx : 1 / ((n : ℝ) + 1) ≤ y - x := by
    have hn0 : (0 : ℝ) < n := by linarith
    have hq : (0 : ℝ) < ((n : ℝ) + 1) / n := by positivity
    have hlog := Real.one_sub_inv_le_log_of_pos hq
    have hinv : 1 - (((n : ℝ) + 1) / n)⁻¹ = 1 / ((n : ℝ) + 1) := by
      field_simp
      ring
    rw [hinv] at hlog
    have hdiff : y - x = Real.log (((n : ℝ) + 1) / n) / Real.log 2 := by
      rw [hx, hy, Real.logb, Real.logb, Real.log_div (by positivity) (by positivity)]
      ring
    have hln2 : Real.log 2 < 1 := by
      have := Real.log_two_lt_d9
      linarith
    have hln2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlpos : 0 ≤ Real.log (((n : ℝ) + 1) / n) := le_trans (by positivity) hlog
    rw [hdiff, le_div_iff₀ hln2pos]
    calc 1 / ((n : ℝ) + 1) * Real.log 2 ≤ 1 / ((n : ℝ) + 1) * 1 := by
          gcongr
      _ ≤ _ := by linarith
  have hy1 : 1 ≤ y := by
    have : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
    linarith
  -- key: `x ≤ 2 n y (y - x)`
  have hkey1 : 1 ≤ 2 * n * (y - x) := by
    have h := mul_le_mul_of_nonneg_left hyx (by positivity : (0 : ℝ) ≤ 2 * n)
    have : 1 ≤ 2 * (n : ℝ) * (1 / ((n : ℝ) + 1)) := by
      rw [mul_one_div, le_div_iff₀ (by positivity)]
      linarith
    linarith
  unfold eps
  have hx0 : 0 < x := by linarith
  have hy0 : 0 < y := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  rw [← hy]
  rw [div_sub_div _ _ hx0.ne' hy0.ne', one_div_le (by positivity) (by
    apply mul_pos (by norm_num)
    apply div_pos (by nlinarith) (by positivity))]
  rw [show 1 / (2 / 7 * ((1 * y - x * 1) / (x * y))) = 7 * (x * y) / (2 * (y - x)) by
    field_simp]
  rw [div_le_iff₀ (by nlinarith)]
  nlinarith [mul_le_mul_of_nonneg_left hkey1 (by positivity : (0 : ℝ) ≤ 7 * y * y)]

/-- Strengthened statement for induction: for `m ≥ 1`,
`∑_{i=1}^{m} ε(i) + (2/7) / log₂ (m + 1) ≤ 3/7`. -/
lemma sum_eps_add_le (m : ℕ) (hm : 1 ≤ m) :
    ∑ i ∈ Finset.range m, eps (i + 1) + 2 / 7 * (1 / Real.logb 2 ((m : ℝ) + 1)) ≤ 3 / 7 := by
  induction m, hm using Nat.le_induction with
  | base =>
    have h : Real.logb 2 ((1 : ℕ) + 1 : ℝ) = 1 := by
      norm_num [Real.logb_self_eq_one]
    simp only [Finset.range_one, Finset.sum_singleton, zero_add, eps, h]
    norm_num
  | succ m hm ih =>
    rw [Finset.sum_range_succ]
    have ht := eps_le_telescope (n := m + 1) (by omega)
    push_cast at ht ⊢
    linarith

/-- The paper's bound `∑_{i ≥ 1} 1 / (7 i log₂² (i + 1)) ≤ 1/2` (all partial sums). -/
theorem sum_eps_le_half (m : ℕ) : ∑ i ∈ Finset.range m, eps (i + 1) ≤ 1 / 2 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · have h := sum_eps_add_le m hm
    have hpos : 0 ≤ 2 / 7 * (1 / Real.logb 2 ((m : ℝ) + 1)) := by
      have := one_le_logb_two_add_one hm
      have : 0 < Real.logb 2 ((m : ℝ) + 1) := by linarith
      positivity
    linarith

/-- Rank lemma: if each `x ∈ S` observes contention `b x` at least its rank w.r.t. the injective key
`f` (one plus the number of elements of `S` with a smaller key), then `∑_{x ∈ S} ε(b x)` is at most
the sum of the first `|S|` terms of the series. -/
theorem sum_eps_le_of_rank {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (hf : Set.InjOn f S) (b : α → ℕ)
    (hb : ∀ x ∈ S, 1 + (S.filter (fun z => f z < f x)).card ≤ b x) :
    ∑ x ∈ S, eps (b x) ≤ ∑ i ∈ Finset.range S.card, eps (i + 1) := by
  induction h : S.card generalizing S with
  | zero =>
    rw [Finset.card_eq_zero] at h
    simp [h]
  | succ n ih =>
    have hne : S.Nonempty := by
      rw [← Finset.card_pos, h]; omega
    obtain ⟨x, hxS, hxmax⟩ := Finset.exists_max_image S f hne
    have hfilter : S.filter (fun z => f z < f x) = S.erase x := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hz, hlt⟩
        exact ⟨fun hzx => by subst hzx; exact lt_irrefl _ hlt, hz⟩
      · rintro ⟨hzx, hz⟩
        refine ⟨hz, lt_of_le_of_ne (hxmax z hz) fun hfe => hzx (hf hz hxS hfe)⟩
    have hbx : n + 1 ≤ b x := by
      have := hb x hxS
      rw [hfilter, Finset.card_erase_of_mem hxS, h] at this
      omega
    have hcard : (S.erase x).card = n := by
      rw [Finset.card_erase_of_mem hxS, h]; rfl
    have ih' := ih (S.erase x) (hf.mono (by simp [Finset.coe_erase]))
      (fun y hy => by
        have h1 := hb y (Finset.mem_of_mem_erase hy)
        have h2 : ((S.erase x).filter (fun z => f z < f y)).card ≤
            (S.filter (fun z => f z < f y)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ (Finset.erase_subset _ _))
        omega) hcard
    rw [← Finset.add_sum_erase S _ hxS, Finset.sum_range_succ, add_comm]
    exact add_le_add ih' (eps_antitone (by omega) hbx)

/-- Corollary of the rank lemma: `∑_{x ∈ S} ε(b x) ≤ 1/2`. -/
theorem sum_eps_le_half_of_rank {α : Type*} [DecidableEq α] (S : Finset α) (f : α → ℕ)
    (hf : Set.InjOn f S) (b : α → ℕ)
    (hb : ∀ x ∈ S, 1 + (S.filter (fun z => f z < f x)).card ≤ b x) :
    ∑ x ∈ S, eps (b x) ≤ 1 / 2 :=
  (sum_eps_le_of_rank S f hf b hb).trans (sum_eps_le_half _)

end Podc.RandomizedWaitFreeLocks
