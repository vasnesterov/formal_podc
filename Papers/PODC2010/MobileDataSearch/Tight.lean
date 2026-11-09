import Papers.PODC2010.MobileDataSearch.TwoRounds

/-!
# Tightness of Theorems 4 and 5 (Lemmas 7 and 8), and Lemmas 4–6

Bar-Noy, Cheilaris, Feng, Levin, *Finding mobile data under delay constraints with searching costs*,
PODC 2010, Sections 5.1–5.2.

Both tight instances use ties in the ratio order: FRO attains the bad ratio only when the ties
are broken adversarially (the indexing below); see `differencies.md`.
-/

namespace Podc.MobileDataSearch

open Finset

variable {m : ℕ}

/-- `∑_{i ∈ S} [i = c] · v = [c ∈ S] · v`. -/
private lemma sum_ite_eq_mem {N : ℕ} (S : Finset (Fin N)) (c : Fin N) (v : ℝ) :
    ∑ i ∈ S, (if i = c then v else 0) = if c ∈ S then v else 0 :=
  Finset.sum_ite_eq' S c (fun _ => v)

private lemma ite_nonneg' {P : Prop} [Decidable P] {v : ℝ} (hv : 0 ≤ v) :
    0 ≤ if P then v else 0 := by split_ifs <;> simp [hv]

private lemma mem_pref_iff {N : ℕ} (k : ℕ) (i : Fin N) : i ∈ pref N k ↔ i.val < k := by
  simp [pref]

/-! ### Lemma 7: the ratio `8/7` is attained for every `N = m + 3 > 2` -/

/-- Lemma 7 instance, probabilities: `p = (1/4, 3/4, 0, …, 0)`. -/
noncomputable def p7 (m : ℕ) : Fin (m + 3) → ℝ := fun i =>
  (if i = 0 then 1 / 4 else 0) + (if i = 1 then 3 / 4 else 0)

/-- Lemma 7 instance, costs: `w = (1/5, 3/5, 1/(5(N-2)), …, 1/(5(N-2)))`. -/
noncomputable def w7 (m : ℕ) : Fin (m + 3) → ℝ := fun i =>
  (if i = 0 then 1 / 5 else 0) + (if i = 1 then 3 / 5 else 0) +
    (if 2 ≤ i.val then 1 / (5 * ((m : ℝ) + 1)) else 0)

private lemma p7_sum (S : Finset (Fin (m + 3))) :
    ∑ i ∈ S, p7 m i = (if (0 : Fin (m + 3)) ∈ S then 1 / 4 else 0) +
      (if (1 : Fin (m + 3)) ∈ S then 3 / 4 else 0) := by
  simp only [p7, sum_add_distrib, sum_ite_eq_mem]

private lemma w7_sum_ge (S : Finset (Fin (m + 3))) :
    (if (0 : Fin (m + 3)) ∈ S then 1 / 5 else 0) + (if (1 : Fin (m + 3)) ∈ S then 3 / 5 else 0) ≤
      ∑ i ∈ S, w7 m i := by
  simp only [w7, sum_add_distrib, sum_ite_eq_mem]
  have : 0 ≤ ∑ i ∈ S, (if 2 ≤ i.val then 1 / (5 * ((m : ℝ) + 1)) else 0) :=
    sum_nonneg fun i _ => ite_nonneg' (by positivity)
  linarith

private lemma card_ge_two : (univ.filter (fun i : Fin (m + 3) => 2 ≤ i.val)).card = m + 1 := by
  have h := Fin.card_filter_val_lt (n := m + 3) (m := 2)
  have hc := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin (m + 3))))
    (fun i : Fin (m + 3) => i.val < 2)
  simp only [card_univ, Fintype.card_fin, not_lt] at hc
  omega

lemma p7_total : ∑ i, p7 m i = 1 := by
  rw [p7_sum]; simp; norm_num

lemma w7_total : ∑ i, w7 m i = 1 := by
  simp only [w7, sum_add_distrib, sum_ite_eq_mem, mem_univ, ite_true]
  rw [← Finset.sum_filter, sum_const, card_ge_two, nsmul_eq_mul]
  push_cast
  field_simp
  ring

lemma p7_nonneg (i : Fin (m + 3)) : 0 ≤ p7 m i :=
  add_nonneg (ite_nonneg' (by norm_num)) (ite_nonneg' (by norm_num))

lemma w7_pos (i : Fin (m + 3)) : 0 < w7 m i := by
  simp only [w7]
  have h01 : (0 : Fin (m + 3)) ≠ 1 := by simp
  by_cases h0 : i = 0
  · subst h0; simp [h01]
  by_cases h1 : i = 1
  · subst h1; simp [h01.symm]
  · have : 2 ≤ i.val := by
      have h0' : i.val ≠ 0 := fun h => h0 (Fin.ext h)
      have h1' : i.val ≠ 1 := fun h => h1 (Fin.ext (by simpa using h))
      omega
    simp [h0, h1, this]; positivity

/-- The Lemma 7 instance is indexed in (non-strict) ratio order `5/4 = 5/4 > 0 = ⋯ = 0`. -/
lemma ratioSorted7 : RatioSorted (p7 m) (w7 m) := by
  intro i j hij
  have hval : i.val ≤ j.val := hij
  have h01 : (0 : Fin (m + 3)).val = 0 := rfl
  have h11 : (1 : Fin (m + 3)).val = 1 := rfl
  simp only [p7, w7, Fin.ext_iff, h01, h11]
  have hc : (0 : ℝ) < 1 / (5 * ((m : ℝ) + 1)) := by positivity
  rcases Nat.lt_or_ge j.val 2 with hj | hj
  · interval_cases hjv : j.val <;> interval_cases hiv : i.val <;> norm_num
  · have hj0 : j.val ≠ 0 := by omega
    have hj1 : j.val ≠ 1 := by omega
    simp only [hj0, hj1, ite_false, zero_add, zero_mul]
    apply mul_nonneg
    · split_ifs <;> norm_num
    · split_ifs <;> positivity

private lemma gain7 (S : Finset (Fin (m + 3))) :
    gain (p7 m) (w7 m) S = (∑ i ∈ S, p7 m i) * (1 - ∑ i ∈ S, w7 m i) := by
  rw [gain, sum_compl_eq, w7_total]

private lemma gain7_le (S : Finset (Fin (m + 3))) : gain (p7 m) (w7 m) S ≤ 3 / 10 := by
  rw [gain7, p7_sum]
  have hw := w7_sum_ge (m := m) S
  have hw1 : ∑ i ∈ S, w7 m i ≤ 1 := by
    rw [← w7_total (m := m)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ S) fun i _ _ => (w7_pos i).le
  by_cases h0 : (0 : Fin (m + 3)) ∈ S <;> by_cases h1 : (1 : Fin (m + 3)) ∈ S <;>
    simp only [h0, h1, ite_true, ite_false] at hw ⊢ <;> nlinarith

private lemma gain7_pref_le (k : ℕ) : gain (p7 m) (w7 m) (pref (m + 3) k) ≤ 1 / 5 := by
  rw [gain7, p7_sum]
  have hw := w7_sum_ge (m := m) (pref (m + 3) k)
  have hw1 : ∑ i ∈ pref (m + 3) k, w7 m i ≤ 1 := by
    rw [← w7_total (m := m)]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun i _ _ => (w7_pos i).le
  have h0 : (0 : Fin (m + 3)) ∈ pref (m + 3) k ↔ 0 < k := mem_pref_iff k 0
  have h1 : (1 : Fin (m + 3)) ∈ pref (m + 3) k ↔ 1 < k := mem_pref_iff k 1
  rcases Nat.lt_or_ge k 2 with hk | hk
  · interval_cases k
    · simp only [h0, h1, lt_irrefl, ite_false, Nat.not_lt_zero] at hw ⊢; norm_num
    · simp only [h0, h1, Nat.lt_irrefl, ite_false, Nat.zero_lt_one, ite_true] at hw ⊢
      nlinarith
  · have a0 : (0 : Fin (m + 3)) ∈ pref (m + 3) k := h0.2 (by omega)
    have a1 : (1 : Fin (m + 3)) ∈ pref (m + 3) k := h1.2 (by omega)
    simp only [a0, a1, ↓reduceIte] at hw ⊢
    nlinarith

private lemma pref_one : pref (m + 3) 1 = {0} := by
  ext i
  simp only [pref, mem_filter, mem_univ, true_and, mem_singleton, Fin.ext_iff, Fin.val_zero]
  omega

private lemma gain7_pref_one : gain (p7 m) (w7 m) (pref (m + 3) 1) = 1 / 5 := by
  rw [gain7, pref_one, sum_singleton, sum_singleton]
  simp [p7, w7]; norm_num

private lemma gain7_one : gain (p7 m) (w7 m) {1} = 3 / 10 := by
  rw [gain7, sum_singleton, sum_singleton]
  simp [p7, w7]; norm_num

/-- **Lemma 7 of [paper]**: for every `N = m + 3 > 2` boxes, on the instance
`p = (1/4, 3/4, 0, …)`, `w = (1/5, 3/5, 1/(5(N-2)), …)` (indexed in ratio order, the tie
`p₁/w₁ = p₂/w₂` broken adversarially) every FRO output costs `4/5` and every optimal strategy costs
`7/10`, so the ratio `8/7` of Theorem 4 is attained. -/
theorem lemma7 :
    (∀ A : Strategy (m + 3) 2, IsFRO (p7 m) (w7 m) A → cost (p7 m) (w7 m) A = 4 / 5) ∧
    (∀ B : Strategy (m + 3) 2, IsOptimal (p7 m) (w7 m) B → cost (p7 m) (w7 m) B = 7 / 10) := by
  constructor
  · intro A hA
    obtain ⟨k, -, rfl⟩ := monotone_eq_prefixStrategy A hA.1
    have h1 := hA.2 (prefixStrategy 1) (prefixStrategy_monotone 1)
    rw [cost_two, cost_two, firstRound_prefixStrategy, firstRound_prefixStrategy, p7_total,
      w7_total, gain7_pref_one] at h1
    rw [cost_two, firstRound_prefixStrategy, p7_total, w7_total]
    have := gain7_pref_le (m := m) k
    linarith
  · intro B hB
    have h1 := hB (ofFirstRound {1})
    rw [cost_two, cost_two, firstRound_ofFirstRound, p7_total, w7_total, gain7_one] at h1
    rw [cost_two, p7_total, w7_total]
    have := gain7_le (m := m) (firstRound B)
    linarith

/-- Theorem 4 and Lemma 7 together: on the Lemma 7 instance the FRO/OPT ratio is exactly `8/7`. -/
theorem theorem4_tight (A B : Strategy (m + 3) 2) (hA : IsFRO (p7 m) (w7 m) A)
    (hB : IsOptimal (p7 m) (w7 m) B) : cost (p7 m) (w7 m) A = 8 / 7 * cost (p7 m) (w7 m) B := by
  rw [lemma7.1 A hA, lemma7.2 B hB]; norm_num

/-! ### Lemma 8: the ratio `(4 + √7)/6` is attained for typical tokens -/

/-- The parameter `x = (3 - √7)/2` of Lemma 8. -/
noncomputable def x8 : ℝ := (3 - √7) / 2

private lemma x8_sq : x8 ^ 2 = 3 * x8 - 1 / 2 := by
  have hs : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  simp only [x8]; nlinarith

private lemma x8_bounds : 0 < x8 ∧ x8 < 1 / 4 := by
  have hs : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have h2 := two_le_sqrt_seven
  have hlt : √7 < 3 := by nlinarith
  have hgt : (5 : ℝ) / 2 < √7 := by nlinarith
  simp only [x8]; constructor <;> linarith

/-- Lemma 8 instance (typical token, `p = w`): `(x, 1 - 2x, x, 0, …, 0)`. -/
noncomputable def p8 (m : ℕ) : Fin (m + 3) → ℝ := fun i =>
  (if i = 0 then x8 else 0) + (if i = 1 then 1 - 2 * x8 else 0) + (if i = 2 then x8 else 0)

private lemma p8_sum (S : Finset (Fin (m + 3))) :
    ∑ i ∈ S, p8 m i = (if (0 : Fin (m + 3)) ∈ S then x8 else 0) +
      (if (1 : Fin (m + 3)) ∈ S then 1 - 2 * x8 else 0) +
      (if (2 : Fin (m + 3)) ∈ S then x8 else 0) := by
  simp only [p8, sum_add_distrib, sum_ite_eq_mem]

lemma p8_total : ∑ i, p8 m i = 1 := by rw [p8_sum]; simp; ring

lemma p8_nonneg (i : Fin (m + 3)) : 0 ≤ p8 m i := by
  obtain ⟨h0, h1⟩ := x8_bounds
  simp only [p8]
  refine add_nonneg (add_nonneg (ite_nonneg' h0.le) (ite_nonneg' (by linarith))) (ite_nonneg' h0.le)

private lemma gain8 (S : Finset (Fin (m + 3))) :
    gain (p8 m) (p8 m) S = (∑ i ∈ S, p8 m i) * (1 - ∑ i ∈ S, p8 m i) := by
  rw [gain, sum_compl_eq, p8_total]

private lemma gain8_le (S : Finset (Fin (m + 3))) :
    gain (p8 m) (p8 m) S ≤ 2 * x8 * (1 - 2 * x8) := by
  obtain ⟨h0, h1⟩ := x8_bounds
  rw [gain8, p8_sum]
  by_cases a : (0 : Fin (m + 3)) ∈ S <;> by_cases b : (1 : Fin (m + 3)) ∈ S <;>
    by_cases c : (2 : Fin (m + 3)) ∈ S <;> simp only [a, b, c, ite_true, ite_false] <;> nlinarith

private lemma gain8_pref_le (k : ℕ) : gain (p8 m) (p8 m) (pref (m + 3) k) ≤ x8 * (1 - x8) := by
  obtain ⟨hx0, hx1⟩ := x8_bounds
  rw [gain8, p8_sum]
  have h0 : (0 : Fin (m + 3)) ∈ pref (m + 3) k ↔ 0 < k := mem_pref_iff k 0
  have h1 : (1 : Fin (m + 3)) ∈ pref (m + 3) k ↔ 1 < k := mem_pref_iff k 1
  have h2 : (2 : Fin (m + 3)) ∈ pref (m + 3) k ↔ 2 < k := mem_pref_iff k 2
  rcases Nat.lt_or_ge k 3 with hk | hk
  · interval_cases k <;> simp only [h0, h1, h2] <;> norm_num <;> nlinarith
  · simp only [h0, h1, h2, show 0 < k by omega, show 1 < k by omega, show 2 < k by omega,
      ite_true]
    nlinarith

private lemma gain8_pref_one : gain (p8 m) (p8 m) (pref (m + 3) 1) = x8 * (1 - x8) := by
  rw [gain8, pref_one, sum_singleton]
  have h2 : 2 % (m + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  simp [p8, Fin.ext_iff, h2]

private lemma gain8_one : gain (p8 m) (p8 m) {1} = 2 * x8 * (1 - 2 * x8) := by
  rw [gain8, sum_singleton]
  have h2 : 2 % (m + 3) = 2 := Nat.mod_eq_of_lt (by omega)
  simp [p8, Fin.ext_iff, h2]; ring

/-- **Lemma 8 of [paper]**: for every `N = m + 3 > 2`, on the typical instance
`p = w = (x, 1 - 2x, x, 0, …)` with `x = (3 - √7)/2` (boxes in the adversarial order), every FRO
output costs `(4 + √7)/6` times the optimum, so the bound of Theorem 5 is attained. -/
theorem lemma8 (A B : Strategy (m + 3) 2) (hA : IsFRO (p8 m) (p8 m) A)
    (hB : IsOptimal (p8 m) (p8 m) B) :
    cost (p8 m) (p8 m) A = (4 + √7) / 6 * cost (p8 m) (p8 m) B := by
  have hA' : cost (p8 m) (p8 m) A = 1 - x8 * (1 - x8) := by
    obtain ⟨k, -, rfl⟩ := monotone_eq_prefixStrategy A hA.1
    have h1 := hA.2 (prefixStrategy 1) (prefixStrategy_monotone 1)
    rw [cost_two, cost_two, firstRound_prefixStrategy, firstRound_prefixStrategy, p8_total,
      gain8_pref_one] at h1
    rw [cost_two, firstRound_prefixStrategy, p8_total]
    have := gain8_pref_le (m := m) k
    linarith
  have hB' : cost (p8 m) (p8 m) B = 1 - 2 * x8 * (1 - 2 * x8) := by
    have h1 := hB (ofFirstRound {1})
    rw [cost_two, cost_two, firstRound_ofFirstRound, p8_total, gain8_one] at h1
    rw [cost_two, p8_total]
    have := gain8_le (m := m) (firstRound B)
    linarith
  rw [hA', hB']
  have hs : √7 ^ 2 = 7 := Real.sq_sqrt (by norm_num)
  have hx := x8_sq
  simp only [x8] at hx ⊢
  nlinarith

/-! ### Lemmas 4, 5, 6 -/

/-- **Lemma 5 of [paper]** (`N = 3`), a special case of `theorem4`. -/
theorem lemma5 {p w : Fin 3 → ℝ} (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i) (hs : RatioSorted p w)
    {A : Strategy 3 2} (hA : IsFRO p w A) (B : Strategy 3 2) : cost p w A ≤ 8 / 7 * cost p w B :=
  theorem4 hp hw hs hA B

/-- **Lemma 6 of [paper]** (`N = 4`), a special case of `theorem4`. -/
theorem lemma6 {p w : Fin 4 → ℝ} (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i) (hs : RatioSorted p w)
    {A : Strategy 4 2} (hA : IsFRO p w A) (B : Strategy 4 2) : cost p w A ≤ 8 / 7 * cost p w B :=
  theorem4 hp hw hs hA B

lemma cost_nonneg {N D : ℕ} {p w : Fin N → ℝ} (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i)
    (A : Strategy N D) : 0 ≤ cost p w A :=
  sum_nonneg fun i _ => mul_nonneg (hp i) (sum_nonneg fun j _ => hw j)

/-- **Lemma 4 of [paper]** (statement): for every instance there is an instance with `N = 3`
boxes on which FRO's ratio is at least as large. True — but only as a consequence of
Theorem 4 (proved here directly) and Lemma 7; the paper's merging proof is flawed
(`Lemma4.lean`). -/
theorem lemma4 {N : ℕ} {p w : Fin N → ℝ} (hp : ∀ i, 0 ≤ p i) (hw : ∀ i, 0 ≤ w i)
    (hs : RatioSorted p w) {A B : Strategy N 2} (hA : IsFRO p w A) :
    ∃ (p' w' : Fin 3 → ℝ), (∀ i, 0 ≤ p' i) ∧ (∀ i, 0 < w' i) ∧ RatioSorted p' w' ∧
      ∀ A' B' : Strategy 3 2, IsFRO p' w' A' → IsOptimal p' w' B' →
        cost p w A / cost p w B ≤ cost p' w' A' / cost p' w' B' := by
  refine ⟨p7 0, w7 0, p7_nonneg, w7_pos, ratioSorted7, fun A' B' hA' hB' => ?_⟩
  rw [lemma7.1 A' hA', lemma7.2 B' hB']
  have h4 := theorem4 hp hw hs hA B
  have hB0 := cost_nonneg hp hw B
  rcases hB0.eq_or_lt with h | h
  · rw [← h, div_zero]; norm_num
  · rw [div_le_iff₀ h]; linarith

end Podc.MobileDataSearch
