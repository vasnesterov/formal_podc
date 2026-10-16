import Papers.PODC2026.TreeAA.TreeGeom

/-!
# Arithmetic of the round bounds (Theorems 1 and 2)

The lower bound (Theorem 1) and the round complexity of `RealAA` (Theorem 2) consist of a cited
part (Fekete's chain of executions, resp. the contraction Claim 12 of Ben-Or–Dolev–Hoch) and an
arithmetic part. We formalize the arithmetic parts, with the cited facts as hypotheses.

* `exists_consecutive_far` — the step of **Lemma 1** that generalizes Fekete's argument from `ℝ`
  to graphs: in a chain of `s` steps from `a` to `b`, some step has length `≥ d(a,b)/s`.
* `theorem1_rounds` — **Theorem 1** (arithmetic): `D · (1/(Rδ))^R ≤ 1` (Lemma 1 + 1-agreement,
  `δ = (n+t)/t`) forces `R ≥ log₂ D / (2 (log₂ log₂ D + log₂ δ))`.
* `theorem2_iterations`, `theorem2` — **Theorem 2** (arithmetic): with
  `R = ⌈(20/9) log₂ δ / log₂ log₂ δ⌉` iterations (`δ = D/ε > 2`) we get `R^R ≥ δ`, hence
  `ε`-agreement from the contraction bound (Lemma 16), and `3R < 7 log₂ δ / log₂ log₂ δ + 3`.
* `theorem2_bound_degenerate` — for `1 < D/ε < 2` the stated bound is `< 3` although at least one
  3-round iteration is needed: Theorem 2's bound is false in this degenerate range.
-/

namespace TreeAA

open Real

/-! ### Lemma 1: chains in a graph -/

/-- In a chain `v 0, …, v s` of vertices, some consecutive pair is at distance at least
`d(v 0, v s) / s` (stated without division). -/
lemma exists_consecutive_far {V : Type*} {G : SimpleGraph V} (hG : G.Connected) (v : ℕ → V)
    {s : ℕ} (hs : 0 < s) : ∃ i < s, G.dist (v 0) (v s) ≤ s * G.dist (v i) (v (i + 1)) := by
  have htri : ∀ k, G.dist (v 0) (v k) ≤ ∑ i ∈ Finset.range k, G.dist (v i) (v (i + 1)) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ]
      exact (hG.dist_triangle (v := v k)).trans (by omega)
  by_contra hcon
  push Not at hcon
  have hlt : ∑ i ∈ Finset.range s, s * G.dist (v i) (v (i + 1)) <
      ∑ _i ∈ Finset.range s, G.dist (v 0) (v s) :=
    Finset.sum_lt_sum_of_nonempty (Finset.nonempty_range_iff.mpr hs.ne') fun i hi => hcon i (by simpa using hi)
  rw [← Finset.mul_sum, Finset.sum_const, Finset.card_range, smul_eq_mul] at hlt
  have := Nat.mul_le_mul_left s (htri s)
  omega

/-! ### Theorem 1 -/

/-- **Theorem 1** (arithmetic part). Lemma 1 with `d(a,b) = D` and 1-agreement give
`1 ≥ D · (t / (R (n+t)))^R = D · (1/(Rδ))^R` with `δ = (n+t)/t ≥ 2`. Then (for `D ≥ 4`)
`R ≥ log₂ D / (2 (log₂ log₂ D + log₂ δ))`, i.e. `R = Ω(log D / (log log D + log ((n+t)/t)))`. -/
theorem theorem1_rounds {D δ : ℝ} (hD : 4 ≤ D) (hδ : 2 ≤ δ) {R : ℕ}
    (h : D * (1 / (R * δ)) ^ R ≤ 1) :
    logb 2 D / (2 * (logb 2 (logb 2 D) + logb 2 δ)) ≤ R := by
  have hR : 0 < R := by
    rcases Nat.eq_zero_or_pos R with rfl | hR
    · simp at h; linarith
    · exact hR
  have hRr : (0 : ℝ) < R := by exact_mod_cast hR
  have hRδ : 0 < (R : ℝ) * δ := by positivity
  -- `D ≤ (Rδ)^R`
  have hpow : D ≤ ((R : ℝ) * δ) ^ R := by
    rw [one_div, inv_pow] at h
    have hp : 0 < ((R : ℝ) * δ) ^ R := by positivity
    rwa [← div_eq_mul_inv, div_le_one hp] at h
  have hX : 2 ≤ logb 2 D := by
    rw [le_logb_iff_rpow_le one_lt_two (by linarith)]; norm_num; linarith
  set X := logb 2 D
  have hXδ : 4 ≤ X * δ := by nlinarith
  have hY : 2 ≤ logb 2 (X * δ) := by
    rw [le_logb_iff_rpow_le one_lt_two (by linarith)]; norm_num; linarith
  have hYeq : logb 2 X + logb 2 δ = logb 2 (X * δ) := (logb_mul (by linarith) (by linarith)).symm
  rw [hYeq]
  set Y := logb 2 (X * δ)
  have hlog : X ≤ R * logb 2 (R * δ) := by
    have := (logb_le_logb one_lt_two (by linarith) (by positivity)).2 hpow
    rwa [logb_pow] at this
  by_contra hcon
  push Not at hcon
  rw [lt_div_iff₀ (by linarith)] at hcon
  -- `Rδ < Xδ`, hence `log₂ (Rδ) < Y` and `R log₂ (Rδ) < R Y < X / 2`
  have hRX : (R : ℝ) < X := by nlinarith
  have hlt : logb 2 (R * δ) < Y := logb_lt_logb one_lt_two hRδ (by nlinarith)
  have : (R : ℝ) * logb 2 (R * δ) < R * Y := mul_lt_mul_of_pos_left hlt hRr
  nlinarith

/-! ### Theorem 2 -/

/-- `log₂ x ≤ (11/20) x` for `x > 0` (the maximum of `log₂ x / x` is `1/(e ln 2) < 11/20`). -/
lemma logb_two_le (x : ℝ) (hx : 0 < x) : logb 2 x ≤ 11 / 20 * x := by
  have h1 : log x ≤ x / exp 1 := by
    have := log_le_sub_one_of_pos (show 0 < x / exp 1 by positivity)
    rw [log_div hx.ne' (exp_pos 1).ne', log_exp] at this
    linarith
  have he := exp_one_gt_d9
  have hl := log_two_gt_d9
  have hc : (1 : ℝ) ≤ 11 / 20 * log 2 * exp 1 := by nlinarith
  rw [logb, div_le_iff₀ (log_pos one_lt_two)]
  calc log x ≤ x / exp 1 := h1
    _ ≤ 11 / 20 * x * log 2 := by
      rw [div_le_iff₀ (exp_pos 1)]
      nlinarith

/-- **Theorem 2** (iteration count). For `δ = D/ε > 2`, `R = ⌈(20/9) log₂ δ / log₂ log₂ δ⌉`
satisfies `R^R ≥ δ` and `3R < 7 log₂ δ / log₂ log₂ δ + 3`. -/
theorem theorem2_iterations {δ : ℝ} (hδ : 2 < δ) :
    δ ≤ (⌈20 / 9 * logb 2 δ / logb 2 (logb 2 δ)⌉₊ : ℝ) ^ ⌈20 / 9 * logb 2 δ / logb 2 (logb 2 δ)⌉₊ ∧
    (3 * ⌈20 / 9 * logb 2 δ / logb 2 (logb 2 δ)⌉₊ : ℝ) <
      7 * (logb 2 δ / logb 2 (logb 2 δ)) + 3 := by
  set L := logb 2 δ with hL
  have hL1 : 1 < L := by
    rw [hL, lt_logb_iff_rpow_lt one_lt_two (by linarith)]; norm_num; exact hδ
  set x := logb 2 L with hx
  have hx0 : 0 < x := logb_pos one_lt_two hL1
  set A := 20 / 9 * L / x with hA
  have hA0 : 0 < A := by positivity
  set R := ⌈A⌉₊ with hR
  have hRA : A ≤ R := Nat.le_ceil A
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le hA0 hRA
  refine ⟨?_, ?_⟩
  · -- `log₂ R ≥ (9/20) x`
    have hlogR : 9 / 20 * x ≤ logb 2 R := by
      have h1 : L / x ≤ A := by
        rw [hA]; apply div_le_div_of_nonneg_right _ hx0.le; linarith
      have h2 : logb 2 (L / x) ≤ logb 2 R :=
        (logb_le_logb one_lt_two (by positivity) hR0).2 (h1.trans hRA)
      rw [logb_div (by linarith) hx0.ne', ← hx] at h2
      have := logb_two_le x hx0
      linarith
    have hprod : L ≤ R * logb 2 R := by
      have : A * (9 / 20 * x) = L := by rw [hA]; field_simp
      calc L = A * (9 / 20 * x) := this.symm
        _ ≤ R * logb 2 R := mul_le_mul hRA hlogR (by positivity) hR0.le
    have : logb 2 δ ≤ logb 2 ((R : ℝ) ^ R) := by rw [logb_pow]; exact hprod
    exact (logb_le_logb one_lt_two (by linarith) (by positivity)).1 this
  · have h1 : (R : ℝ) < A + 1 := Nat.ceil_lt_add_one hA0.le
    have h2 : 0 < L / x := by positivity
    have h3 : A = 20 / 9 * (L / x) := by rw [hA]; ring
    rw [h3] at h1
    linarith

/-- Contraction: if `n > 3t`, then `D t^R / ((n-2t)^R R^R) ≤ D / R^R`. -/
lemma contraction_le {n t : ℕ} (h : 3 * t < n) {D : ℝ} (hD : 0 ≤ D) (R : ℕ) :
    D * (t : ℝ) ^ R / (((n : ℝ) - 2 * t) ^ R * (R : ℝ) ^ R) ≤ D / (R : ℝ) ^ R := by
  have hn : (t : ℝ) ≤ (n : ℝ) - 2 * t := by
    have : (3 * t : ℝ) < n := by exact_mod_cast h
    linarith
  have hpos : (0 : ℝ) < (n : ℝ) - 2 * t := by
    have : (3 * t : ℝ) < n := by exact_mod_cast h
    have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    linarith
  rcases Nat.eq_zero_or_pos R with rfl | hR
  · simp
  have hRR : (0 : ℝ) < (R : ℝ) ^ R := by positivity
  have htn : (t : ℝ) ^ R ≤ ((n : ℝ) - 2 * t) ^ R := pow_le_pow_left₀ (Nat.cast_nonneg t) hn R
  rw [div_le_div_iff₀ (by positivity) hRR]
  have : D * (t : ℝ) ^ R ≤ D * ((n : ℝ) - 2 * t) ^ R := mul_le_mul_of_nonneg_left htn hD
  nlinarith

/-- **Theorem 2** (with Lemma 16 of the paper — Claim 12 of Ben-Or–Dolev–Hoch — as hypothesis).
Let `n > 3t`, `D/ε > 2`, and assume the honest range after `R` iterations is at most
`D t^R / ((n-2t)^R R^R)`. Then after `R = ⌈(20/9) log₂ δ / log₂ log₂ δ⌉` iterations (`δ = D/ε`) the
honest values are `ε`-close, and the `3R` rounds are `< 7 log₂ δ / log₂ log₂ δ + 3`. -/
theorem theorem2 {n t : ℕ} (hnt : 3 * t < n) {D ε : ℝ} (hε : 0 < ε) (hD : 2 * ε < D)
    (range : ℕ → ℝ)
    (h16 : ∀ R : ℕ, range R ≤ D * (t : ℝ) ^ R / (((n : ℝ) - 2 * t) ^ R * (R : ℝ) ^ R)) :
    range ⌈20 / 9 * logb 2 (D / ε) / logb 2 (logb 2 (D / ε))⌉₊ ≤ ε ∧
    (3 * ⌈20 / 9 * logb 2 (D / ε) / logb 2 (logb 2 (D / ε))⌉₊ : ℝ) <
      7 * (logb 2 (D / ε) / logb 2 (logb 2 (D / ε))) + 3 := by
  have hδ : 2 < D / ε := by rw [lt_div_iff₀ hε]; linarith
  obtain ⟨hpow, hrounds⟩ := theorem2_iterations hδ
  refine ⟨?_, hrounds⟩
  set R := ⌈20 / 9 * logb 2 (D / ε) / logb 2 (logb 2 (D / ε))⌉₊
  have hD0 : 0 ≤ D := by linarith
  have hRR : (0 : ℝ) < (R : ℝ) ^ R := lt_of_lt_of_le (by linarith) hpow
  refine (h16 R).trans ((contraction_le hnt hD0 R).trans ?_)
  rw [div_le_iff₀ hRR]
  rw [div_le_iff₀ hε] at hpow
  linarith

/-- In the degenerate range `1 < D/ε < 2`, the bound `7 log₂ δ / log₂ log₂ δ + 3` of Theorem 2
is smaller than `3`, i.e. than one iteration of `RealAA` (and at least one iteration is needed
when the honest inputs are not `ε`-close). At `δ = 2` the bound is undefined (`log₂ log₂ 2 = 0`). -/
theorem theorem2_bound_degenerate {δ : ℝ} (h1 : 1 < δ) (h2 : δ < 2) :
    7 * (logb 2 δ / logb 2 (logb 2 δ)) + 3 < 3 := by
  have hL0 : 0 < logb 2 δ := logb_pos one_lt_two h1
  have hL1 : logb 2 δ < 1 := by
    rw [logb_lt_iff_lt_rpow one_lt_two (by linarith)]; norm_num; exact h2
  have hx : logb 2 (logb 2 δ) < 0 := logb_neg one_lt_two hL0 hL1
  have : logb 2 δ / logb 2 (logb 2 δ) < 0 := div_neg_of_pos_of_neg hL0 hx
  linarith

end TreeAA
