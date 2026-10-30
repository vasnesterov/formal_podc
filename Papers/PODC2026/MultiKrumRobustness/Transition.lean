import Papers.PODC2026.MultiKrumRobustness.Defs

/-!
# The transition point `m†` (Theorem 2)

Theorem 2 of the paper: let `m† = m†(n, f) > 0` satisfy `κ^>_2(m†) = (√2 + 1)²`; then
`m†(n, f) = n / (√2 + 1)² · (1 + o(1))` as `f / n → 0`.

Write `C = cKrum = (√2+1)²`, `s = √C = √2 + 1`, `A = √(n - 2f) + √(2f)` (`amp n f`) and
`x = √m`. Then `κ^>_2(m) = ((A x + f) / x²)²`, so `κ^>_2(m) = C` iff `s x² = A x + f`, whose
unique positive root is `x = (A + √(A² + 4 s f)) / (2 s)`. Hence

* `exists_unique_transition` — `m†` exists and is unique (for `0 ≤ f`, `2f < n`);
* `transition_eq` — `m† = mDagger n f` (closed form);
* `mDagger_mul_div` — `m† · C / n = gT (f / n)` *exactly*, where `gT` is continuous, `gT 0 = 1`;
* `theorem_2`, `theorem_2_tendsto` — Theorem 2 (ε-δ and filter forms).

## The paper's proof

The paper squares `s m = A √m + f` to `C m² = A² m + 2 A f √m + f²` and bounds the middle term
by `0 ≤ 2 A f √m ≤ A² m + f²`, obtaining
`(A² + √(A⁴ + 4Cf²)) / (2C) ≤ m† ≤ (A² + √(A⁴ + 2Cf²)) / C`
(`transition_ge_paper`, `transition_le_paper`, both true) and claims that "both bounds reduce to
`n/C (1 + o(1))`". The lower bound does, but the upper bound does not: at `f = 0` it equals
`2 n / C` (`paper_upper_bound_at_f_zero`), twice `m† = n / C` (`mDagger_f_zero`), so it is
`2 n / C (1 + o(1))` (`paper_upper_not_asymp`). Theorem 2 is nevertheless true (`theorem_2`);
only this step of the proof is wrong — the exact formula `mDagger_mul_div` repairs it.
-/

namespace Podc.MultiKrumRobustness

open Filter Topology

lemma cKrum_pos : 0 < cKrum := by unfold cKrum; positivity

/-- `√C = √2 + 1`. -/
lemma sqrt_cKrum : Real.sqrt cKrum = Real.sqrt 2 + 1 := by
  unfold cKrum; rw [Real.sqrt_sq]; positivity

/-- `A = √(n - 2f) + √(2f)`. -/
noncomputable def amp (n f : ℝ) : ℝ := Real.sqrt (n - 2 * f) + Real.sqrt (2 * f)

/-- Closed form of the transition point:
`m† = ((A + √(A² + 4 √C f)) / (2 √C))²`, with `√C = √2 + 1`. -/
noncomputable def mDagger (n f : ℝ) : ℝ :=
  ((amp n f + Real.sqrt (amp n f ^ 2 + 4 * (Real.sqrt 2 + 1) * f)) /
    (2 * (Real.sqrt 2 + 1))) ^ 2

/-- `h(t) = √(1 - 2t) + √(2t)` (so that `A = √n · h(f/n)`). -/
noncomputable def hT (t : ℝ) : ℝ := Real.sqrt (1 - 2 * t) + Real.sqrt (2 * t)

/-- `g(t) = ((h t + √((h t)² + 4 √C t)) / 2)²`; `m† · C / n = g(f / n)`. -/
noncomputable def gT (t : ℝ) : ℝ :=
  ((hT t + Real.sqrt (hT t ^ 2 + 4 * (Real.sqrt 2 + 1) * t)) / 2) ^ 2

lemma amp_pos {n f : ℝ} (_hf : 0 ≤ f) (hnf : 0 < n - 2 * f) : 0 < amp n f := by
  have := Real.sqrt_pos.mpr hnf
  have := Real.sqrt_nonneg (2 * f)
  unfold amp; linarith

/-- `κ^>_2(x²) = ((A x + f) / x²)²` for `x > 0`. -/
lemma kappaGt_sq (n f : ℝ) {x : ℝ} (hx : 0 < x) :
    kappaGt n f (x ^ 2) = ((amp n f * x + f) / x ^ 2) ^ 2 := by
  unfold kappaGt amp
  rw [Real.sqrt_sq hx.le]
  congr 1
  field_simp

/-- `κ^>_2(x²) = C ↔ s x² = A x + f` for `x > 0`, `f ≥ 0`, `A ≥ 0`. -/
lemma kappaGt_sq_eq_iff {n f x : ℝ} (hf : 0 ≤ f) (hnf : 0 < n - 2 * f) (hx : 0 < x) :
    kappaGt n f (x ^ 2) = cKrum ↔ (Real.sqrt 2 + 1) * x ^ 2 = amp n f * x + f := by
  have hA := amp_pos hf hnf
  rw [kappaGt_sq n f hx, cKrum, sq_eq_sq₀ (by positivity) (by positivity),
    div_eq_iff (by positivity), eq_comm]

/-- The positive root of `s x² = A x + f`. -/
lemma root_iff {s A f x : ℝ} (hs : 0 < s) (hA : 0 < A) (hf : 0 ≤ f) (hx : 0 < x) :
    s * x ^ 2 = A * x + f ↔ x = (A + Real.sqrt (A ^ 2 + 4 * s * f)) / (2 * s) := by
  have hD : Real.sqrt (A ^ 2 + 4 * s * f) ^ 2 = A ^ 2 + 4 * s * f :=
    Real.sq_sqrt (by positivity)
  constructor
  · intro h
    have h1 : A ≤ s * x := by
      by_contra h1
      push Not at h1
      nlinarith
    have h2 : (2 * s * x - A) ^ 2 = A ^ 2 + 4 * s * f := by linear_combination 4 * s * h
    have h3 : 2 * s * x - A = Real.sqrt (A ^ 2 + 4 * s * f) := by
      rw [← h2, Real.sqrt_sq (by linarith)]
    field_simp
    linarith
  · rintro rfl
    field_simp
    rw [show s * 4 * f = 4 * s * f by ring]
    linear_combination hD

lemma mDagger_sqrt_pos {n f : ℝ} (hf : 0 ≤ f) (hnf : 0 < n - 2 * f) :
    0 < (amp n f + Real.sqrt (amp n f ^ 2 + 4 * (Real.sqrt 2 + 1) * f)) /
      (2 * (Real.sqrt 2 + 1)) := by
  have := amp_pos hf hnf
  positivity

/-- Characterization of the transition point: `m > 0` solves `κ^>_2(m) = C` iff `m = m†`. -/
lemma kappaGt_eq_iff {n f m : ℝ} (hf : 0 ≤ f) (hnf : 0 < n - 2 * f) (hm : 0 < m) :
    kappaGt n f m = cKrum ↔ m = mDagger n f := by
  have hx : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hmx : m = Real.sqrt m ^ 2 := (Real.sq_sqrt hm.le).symm
  have hs : (0 : ℝ) < Real.sqrt 2 + 1 := by positivity
  have hx0 := mDagger_sqrt_pos hf hnf
  rw [hmx, kappaGt_sq_eq_iff hf hnf hx, root_iff hs (amp_pos hf hnf) hf hx, mDagger,
    sq_eq_sq₀ hx.le hx0.le]

/-- The transition point `m†` exists and is unique (`0 ≤ f`, `2f < n`). -/
theorem exists_unique_transition {n f : ℝ} (hf : 0 ≤ f) (hnf : 0 < n - 2 * f) :
    ∃! m : ℝ, 0 < m ∧ kappaGt n f m = cKrum := by
  have hpos : 0 < mDagger n f := by unfold mDagger; exact pow_pos (mDagger_sqrt_pos hf hnf) 2
  refine ⟨mDagger n f, ⟨hpos, (kappaGt_eq_iff hf hnf hpos).2 rfl⟩, ?_⟩
  rintro m ⟨hm, h⟩
  exact (kappaGt_eq_iff hf hnf hm).1 h

/-- Any transition point equals the closed form `mDagger n f`. -/
theorem transition_eq {n f m : ℝ} (hf : 0 ≤ f) (hnf : 0 < n - 2 * f) (hm : 0 < m)
    (h : kappaGt n f m = cKrum) : m = mDagger n f :=
  (kappaGt_eq_iff hf hnf hm).1 h

lemma mDagger_mul_div_aux {n t : ℝ} (hn : 0 < n) :
    mDagger n (n * t) * cKrum / n = gT t := by
  have hr : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hr0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn
  have hamp : amp n (n * t) = Real.sqrt n * hT t := by
    unfold amp hT
    rw [show n - 2 * (n * t) = n * (1 - 2 * t) by ring, show 2 * (n * t) = n * (2 * t) by ring,
      Real.sqrt_mul hn.le, Real.sqrt_mul hn.le]
    ring
  have hD : Real.sqrt (amp n (n * t) ^ 2 + 4 * (Real.sqrt 2 + 1) * (n * t)) =
      Real.sqrt n * Real.sqrt (hT t ^ 2 + 4 * (Real.sqrt 2 + 1) * t) := by
    rw [hamp, ← Real.sqrt_sq hr0.le, ← Real.sqrt_mul (by positivity), Real.sqrt_sq hr0.le]
    congr 1
    rw [mul_pow, hr]
    ring
  unfold mDagger gT
  rw [hD, hamp, cKrum]
  have hs : (0 : ℝ) < Real.sqrt 2 + 1 := by positivity
  field_simp
  rw [hr]
  ring

/-- Exact normalized form: `m† · C / n = g(f / n)`. -/
theorem mDagger_mul_div {n f : ℝ} (hf : 0 ≤ f) (hnf : 0 < n - 2 * f) :
    mDagger n f * cKrum / n = gT (f / n) := by
  have hn : 0 < n := by linarith
  have := mDagger_mul_div_aux (t := f / n) hn
  rwa [mul_div_cancel₀ _ hn.ne'] at this

lemma continuous_gT : Continuous gT := by
  unfold gT hT
  fun_prop

lemma gT_zero : gT 0 = 1 := by
  simp [gT, hT]

/-- **Theorem 2** of [paper]: the transition point `m†(n, f) > 0`, `κ^>_2(m†) = (√2+1)²`,
satisfies `m† = n / (√2+1)² · (1 + o(1))` as `f / n → 0`. -/
theorem theorem_2 (ε : ℝ) (hε : 0 < ε) :
    ∃ δ > 0, ∀ n f : ℝ, 0 ≤ f → 0 < n - 2 * f → f / n < δ →
      ∀ m : ℝ, 0 < m → kappaGt n f m = cKrum → |m / (n / cKrum) - 1| < ε := by
  obtain ⟨δ, hδ, H⟩ := Metric.continuous_iff.1 continuous_gT 0 ε hε
  refine ⟨δ, hδ, fun n f hf hnf hδn m hm h => ?_⟩
  have hn : 0 < n := by linarith
  rw [transition_eq hf hnf hm h, div_div_eq_mul_div, mDagger_mul_div hf hnf, ← gT_zero]
  have ht : 0 ≤ f / n := div_nonneg hf hn.le
  exact H (f / n) (by rwa [Real.dist_eq, sub_zero, abs_of_nonneg ht])

/-- **Theorem 2** of [paper], filter form: along any filter on which `0 ≤ f`, `2f < n` eventually
and `f / n → 0`, we have `m†(n, f) / (n / C) → 1`. -/
theorem theorem_2_tendsto {ι : Type*} {l : Filter ι} {n f : ι → ℝ}
    (hf : ∀ᶠ i in l, 0 ≤ f i) (hnf : ∀ᶠ i in l, 0 < n i - 2 * f i)
    (ht : Tendsto (fun i => f i / n i) l (𝓝 0)) :
    Tendsto (fun i => mDagger (n i) (f i) / (n i / cKrum)) l (𝓝 1) := by
  have := (continuous_gT.tendsto 0).comp ht
  rw [gT_zero] at this
  refine this.congr' ?_
  filter_upwards [hf, hnf] with i hfi hnfi
  simp only [Function.comp_apply]
  rw [div_div_eq_mul_div, mDagger_mul_div hfi hnfi]

/-! ### The bounds of the paper's proof -/

/-- The paper's lower bound `(A² + √(A⁴ + 4Cf²)) / (2C)`. -/
noncomputable def paperLower (n f : ℝ) : ℝ :=
  (amp n f ^ 2 + Real.sqrt (amp n f ^ 4 + 4 * cKrum * f ^ 2)) / (2 * cKrum)

/-- The paper's upper bound `(A² + √(A⁴ + 2Cf²)) / C`. -/
noncomputable def paperUpper (n f : ℝ) : ℝ :=
  (amp n f ^ 2 + Real.sqrt (amp n f ^ 4 + 2 * cKrum * f ^ 2)) / cKrum

/-- `C m² = (A √m + f)²` for a transition point `m`. -/
lemma transition_sq_eq {n f m : ℝ} (hf : 0 ≤ f) (hnf : 0 < n - 2 * f) (hm : 0 < m)
    (h : kappaGt n f m = cKrum) :
    cKrum * m ^ 2 = (amp n f * Real.sqrt m + f) ^ 2 ∧ amp n f ^ 2 ≤ cKrum * m := by
  have hx : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm
  have hmx : m = Real.sqrt m ^ 2 := (Real.sq_sqrt hm.le).symm
  have hA := amp_pos hf hnf
  rw [hmx, kappaGt_sq_eq_iff hf hnf hx] at h
  set x := Real.sqrt m
  have h1 : amp n f ≤ (Real.sqrt 2 + 1) * x := by
    by_contra h1
    push Not at h1
    nlinarith
  rw [hmx, cKrum]
  constructor
  · rw [← h]; ring
  · have := mul_le_mul h1 h1 hA.le (by positivity)
    nlinarith

/-- The paper's lower bound on `m†` (true). -/
theorem transition_ge_paper {n f m : ℝ} (hf : 0 ≤ f) (hnf : 0 < n - 2 * f) (hm : 0 < m)
    (h : kappaGt n f m = cKrum) : paperLower n f ≤ m := by
  obtain ⟨h1, h2⟩ := transition_sq_eq hf hnf hm h
  have hA := amp_pos hf hnf
  have hC := cKrum_pos
  have hx := Real.sqrt_nonneg m
  have hq : amp n f ^ 2 * m + f ^ 2 ≤ cKrum * m ^ 2 := by
    have hmx : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
    rw [h1]; nlinarith [mul_nonneg (mul_nonneg hA.le hf) hx]
  unfold paperLower
  rw [div_le_iff₀ (by positivity)]
  have : Real.sqrt (amp n f ^ 4 + 4 * cKrum * f ^ 2) ≤ 2 * cKrum * m - amp n f ^ 2 := by
    rw [Real.sqrt_le_iff]
    constructor
    · nlinarith
    · nlinarith
  linarith

/-- The paper's upper bound on `m†` (true). -/
theorem transition_le_paper {n f m : ℝ} (hf : 0 ≤ f) (hnf : 0 < n - 2 * f) (hm : 0 < m)
    (h : kappaGt n f m = cKrum) : m ≤ paperUpper n f := by
  obtain ⟨h1, -⟩ := transition_sq_eq hf hnf hm h
  have hC := cKrum_pos
  have hmx : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm.le
  have hq : cKrum * m ^ 2 ≤ 2 * amp n f ^ 2 * m + 2 * f ^ 2 := by
    rw [h1]; nlinarith [sq_nonneg (amp n f * Real.sqrt m - f)]
  unfold paperUpper
  rw [le_div_iff₀ hC]
  have : |cKrum * m - amp n f ^ 2| ≤ Real.sqrt (amp n f ^ 4 + 2 * cKrum * f ^ 2) :=
    Real.abs_le_sqrt (by nlinarith)
  have := le_abs_self (cKrum * m - amp n f ^ 2)
  linarith

/-- At `f = 0` the transition point is exactly `n / C`. -/
theorem mDagger_f_zero {n : ℝ} (hn : 0 < n) : mDagger n 0 = n / cKrum := by
  have hs : (0 : ℝ) < Real.sqrt 2 + 1 := by positivity
  have hr : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  unfold mDagger amp cKrum
  simp only [mul_zero, sub_zero, Real.sqrt_zero, add_zero]
  rw [Real.sqrt_sq (Real.sqrt_nonneg n)]
  field_simp
  rw [hr]
  ring

/-- **Gap in the paper's proof.** At `f = 0` the paper's upper bound equals `2 n / C`, twice the
true value `m† = n / C`; so it does *not* "reduce to `n/C (1 + o(1))`". -/
theorem paper_upper_bound_at_f_zero {n : ℝ} (hn : 0 < n) :
    paperUpper n 0 = 2 * (n / cKrum) ∧ paperUpper n 0 = 2 * mDagger n 0 := by
  have hr : Real.sqrt n ^ 2 = n := Real.sq_sqrt hn.le
  have hup : paperUpper n 0 = 2 * (n / cKrum) := by
    unfold paperUpper amp
    simp only [mul_zero, sub_zero, Real.sqrt_zero, add_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow]
    rw [show Real.sqrt n ^ 4 = (Real.sqrt n ^ 2) ^ 2 by ring, hr, Real.sqrt_sq hn.le]
    ring
  exact ⟨hup, by rw [hup, mDagger_f_zero hn]⟩

/-- The paper's upper bound is not `n/C (1 + o(1))` as `f / n → 0` (not even within a factor
`3/2`). -/
theorem paper_upper_not_asymp :
    ¬ ∃ δ > 0, ∀ n f : ℝ, 0 ≤ f → 0 < n - 2 * f → f / n < δ →
      |paperUpper n f / (n / cKrum) - 1| < 1 / 2 := by
  rintro ⟨δ, hδ, H⟩
  have := H 1 0 le_rfl (by norm_num) (by simpa using hδ)
  rw [(paper_upper_bound_at_f_zero one_pos).1,
    mul_div_cancel_right₀ _ (div_pos one_pos cKrum_pos).ne'] at this
  norm_num [abs_of_pos] at this

end Podc.MultiKrumRobustness
