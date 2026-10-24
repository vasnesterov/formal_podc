import Papers.PODC2011.ErrorFreeMultivaluedBC.Theorem

/-!
# Communication complexity (Section 3.4)

Liang–Vaidya, PODC 2011 (arXiv:1101.3520), Section 3.4, equations (1)–(3).

The model of `Algorithm.lean` does not represent bits on the wire, so we verify the *accounting*
of Section 3.4 on top of the diagnosis bound of Theorem 1:

* `Run.cost`: the paper's per-generation counts (`s = D/(n-2t)` bits per symbol, `B` bits per
  instance of `Broadcast_Single_Bit`), summed over the generations, a diagnosis stage costing
  extra only in the generations that perform it.
* `Run.cost_le` (equation (1)): `cost ≤ N · (matching + checking) + t(t+1) · diagnosis`.
* `ccon_opt` (equation (2)): with the paper's choice of `D`, the two `D`-dependent terms of (1)
  become `2B√(L (n²-n+t) t(t+1)(n-t)/(n-2t))`.
* `ccon_opt_le` (equation (3)): if `B ≤ b n²`, then `C_con(L) ≤ 3nL + 4b n⁴ √L + b n⁶`, i.e.
  `O(nL + n⁴ L^{1/2} + n⁶)`.

Equations (2)–(3) are real-valued, as in the paper: `D` is not rounded to a multiple of `n - 2t`
dividing `L` (see `differencies.md`).
-/

namespace Podc.ErrorFreeMultivaluedBC

open Finset

/-- Bits of the matching and checking stages of one generation (Section 3.4): `n(n-1)` symbols of
`s` bits, `n(n-1)` broadcast bits for the vectors `M_i`, `t` broadcast bits `Detected_j`. -/
def baseCost (n t s B : ℕ) : ℕ := n * (n - 1) * s + n * (n - 1) * B + t * B

/-- Bits of one diagnosis stage (Section 3.4): `n - t` broadcast symbols of `s` bits and `n(n-t)`
broadcast bits `Trust_i/P_match`. -/
def diagCost (n t s B : ℕ) : ℕ := (n - t) * s * B + n * (n - t) * B

namespace Run

variable {n t : ℕ} {α β : Type*} (A : Alg n t α β) (r : Run n α β)

open Classical in
/-- The communication of the first `N` generations, counted as in Section 3.4. -/
noncomputable def cost (N s B : ℕ) : ℕ :=
  ∑ g ∈ range N, (baseCost n t s B + if (r.gen A g).Diagnosed then diagCost n t s B else 0)

theorem cost_eq (N s B : ℕ) :
    r.cost A N s B = N * baseCost n t s B + r.numDiag A N * diagCost n t s B := by
  classical
  unfold cost numDiag
  rw [sum_add_distrib, sum_const, card_range, smul_eq_mul, ← sum_filter, sum_const,
    smul_eq_mul]

/-- **Equation (1)** (repaired algorithm, `3t < n`). -/
theorem cost_le (hnt : 3 * t < n) (hV : r.Valid A) (hvar : A.var = .repaired) (N s B : ℕ) :
    r.cost A N s B ≤ N * baseCost n t s B + t * (t + 1) * diagCost n t s B := by
  rw [cost_eq]
  have := r.theorem_1_numDiag A hnt hV hvar N
  gcongr

end Run

/-! ### Equations (2) and (3) -/

/-- The right-hand side of equation (1) as a real function of the generation size `D`, with
`L/D` generations and symbols of `D/(n-2t)` bits. -/
noncomputable def ccon (n t L B D : ℝ) : ℝ :=
  L / D * (n * (n - 1) / (n - 2 * t) * D + n * (n - 1) * B + t * B) +
    t * (t + 1) * ((n - t) / (n - 2 * t) * D + n * (n - t)) * B

/-- The paper's choice `D = √((n² - n + t)(n - 2t)L / (t(t+1)(n-t)))`. -/
noncomputable def optD (n t L : ℝ) : ℝ :=
  Real.sqrt ((n ^ 2 - n + t) * (n - 2 * t) * L / (t * (t + 1) * (n - t)))

/-- **Equation (2).** -/
theorem ccon_opt {n t L B : ℝ} (ht : 1 ≤ t) (hnt : 3 * t < n) (hL : 0 < L) :
    ccon n t L B (optD n t L) = n * (n - 1) / (n - 2 * t) * L +
      2 * B * Real.sqrt (L * ((n ^ 2 - n + t) * t * (t + 1) * (n - t) / (n - 2 * t))) +
      t * (t + 1) * n * (n - t) * B := by
  have h1 : 0 < n - 2 * t := by linarith
  have h2 : 0 < n - t := by linarith
  have h3 : 0 < n ^ 2 - n + t := by nlinarith
  have h4 : 0 < t * (t + 1) := by positivity
  have hn2 : n - 2 * t ≠ 0 := h1.ne'
  have hn2' : n - t * 2 ≠ 0 := by intro h; linarith
  have hnt0 : n - t ≠ 0 := h2.ne'
  set a := n ^ 2 - n + t
  set D := optD n t L
  have hDpos : 0 < D := Real.sqrt_pos.mpr (by positivity)
  have hD2 : D ^ 2 = a * (n - 2 * t) * L / (t * (t + 1) * (n - t)) :=
    Real.sq_sqrt (by positivity)
  set q := Real.sqrt (L * (a * t * (t + 1) * (n - t) / (n - 2 * t)))
  have hq2 : q ^ 2 = L * (a * t * (t + 1) * (n - t) / (n - 2 * t)) :=
    Real.sq_sqrt (by positivity)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  -- `q = L a / D = t(t+1)(n-t)/(n-2t) · D`
  have hqD : q * D = L * a := by
    have : (q * D) ^ 2 = (L * a) ^ 2 := by
      rw [mul_pow, hq2, hD2]; field_simp
    have hLa : 0 ≤ L * a := by positivity
    nlinarith [sq_nonneg (q * D - L * a), sq_nonneg (q * D + L * a), mul_nonneg hq hDpos.le]
  have hqD' : q * (n - 2 * t) = t * (t + 1) * (n - t) * D := by
    have hD : D ≠ 0 := hDpos.ne'
    have : q * (n - 2 * t) * D = t * (t + 1) * (n - t) * D * D := by
      rw [show q * (n - 2 * t) * D = (q * D) * (n - 2 * t) by ring, hqD,
        show t * (t + 1) * (n - t) * D * D = t * (t + 1) * (n - t) * D ^ 2 by ring, hD2]
      field_simp
    exact mul_right_cancel₀ hD this
  unfold ccon
  have hD : D ≠ 0 := hDpos.ne'
  have e1 : L / D * (n * (n - 1) * B + t * B) = B * q := by
    field_simp
    have : n * (n - 1) + t = a := by simp only [a]; ring
    linear_combination (L * B) * this - B * hqD
  have e2 : t * (t + 1) * ((n - t) / (n - 2 * t) * D) * B = B * q := by
    field_simp
    linear_combination -B * hqD'
  calc L / D * (n * (n - 1) / (n - 2 * t) * D + n * (n - 1) * B + t * B) +
        t * (t + 1) * ((n - t) / (n - 2 * t) * D + n * (n - t)) * B
      = n * (n - 1) / (n - 2 * t) * L + L / D * (n * (n - 1) * B + t * B) +
        t * (t + 1) * ((n - t) / (n - 2 * t) * D) * B + t * (t + 1) * n * (n - t) * B := by
        field_simp; ring
    _ = _ := by rw [e1, e2]; ring

/-- **Equation (3)**: with `B ≤ b n²` bits per broadcast bit (error-free 1-bit broadcast with
`Θ(n²)` bits), `C_con(L) ≤ 3nL + 4b n⁴ √L + b n⁶`, i.e. `O(nL + n⁴ L^{0.5} + n⁶)`. -/
theorem ccon_opt_le {n t L B b : ℝ} (ht : 1 ≤ t) (hnt : 3 * t < n) (hL : 0 < L) (hB : 0 ≤ B)
    (hBb : B ≤ b * n ^ 2) :
    ccon n t L B (optD n t L) ≤ 3 * n * L + 4 * b * n ^ 4 * Real.sqrt L + b * n ^ 6 := by
  rw [ccon_opt ht hnt hL]
  have hn : 3 < n := by linarith
  have h1 : 0 < n - 2 * t := by linarith
  have h2 : 0 < n - t := by linarith
  have ht1 : t + 1 ≤ n := by linarith
  -- first term
  have e1 : n * (n - 1) / (n - 2 * t) * L ≤ 3 * n * L := by
    apply mul_le_mul_of_nonneg_right _ hL.le
    rw [div_le_iff₀ h1]; nlinarith
  -- second term
  have hin : (n ^ 2 - n + t) * t * (t + 1) * (n - t) / (n - 2 * t) ≤ 4 * n ^ 4 := by
    rw [div_le_iff₀ h1]
    have ha : 0 ≤ n ^ 2 - n + t := by nlinarith
    have ha' : n ^ 2 - n + t ≤ n ^ 2 := by nlinarith
    have htt : t * (t + 1) ≤ n ^ 2 := by nlinarith
    have hnt' : n - t ≤ 3 * (n - 2 * t) := by linarith
    calc (n ^ 2 - n + t) * t * (t + 1) * (n - t)
        = (n ^ 2 - n + t) * (t * (t + 1)) * (n - t) := by ring
      _ ≤ n ^ 2 * n ^ 2 * (3 * (n - 2 * t)) := by
        apply mul_le_mul (mul_le_mul ha' htt (by positivity) (by positivity)) hnt' h2.le
        positivity
      _ ≤ 4 * n ^ 4 * (n - 2 * t) := by nlinarith [pow_pos (show (0:ℝ) < n by linarith) 4]
  have hsq : Real.sqrt (L * ((n ^ 2 - n + t) * t * (t + 1) * (n - t) / (n - 2 * t))) ≤
      2 * n ^ 2 * Real.sqrt L := by
    rw [show 2 * n ^ 2 * Real.sqrt L = Real.sqrt (L * (2 * n ^ 2) ^ 2) by
      rw [Real.sqrt_mul hL.le, Real.sqrt_sq (by positivity)]; ring]
    apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ hL.le
    nlinarith
  have e2 : 2 * B * Real.sqrt (L * ((n ^ 2 - n + t) * t * (t + 1) * (n - t) / (n - 2 * t))) ≤
      4 * b * n ^ 4 * Real.sqrt L := by
    have hsL := Real.sqrt_nonneg L
    calc _ ≤ 2 * B * (2 * n ^ 2 * Real.sqrt L) := by gcongr
      _ ≤ 2 * (b * n ^ 2) * (2 * n ^ 2 * Real.sqrt L) := by gcongr
      _ = 4 * b * n ^ 4 * Real.sqrt L := by ring
  -- third term
  have e3 : t * (t + 1) * n * (n - t) * B ≤ b * n ^ 6 := by
    have htt : t * (t + 1) ≤ n ^ 2 := by nlinarith
    have : t * (t + 1) * n * (n - t) ≤ n ^ 4 := by
      have : n * (n - t) ≤ n ^ 2 := by nlinarith
      nlinarith [mul_le_mul htt this (by positivity) (by positivity)]
    calc _ ≤ n ^ 4 * (b * n ^ 2) := by
          apply mul_le_mul this hBb hB (by positivity)
      _ = b * n ^ 6 := by ring
  linarith

end Podc.ErrorFreeMultivaluedBC
