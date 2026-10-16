import Papers.PODC2025.MinimalistLE.Basic

/-!
# The pair chain of two leaders and its Lyapunov function

While a node is a leader, its phase follows the 3-state chain `W → B` (coin `true`), `W → W`
(coin `false`), `B → F → W`. For two leaders `u, v` we follow `(x_u, x_v, Δ)` with
`Δ = N(u) − N(v)` (difference of beep counts). With `a = 1 + 2p`, the function
`M = Δ + h(x_u) − h(x_v)` (`h(W) = 0`, `h(B) = −2p/a`, `h(F) = −p/a`) is a martingale whose
conditional variance has stationary mean `v̄ = 2p(1−p)/a³`; adding the corrector
`k(x_u) + k(x_v)` (`k(W) = 0`, `k(B) = 2p(1−p)/a³`, `k(F) = p(1−p)/a³`) gives the Lyapunov function
`g = ((D+2)² − M² + k(x_u) + k(x_v)) / v̄` with exact drift `−1` (`lyap_drift`).
-/

namespace MinimalistLE

instance : Fintype Phase := ⟨{.W, .B, .F}, by intro x; cases x <;> simp⟩

/-- One step of a leader's phase with coin `b`. -/
def cstep : Phase → Bool → Phase
  | .W, b => if b then .B else .W
  | .B, _ => .F
  | .F, _ => .W

/-- `1{x = B}`. -/
def ind (x : Phase) : ℤ := if x = .B then 1 else 0

/-- States of the pair chain: `(x_u, x_v, Δ)`. -/
abbrev PS := Phase × Phase × ℤ

/-- One step of the pair chain with coins `bu`, `bv`. -/
def pstep (y : PS) (bu bv : Bool) : PS :=
  (cstep y.1 bu, cstep y.2.1 bv, y.2.2 + ind (cstep y.1 bu) - ind (cstep y.2.1 bv))

/-- Probability of coin value `b`. -/
noncomputable def wt (p : ℝ) (b : Bool) : ℝ := if b then p else 1 - p

noncomputable def hfun (p : ℝ) : Phase → ℝ
  | .W => 0
  | .B => -2 * p / (1 + 2 * p)
  | .F => -p / (1 + 2 * p)

noncomputable def kfun (p : ℝ) : Phase → ℝ
  | .W => 0
  | .B => 2 * p * (1 - p) / (1 + 2 * p) ^ 3
  | .F => p * (1 - p) / (1 + 2 * p) ^ 3

/-- The Lyapunov function. -/
noncomputable def lyap (p : ℝ) (D : ℕ) (y : PS) : ℝ :=
  (((D : ℝ) + 2) ^ 2 - ((y.2.2 : ℝ) + hfun p y.1 - hfun p y.2.1) ^ 2 + kfun p y.1 + kfun p y.2.1)
    * (1 + 2 * p) ^ 3 / (2 * p * (1 - p))

/-- Exact drift `−1` of the Lyapunov function along the pair chain. -/
theorem lyap_drift {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (D : ℕ) (y : PS) :
    ∑ bu : Bool, ∑ bv : Bool, wt p bu * wt p bv * lyap p D (pstep y bu bv) = lyap p D y - 1 := by
  obtain ⟨xu, xv, δ⟩ := y
  have h1 : (1 + 2 * p) ≠ 0 := by linarith
  have h2 : p ≠ 0 := hp0.ne'
  have h3 : (1 - p) ≠ 0 := by linarith
  cases xu <;> cases xv <;>
    simp [pstep, cstep, ind, wt, lyap, hfun, kfun] <;> field_simp <;> ring

section bounds
variable {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1)
include hp0 hp1

theorem hfun_bounds (x : Phase) : -(2 * p / (1 + 2 * p)) ≤ hfun p x ∧ hfun p x ≤ 0 := by
  have ha : 0 < 1 + 2 * p := by linarith
  cases x <;> simp only [hfun]
  · constructor <;> [exact neg_nonpos.2 (by positivity); exact le_rfl]
  · constructor
    · rw [neg_mul, neg_div]
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le
  · constructor
    · rw [neg_div, neg_le_neg_iff]; exact div_le_div_of_nonneg_right (by linarith) ha.le
    · exact div_nonpos_of_nonpos_of_nonneg (by linarith) ha.le

theorem kfun_bounds (x : Phase) :
    0 ≤ kfun p x ∧ kfun p x ≤ 2 * p * (1 - p) / (1 + 2 * p) ^ 3 := by
  have ha : 0 < 1 + 2 * p := by linarith
  have h1 : 0 < 1 - p := by linarith
  cases x <;> simp only [kfun]
  · exact ⟨le_rfl, by positivity⟩
  · exact ⟨by positivity, le_rfl⟩
  · exact ⟨by positivity, div_le_div_of_nonneg_right (by nlinarith) (by positivity)⟩

theorem hdiff_bound (x y : Phase) : |hfun p x - hfun p y| < 1 := by
  have hx := hfun_bounds hp0 hp1 x
  have hy := hfun_bounds hp0 hp1 y
  have : 2 * p / (1 + 2 * p) < 1 := by rw [div_lt_one (by linarith)]; linarith
  rw [abs_lt]; constructor <;> linarith

/-- The Lyapunov function is nonnegative on states with `|Δ| ≤ D + 1`. -/
theorem lyap_nonneg (D : ℕ) (y : PS) (hy : |y.2.2| ≤ (D : ℤ) + 1) : 0 ≤ lyap p D y := by
  obtain ⟨xu, xv, δ⟩ := y
  have hδ : |(δ : ℝ)| ≤ D + 1 := by exact_mod_cast hy
  have he := hdiff_bound hp0 hp1 xu xv
  have hsq : ((δ : ℝ) + hfun p xu - hfun p xv) ^ 2 ≤ ((D : ℝ) + 2) ^ 2 := by
    have : |(δ : ℝ) + hfun p xu - hfun p xv| ≤ D + 2 := by
      calc |(δ : ℝ) + hfun p xu - hfun p xv| = |(δ : ℝ) + (hfun p xu - hfun p xv)| := by ring_nf
        _ ≤ |(δ : ℝ)| + |hfun p xu - hfun p xv| := abs_add_le _ _
        _ ≤ D + 2 := by linarith
    exact sq_le_sq' (abs_le.1 this).1 (abs_le.1 this).2
  have hk1 := (kfun_bounds hp0 hp1 xu).1
  have hk2 := (kfun_bounds hp0 hp1 xv).1
  have h1 : 0 < 1 - p := by linarith
  unfold lyap
  apply div_nonneg (mul_nonneg (by simp only; linarith) (by positivity)) (by positivity)

/-- Upper bound `G_max = (D+2)²(1+2p)³/(2p(1−p)) + 2` on states with `|Δ| ≤ D`. -/
theorem lyap_le (D : ℕ) (y : PS) :
    lyap p D y ≤ ((D : ℝ) + 2) ^ 2 * (1 + 2 * p) ^ 3 / (2 * p * (1 - p)) + 2 := by
  obtain ⟨xu, xv, δ⟩ := y
  have hk1 := (kfun_bounds hp0 hp1 xu).2
  have hk2 := (kfun_bounds hp0 hp1 xv).2
  have h1 : 0 < 1 - p := by linarith
  have hc : 0 < (1 + 2 * p) ^ 3 / (2 * p * (1 - p)) := by positivity
  have hkc : (2 * p * (1 - p) / (1 + 2 * p) ^ 3) * ((1 + 2 * p) ^ 3 / (2 * p * (1 - p))) = 1 := by
    field_simp
  unfold lyap
  simp only
  rw [mul_div_assoc, mul_div_assoc]
  have hM := sq_nonneg ((δ : ℝ) + hfun p xu - hfun p xv)
  nlinarith

end bounds

end MinimalistLE
