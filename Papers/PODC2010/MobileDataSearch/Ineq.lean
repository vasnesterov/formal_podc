import Mathlib

/-!
# Real inequalities behind the `8/7` bound (Theorem 4)

Bar-Noy, Cheilaris, Feng, Levin, *Finding mobile data under delay constraints with searching costs*,
PODC 2010.

The paper's proof of Theorem 4 reduces every instance to `N = 3, 4` boxes (Lemma 4, whose proof
is flawed) and then omits the case analysis for `N = 3, 4` (Lemmas 5, 6). We replace this by a
direct argument (see `TwoRounds.lean`): for every two-round strategy `S` the prefixes `k` and
`k + 1` of the ratio order bracketing the weight of `S` already give the bound. The resulting
real inequality (`key_real`) is proved here.

Notation (all quantities normalised so that total probability and total cost are `1`):
`ℓ x = r x + V` is the line through the "critical" box, `φ x = ℓ x · (1 - x)` the gain
`p(S) · w(Sᶜ)` of a (fractional) first round of weight `x`. After the change of variables
`s = r (1 - x) / (r + V)` we get `φ = K · s (1 - s)` with `K = (r + V)² / r`, which leads to the
three-variable inequalities `ineq_case1`, `ineq_case2`.
-/

namespace Podc.MobileDataSearch

/-- `8 m(1-m) - 8m² + (H+8)m - 7H + 5H² ≥ 0`-type auxiliary bound used in both cases. -/
private lemma aux_quad (m H : ℝ) (h1 : 1 - H ≤ m) (h2 : m ≤ H) (h3 : 2 * H - 1 ≤ m) :
    0 ≤ 8 * m ^ 2 - (H + 8) * m + 7 * H - 5 * H ^ 2 := by
  rcases le_total H (51 / 100) with hA | hA
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hA),
      mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h1)]
  rcases le_total H (78 / 100) with hB | hB
  · nlinarith [mul_nonneg (sub_nonneg.2 hA) (sub_nonneg.2 hB), sq_nonneg (16 * m - H - 8)]
  · nlinarith [mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 hB), sq_nonneg (5 * H - 4),
      mul_nonneg (sub_nonneg.2 h3) (sub_nonneg.2 h3)]

/-- Three-variable form of the critical box being in the first round ("case 2"). -/
lemma ineq_case2 (L m H : ℝ) (h0 : 0 ≤ L) (h1 : L ≤ m) (h2 : m ≤ H) (h3 : H - L + m ≤ 1) :
    8 * (m * (1 - m)) ≤ (H - L + m) * (1 - L) + 7 * max (H * (1 - H)) (L * (1 - L)) := by
  rcases le_total (H + L) 1 with hB | hA
  · -- `h H ≥ h L`
    have : L * (1 - L) ≤ H * (1 - H) := by nlinarith
    rw [max_eq_left this]
    nlinarith [mul_nonneg (sub_nonneg.2 hB) h0, mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h1),
      sq_nonneg (5 * L - 1), mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h3),
      mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h3), sq_nonneg (m - 2 * L), sq_nonneg (H - 2 * m),
      mul_nonneg h0 (sub_nonneg.2 h1), mul_nonneg (sub_nonneg.2 hB) (sub_nonneg.2 h2)]
  · have : H * (1 - H) ≤ L * (1 - L) := by nlinarith
    rw [max_eq_right this]
    have hL1 : L ≤ 1 := by linarith
    rcases le_total (1 - L) m with hm | hm
    · have : (H - m) * (1 - L) ≥ 0 := mul_nonneg (by linarith) (by linarith)
      nlinarith [mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 h1),
        mul_nonneg (sub_nonneg.2 hm) (sub_nonneg.2 hm)]
    · have hH : (H - (1 - L)) * (1 - L) ≥ 0 := mul_nonneg (by linarith) (by linarith)
      have hm2 : m ≤ 2 * L := by linarith
      suffices 8 * m ^ 2 - (7 + L) * m + (1 - L) * (1 + 5 * L) ≥ 0 by nlinarith
      rcases le_total L (7 / 31) with hL | hL
      · nlinarith [mul_nonneg (sub_nonneg.2 hm2) (sub_nonneg.2 hL), sq_nonneg (5 * L - 1),
          sq_nonneg (2 * L - m)]
      rcases le_total L (12 / 25) with hL' | hL'
      · nlinarith [mul_nonneg (sub_nonneg.2 hL) (sub_nonneg.2 hL'),
          sq_nonneg (16 * (2 * L - m) - (31 * L - 7))]
      · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 hL'),
          mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h1)]

/-- Three-variable form of the critical box being in the second round ("case 1"). -/
lemma ineq_case1 (L m H : ℝ) (h0 : 0 ≤ L) (h1 : L ≤ m) (h2 : m ≤ H) (h3 : H ≤ 1)
    (h4 : H ≤ L + m) :
    8 * (m * (1 - m)) ≤ H * (1 - L - m + H) + 7 * max (H * (1 - H)) (L * (1 - L)) := by
  rcases le_total (H + L) 1 with hB | hA
  · have : L * (1 - L) ≤ H * (1 - H) := by nlinarith
    rw [max_eq_left this]
    rcases le_total m (1 - H) with hm | hm
    · nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 hm),
        mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h1),
        mul_nonneg (le_trans h0 (le_trans h1 h2)) (sub_nonneg.2 h1),
        mul_nonneg (sub_nonneg.2 h2) (le_trans h0 (le_trans h1 h2))]
    · have := aux_quad m H (by linarith) h2 (by linarith)
      nlinarith [mul_nonneg (le_trans h0 (le_trans h1 h2)) (show 0 ≤ 1 - H - L by linarith)]
  · have : H * (1 - H) ≤ L * (1 - L) := by nlinarith
    rw [max_eq_right this]
    rcases le_total (1 - H) (H - m) with hc | hc
    · have e0 : 0 ≤ 8 * m ^ 2 - 7 * m + 8 * (H - m) - 7 * (H - m) ^ 2 := by
        nlinarith [sq_nonneg (5 * m - 3), sq_nonneg (5 * (H - m) - 1),
          mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 h2), mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 h3)]
      rcases le_total 0 (7 - H - 7 * (L + (H - m))) with hs | hs
      · nlinarith [mul_nonneg (show 0 ≤ L - (H - m) by linarith) hs]
      · nlinarith [mul_nonneg (sub_nonneg.2 h1) (show 0 ≤ 7 * (L + m) - (7 - H) by linarith)]
    · have e0 := aux_quad m H (by linarith) h2 (by linarith)
      rcases le_total 0 (7 - H - 7 * (L + (1 - H))) with hs | hs
      · nlinarith [mul_nonneg (show 0 ≤ L - (1 - H) by linarith) hs]
      · nlinarith [mul_nonneg (sub_nonneg.2 h1) (show 0 ≤ 7 * (L + m) - (7 - H) by linarith)]

/-- The gain `φ x = (r x + V)(1 - x)` of a fractional first round of weight `x`. -/
def phi (r V x : ℝ) : ℝ := (r * x + V) * (1 - x)

/-- `φ` in the scaled variable `s = r (1 - x) / (r + V)`. -/
private lemma phi_eq (r V x : ℝ) (hr : 0 < r) (hk : 0 < r + V) :
    phi r V x = (r + V) ^ 2 / r * ((r * (1 - x) / (r + V)) * (1 - r * (1 - x) / (r + V))) := by
  unfold phi
  field_simp
  ring

/-- Transfer of a three-variable inequality to `φ`: if
`8 h(s b) ≤ c + 7 max (h (s x₁)) (h (s x₂))` with `c ≤ r / (r+V)²`, then
`8 φ b ≤ 1 + 7 max (φ x₁) (φ x₂)`. -/
private lemma transfer (r V x1 b x2 c : ℝ) (hr : 0 < r) (hk : 0 < r + V)
    (hc : c ≤ r / (r + V) ^ 2)
    (h : 8 * ((r * (1 - b) / (r + V)) * (1 - r * (1 - b) / (r + V))) ≤
      c + 7 * max ((r * (1 - x1) / (r + V)) * (1 - r * (1 - x1) / (r + V)))
        ((r * (1 - x2) / (r + V)) * (1 - r * (1 - x2) / (r + V)))) :
    8 * phi r V b ≤ 1 + 7 * max (phi r V x1) (phi r V x2) := by
  have hK : 0 < (r + V) ^ 2 / r := by positivity
  rw [phi_eq r V b hr hk, phi_eq r V x1 hr hk, phi_eq r V x2 hr hk, ← mul_max_of_nonneg _ _ hK.le]
  have h1 : (r + V) ^ 2 / r * c ≤ 1 := by
    calc (r + V) ^ 2 / r * c ≤ (r + V) ^ 2 / r * (r / (r + V) ^ 2) :=
          mul_le_mul_of_nonneg_left hc hK.le
      _ = 1 := by field_simp
  nlinarith [mul_le_mul_of_nonneg_left h hK.le]

/-- Core inequality, critical box in the first round. -/
lemma core2 (r V x1 b x2 : ℝ) (hr : 0 < r) (hV : 0 ≤ V) (h1 : 0 ≤ x1) (h1b : x1 ≤ b)
    (hb2 : b ≤ x2) (h2 : x2 ≤ 1) (hd : x2 - x1 ≤ b) (hP : r * x2 + V ≤ 1) :
    8 * phi r V b ≤ 1 + 7 * max (phi r V x1) (phi r V x2) := by
  have hk : 0 < r + V := by linarith
  set κ := r + V
  set L := r * (1 - x2) / κ
  set m := r * (1 - b) / κ
  set H := r * (1 - x1) / κ
  have hL0 : 0 ≤ L := by positivity
  have hLm : L ≤ m := div_le_div_of_nonneg_right (by nlinarith) hk.le
  have hmH : m ≤ H := div_le_div_of_nonneg_right (by nlinarith) hk.le
  have hHLm : H - L + m = r * (x2 - x1 + 1 - b) / κ := by simp only [H, L, m]; field_simp; ring
  have h1L : 1 - L = (V + r * x2) / κ := by simp only [L, κ]; field_simp; ring
  apply transfer r V x1 b x2 ((H - L + m) * (1 - L)) hr hk
  · rw [hHLm, h1L, div_mul_div_comm, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (x2 - x1 + 1 - b) * (V + r * x2) ≤ 1 := by
      have ha : 0 ≤ x2 - x1 + 1 - b := by linarith
      have hb : 0 ≤ V + r * x2 := by nlinarith
      nlinarith [mul_le_mul ( show x2 - x1 + 1 - b ≤ 1 by linarith) (show V + r * x2 ≤ 1 by linarith) hb
        (by norm_num : (0:ℝ) ≤ 1)]
    have hκ2 : (r + V) ^ 2 = κ * κ := by simp only [κ]; ring
    rw [hκ2]
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hr.le (mul_self_nonneg κ))]
  · have := ineq_case2 L m H hL0 hLm hmH (by
      rw [hHLm, div_le_one hk]; nlinarith)
    rw [max_comm] at this ⊢
    exact this

/-- Core inequality, critical box in the second round. -/
lemma core1 (r V x1 b x2 : ℝ) (hr : 0 < r) (hV : 0 ≤ V) (hk1 : 1 ≤ r + V) (h1 : 0 ≤ x1)
    (h1b : x1 ≤ b) (hb2 : b ≤ x2) (h2 : x2 ≤ 1) (hP : V + r * (x2 + b - x1) ≤ 1) :
    8 * phi r V b ≤ 1 + 7 * max (phi r V x1) (phi r V x2) := by
  have hk : 0 < r + V := by linarith
  set κ := r + V
  set L := r * (1 - x2) / κ
  set m := r * (1 - b) / κ
  set H := r * (1 - x1) / κ
  have hL0 : 0 ≤ L := by positivity
  have hLm : L ≤ m := div_le_div_of_nonneg_right (by nlinarith) hk.le
  have hmH : m ≤ H := div_le_div_of_nonneg_right (by nlinarith) hk.le
  have hsum : x2 + b - x1 ≤ 1 := by
    by_contra hc
    nlinarith
  have hH1 : H ≤ 1 := by
    rw [div_le_one hk]; nlinarith
  have hHLm : H ≤ L + m := by
    simp only [H, L, m]; rw [← add_div]; gcongr; nlinarith
  have hexpr : H * (1 - L - m + H) = r * (1 - x1) * (V + r * (x2 + b - x1)) / κ ^ 2 := by
    simp only [H, L, m, κ]; field_simp; ring
  apply transfer r V x1 b x2 (H * (1 - L - m + H)) hr hk
  · rw [hexpr, div_le_div_iff₀ (by positivity) (by positivity)]
    have hb : 0 ≤ V + r * (x2 + b - x1) := by
      have : 0 ≤ x2 + b - x1 := by linarith
      positivity
    have : (1 - x1) * (V + r * (x2 + b - x1)) ≤ 1 := by
      nlinarith [mul_le_mul (show 1 - x1 ≤ 1 by linarith) hP hb (by norm_num : (0:ℝ) ≤ 1)]
    have hκ2 : (r + V) ^ 2 = κ ^ 2 := by simp only [κ]
    rw [hκ2]
    nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg hr.le (sq_nonneg κ))]
  · have := ineq_case1 L m H hL0 hLm hmH hH1 hHLm
    rw [max_comm] at this ⊢
    exact this

/-- The real inequality behind Theorem 4. Normalised instance (total probability and total cost
`1`); the prefix `Q` of the ratio order has cost `u` and probability `U`, the next ("critical") box
has cost `δ > 0` and probability `Δ`; the first round `S` of an arbitrary strategy has cost `b`,
`u ≤ b ≤ u + δ`, and probability `a`. Ratio order: `Q` has ratio `≥ Δ/δ` (`hpre`), the boxes after
the critical one have ratio `≤ Δ/δ` (`hsuf`), hence `a ≤ U + (Δ/δ)(b - u)` (`ha`). Integrality:
either the critical box is not in `S` (then `a ≤ 1 - Δ`) or it is (then `δ ≤ b`).
Conclusion: `8 G(S) ≤ 1 + 7 max (G(Q), G(Q ∪ {critical}))` for `G(X) = p(X) w(Xᶜ)`. -/
lemma key_real (u U δ Δ a b : ℝ) (hu : 0 ≤ u) (hδ : 0 < δ) (hub : u ≤ b) (hbu : b ≤ u + δ)
    (h1 : u + δ ≤ 1) (hU : 0 ≤ U) (hΔ : 0 ≤ Δ) (hUΔ : U + Δ ≤ 1) (hpre : Δ * u ≤ U * δ)
    (hsuf : (1 - U - Δ) * δ ≤ Δ * (1 - u - δ)) (ha : a * δ ≤ U * δ + Δ * (b - u))
    (hcase : a ≤ 1 - Δ ∨ δ ≤ b) :
    8 * (a * (1 - b)) ≤ 1 + 7 * max (U * (1 - u)) ((U + Δ) * (1 - u - δ)) := by
  have hb1 : 0 ≤ 1 - b := by linarith
  have hG1 : 0 ≤ U * (1 - u) := mul_nonneg hU (by linarith)
  have hc0 : U * (1 - u) ≤ max (U * (1 - u)) ((U + Δ) * (1 - u - δ)) := le_max_left _ _
  rcases le_or_gt a 0 with ha0 | ha0
  · nlinarith [mul_nonpos_of_nonpos_of_nonneg ha0 hb1]
  rcases hΔ.eq_or_lt with hΔ0 | hΔ0
  · -- degenerate: the critical box and all later boxes have probability `0`
    subst hΔ0
    have hU1 : U = 1 := by nlinarith
    subst hU1
    have ha1 : a ≤ 1 := by nlinarith
    have hx : a * (1 - b) ≤ 1 * (1 - u) := mul_le_mul ha1 (by linarith) hb1 (by norm_num)
    have hc1 : max (1 * (1 - u)) ((1 + 0) * (1 - u - δ)) ≤ 1 := max_le (by nlinarith) (by nlinarith)
    nlinarith
  set r := Δ / δ with hr_def
  have hr : 0 < r := div_pos hΔ0 hδ
  have hrδ : r * δ = Δ := by rw [hr_def]; field_simp
  set V := U - r * u with hV_def
  have hV : 0 ≤ V := by
    have : r * u * δ ≤ U * δ := by rw [mul_right_comm, hrδ]; linarith
    have := le_of_mul_le_mul_right this hδ
    linarith
  have hk1 : 1 ≤ r + V := by
    have h' : (1 - U - Δ) * δ ≤ r * (1 - u - δ) * δ := by
      rw [mul_right_comm, hrδ]; linarith
    have := le_of_mul_le_mul_right h' hδ
    nlinarith
  have hab : a ≤ r * b + V := by
    have h' : a * δ ≤ (r * b + V) * δ := by
      rw [hV_def]; nlinarith
    exact le_of_mul_le_mul_right h' hδ
  have hφ1 : phi r V u = U * (1 - u) := by simp only [phi, hV_def]; ring
  have hφ2 : phi r V (u + δ) = (U + Δ) * (1 - u - δ) := by
    simp only [phi, hV_def]; rw [← hrδ]; ring
  rw [← hφ1, ← hφ2]
  rcases hcase with hc | hc
  · by_cases hP : V + r * (u + δ + b - u) ≤ 1
    · have := core1 r V u b (u + δ) hr hV hk1 hu hub hbu h1 hP
      have : a * (1 - b) ≤ phi r V b := mul_le_mul_of_nonneg_right hab hb1
      linarith
    · -- shift the first round down to the cost `b'` where `ℓ b' = 1 - Δ`
      push Not at hP
      set b' := u + (1 - U - Δ) / r with hb'_def
      have hE : 0 ≤ 1 - U - Δ := by linarith
      have hub' : u ≤ b' := by have := div_nonneg hE hr.le; linarith
      have hrb' : r * (b' - u) = 1 - U - Δ := by rw [hb'_def]; field_simp; ring
      have hb'b : b' ≤ b := by
        by_contra hcon
        push Not at hcon
        have : r * (b - u) < r * (b' - u) := mul_lt_mul_of_pos_left (by linarith) hr
        nlinarith
      have hP' : V + r * (u + δ + b' - u) ≤ 1 := by
        rw [hV_def]; nlinarith
      have := core1 r V u b' (u + δ) hr hV hk1 hu hub' (by linarith) h1 hP'
      have hl : r * b' + V = 1 - Δ := by rw [hV_def]; nlinarith
      have : a * (1 - b) ≤ phi r V b' := by
        simp only [phi]; rw [hl]
        exact mul_le_mul hc (by linarith) hb1 (by linarith)
      linarith
  · have := core2 r V u b (u + δ) hr hV hu hub hbu h1 (by linarith) (by rw [← hrδ] at hUΔ; nlinarith)
    have : a * (1 - b) ≤ phi r V b := mul_le_mul_of_nonneg_right hab hb1
    linarith

/-- Homogeneous version of `key_real`: total probability `P > 0` and total cost `W > 0`. -/
lemma key_hom (P W u U δ Δ a b : ℝ) (hP : 0 < P) (hW : 0 < W) (hu : 0 ≤ u) (hδ : 0 < δ)
    (hub : u ≤ b) (hbu : b ≤ u + δ) (h1 : u + δ ≤ W) (hU : 0 ≤ U) (hΔ : 0 ≤ Δ) (hUΔ : U + Δ ≤ P)
    (hpre : Δ * u ≤ U * δ) (hsuf : (P - U - Δ) * δ ≤ Δ * (W - u - δ))
    (ha : a * δ ≤ U * δ + Δ * (b - u)) (hcase : a ≤ P - Δ ∨ δ ≤ b) :
    8 * (a * (W - b)) ≤ P * W + 7 * max (U * (W - u)) ((U + Δ) * (W - u - δ)) := by
  have hPW : 0 < P * W := mul_pos hP hW
  have key := key_real (u / W) (U / P) (δ / W) (Δ / P) (a / P) (b / W) (div_nonneg hu hW.le)
    (div_pos hδ hW) (div_le_div_of_nonneg_right hub hW.le)
    (by rw [← add_div]; exact div_le_div_of_nonneg_right hbu hW.le)
    (by rw [← add_div, div_le_one hW]; exact h1) (div_nonneg hU hP.le) (div_nonneg hΔ hP.le)
    (by rw [← add_div, div_le_one hP]; exact hUΔ)
    (by rw [div_mul_div_comm, div_mul_div_comm]
        exact div_le_div_of_nonneg_right hpre hPW.le)
    (by
      have e1 : (1 - U / P - Δ / P) * (δ / W) = (P - U - Δ) * δ / (P * W) := by
        field_simp
      have e2 : Δ / P * (1 - u / W - δ / W) = Δ * (W - u - δ) / (P * W) := by
        field_simp
      rw [e1, e2]; exact div_le_div_of_nonneg_right hsuf hPW.le)
    (by
      have e1 : a / P * (δ / W) = a * δ / (P * W) := by field_simp
      have e2 : U / P * (δ / W) + Δ / P * (b / W - u / W) = (U * δ + Δ * (b - u)) / (P * W) := by
        field_simp
      rw [e1, e2]; exact div_le_div_of_nonneg_right ha hPW.le)
    (by
      rcases hcase with h | h
      · left; rw [show 1 - Δ / P = (P - Δ) / P by field_simp]
        exact div_le_div_of_nonneg_right h hP.le
      · right; exact div_le_div_of_nonneg_right h hW.le)
  have e1 : a / P * (1 - b / W) = a * (W - b) / (P * W) := by field_simp
  have e2 : U / P * (1 - u / W) = U * (W - u) / (P * W) := by field_simp
  have e3 : (U / P + Δ / P) * (1 - u / W - δ / W) = (U + Δ) * (W - u - δ) / (P * W) := by
    field_simp
  rw [e1, e2, e3, max_div_div_right hPW.le] at key
  have h := mul_le_mul_of_nonneg_left key hPW.le
  have h8 : P * W * (8 * (a * (W - b) / (P * W))) = 8 * (a * (W - b)) := by
    field_simp
  have h7 : P * W * (1 + 7 * (max (U * (W - u)) ((U + Δ) * (W - u - δ)) / (P * W))) =
      P * W + 7 * max (U * (W - u)) ((U + Δ) * (W - u - δ)) := by
    field_simp
  linarith

end Podc.MobileDataSearch
