import Papers.PODC2013.IncentiveTrees.CDRM

/-!
# Non-vacuity of Theorem 5: the first CDRM example of Algorithm 5

`R(x, y) = (Φ - θ / (1 + x + y)) · x` with `θ > 0`, `θ + φ < Φ ≤ 1`, `φ ≥ 0` is successfully
contribution-deterministic, so `theorem_5` applies to it.
-/

namespace Podc.IncentiveTrees

open Set

/-- Algorithm 5 (i): `R(p) = (Φ - θ / (1 + x_p + y_p)) x_p`. -/
noncomputable def cdrmExample (Φ θ : ℝ) (x y : ℝ) : ℝ := (Φ - θ / (1 + x + y)) * x

theorem cdrmExample_hasDerivAt_x (Φ θ x y : ℝ) (h : 0 < 1 + x + y) :
    HasDerivAt (fun x => cdrmExample Φ θ x y)
      (Φ - θ * (1 + y) / (1 + x + y) ^ 2) x := by
  have hg : HasDerivAt (fun x => 1 + x + y) 1 x :=
    ((hasDerivAt_id x).const_add 1).add_const y
  have h1 : HasDerivAt (fun x => Φ - θ / (1 + x + y)) (-(-(θ * 1) / (1 + x + y) ^ 2)) x :=
    ((hg.inv h.ne').const_mul θ).const_sub Φ |>.congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun z => by simp [div_eq_mul_inv]) |>.congr_deriv
      (by field_simp)
  have h2 := h1.mul (hasDerivAt_id x)
  have hf : (fun x => cdrmExample Φ θ x y) = fun x => (Φ - θ / (1 + x + y)) * id x := rfl
  rw [hf]
  convert h2 using 1
  simp only [id]
  field_simp
  ring

theorem cdrmExample_hasDerivAt_y (Φ θ x y : ℝ) (h : 0 < 1 + x + y) :
    HasDerivAt (cdrmExample Φ θ x) (θ * x / (1 + x + y) ^ 2) y := by
  have hg : HasDerivAt (fun y => 1 + x + y) 1 y := (hasDerivAt_id y).const_add (1 + x)
  have h1 := (((hg.inv h.ne').const_mul θ).const_sub Φ).mul_const x
  convert h1 using 1
  · ext z; simp [cdrmExample, div_eq_mul_inv]
  · field_simp

theorem cdrmExample_successfullyCD {φ Φ θ : ℝ} (hφ : 0 ≤ φ) (hθ : 0 < θ) (hθφ : θ + φ < Φ)
    (hΦ : Φ ≤ 1) : SuccessfullyCD (cdrmExample Φ θ) φ Φ where
  cont_x y hy := by
    intro x hx
    have : 0 < 1 + x + y := by have := mem_Ici.1 hx; linarith
    exact (cdrmExample_hasDerivAt_x Φ θ x y this).continuousAt.continuousWithinAt
  diff_x y hy x hx := (cdrmExample_hasDerivAt_x Φ θ x y (by linarith)).differentiableAt
  deriv_x_pos y hy x hx := by
    rw [(cdrmExample_hasDerivAt_x Φ θ x y (by linarith)).deriv]
    have hpos : 0 < 1 + x + y := by linarith
    have : θ * (1 + y) / (1 + x + y) ^ 2 ≤ θ := by
      rw [div_le_iff₀ (by positivity)]
      have : 1 + y ≤ (1 + x + y) ^ 2 := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this hθ.le]
    linarith
  deriv_x_lt_one y hy x hx := by
    rw [(cdrmExample_hasDerivAt_x Φ θ x y (by linarith)).deriv]
    have : 0 < θ * (1 + y) / (1 + x + y) ^ 2 := by
      have : 0 < 1 + y := by linarith
      positivity
    linarith
  diff_y x hx y hy := (cdrmExample_hasDerivAt_y Φ θ x y (by linarith)).differentiableAt
  deriv_y_pos x hx y hy := by
    rw [(cdrmExample_hasDerivAt_y Φ θ x y (by linarith)).deriv]
    have : 0 < 1 + x + y := by linarith
    positivity
  lower x hx y hy := by
    simp only [cdrmExample]
    have : θ / (1 + x + y) < θ := by
      rw [div_lt_iff₀ (by linarith)]; nlinarith
    nlinarith
  upper x hx y hy := by
    simp only [cdrmExample]
    have : 0 < θ / (1 + x + y) := by apply div_pos hθ; linarith
    nlinarith
  split x' hx' x'' hx'' y hy := by
    simp only [cdrmExample]
    have h1 : 0 < 1 + x' + (x'' + y) := by linarith
    have h2 : 0 < 1 + x'' + y := by linarith
    have h3 : 0 < 1 + (x' + x'') + y := by linarith
    have key : θ * x'' / (1 + (x' + x'') + y) ≤ θ * x'' / (1 + x'' + y) := by
      apply div_le_div_of_nonneg_left (by positivity) h2 (by linarith)
    have e1 : (Φ - θ / (1 + x' + (x'' + y))) * x' = Φ * x' - θ * x' / (1 + (x' + x'') + y) := by
      field_simp; ring
    have e2 : (Φ - θ / (1 + x'' + y)) * x'' = Φ * x'' - θ * x'' / (1 + x'' + y) := by
      field_simp
    have e3 : (Φ - θ / (1 + (x' + x'') + y)) * (x' + x'') =
        Φ * (x' + x'') - θ * x' / (1 + (x' + x'') + y) - θ * x'' / (1 + (x' + x'') + y) := by
      field_simp; ring
    rw [e1, e2, e3]
    linarith

/-- Non-vacuity of Theorem 5: the CDRM example satisfies all properties except URO and PO. -/
theorem theorem_5_example {φ Φ θ : ℝ} (hφ : 0 ≤ φ) (hθ : 0 < θ) (hθφ : θ + φ < Φ)
    (hΦ : Φ ≤ 1) :
    NonnegReward (cdrm (cdrmExample Φ θ)) ∧ Budget (cdrm (cdrmExample Φ θ)) Φ ∧
      CCI (cdrm (cdrmExample Φ θ)) ∧ CSI (cdrm (cdrmExample Φ θ)) ∧
      RPC (cdrm (cdrmExample Φ θ)) φ ∧ USA (cdrm (cdrmExample Φ θ)) ∧
      UGSA (cdrm (cdrmExample Φ θ)) ∧ ¬ URO (cdrm (cdrmExample Φ θ)) ∧
      ¬ PO (cdrm (cdrmExample Φ θ)) :=
  theorem_5 hφ hΦ (cdrmExample_successfullyCD hφ hθ hθφ hΦ)

end Podc.IncentiveTrees
