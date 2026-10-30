import Papers.PODC2023.PPDoubleExpThresholds.Specs

/-!
# Register arithmetic: moves, swaps, the `Large` transformation, and the configuration types
-/

namespace Podc.PPDoubleExpThresholds

variable {R : Type*} [DecidableEq R]

/-- `C` after moving `m` units from `x` to `y`. -/
def shift (C : R → ℕ) (x y : R) (m : ℕ) : R → ℕ :=
  fun z => if z = x then C x - m else if z = y then C y + m else C z

theorem mv_eq_shift (C : R → ℕ) {x y : R} (hxy : x ≠ y) : mv C x y = shift C x y 1 := by
  funext z; unfold mv shift
  by_cases hx : z = x
  · subst hx; simp [hxy]
  · by_cases hy : z = y <;> simp [hx, hy, Ne.symm hxy]

theorem shift_zero (C : R → ℕ) (x y : R) : shift C x y 0 = C := by
  funext z; unfold shift; split_ifs <;> simp_all

theorem mv_shift (C : R → ℕ) {x y : R} (hxy : x ≠ y) (m : ℕ) (hm : m < C x) :
    mv (shift C x y m) x y = shift C x y (m + 1) := by
  funext z; unfold mv shift
  by_cases hx : z = x
  · subst hx; simp [hxy]; omega
  · by_cases hy : z = y
    · subst hy; simp [hx, Ne.symm hxy]; omega
    · simp [hx, hy]

theorem mv_shift_back (C : R → ℕ) {x y : R} (hxy : x ≠ y) (m : ℕ) (hm : m + 1 ≤ C x) :
    mv (shift C x y (m + 1)) y x = shift C x y m := by
  funext z; unfold mv shift
  by_cases hx : z = x
  · subst hx; simp [hxy]; omega
  · by_cases hy : z = y <;> simp [hx, hy, Ne.symm hxy]

theorem shift_apply_x (C : R → ℕ) (x y : R) (m : ℕ) : shift C x y m x = C x - m := by simp [shift]

theorem shift_apply_y (C : R → ℕ) {x y : R} (hxy : x ≠ y) (m : ℕ) : shift C x y m y = C y + m := by
  simp [shift, Ne.symm hxy]

theorem shift_apply_other (C : R → ℕ) {x y z : R} (hx : z ≠ x) (hy : z ≠ y) (m : ℕ) :
    shift C x y m z = C z := by simp [shift, hx, hy]

theorem swp_shift_eq_lg {n : ℕ} (C : Reg n → ℕ) {x y : Reg n} (hxy : x ≠ y) (m : ℕ) :
    swp (shift C x y m) x y = lg C x y m := by
  funext z; unfold swp shift lg
  by_cases hx : z = x
  · subst hx; simp [Equiv.swap_apply_left, Function.update_apply, hxy, Ne.symm hxy]
  · by_cases hy : z = y
    · subst hy; simp [Equiv.swap_apply_right, Function.update_apply, hxy]
    · simp [Equiv.swap_apply_of_ne_of_ne hx hy, Function.update_apply, hx, hy]

theorem swp_mv_eq_lg {n : ℕ} (C : Reg n → ℕ) {x y : Reg n} (hxy : x ≠ y) :
    swp (mv C x y) x y = lg C x y 1 := by
  rw [mv_eq_shift C hxy, swp_shift_eq_lg C hxy]

theorem swp_swp (C : R → ℕ) (x y : R) : swp (swp C x y) x y = C := by
  funext z; simp [swp, Equiv.swap_apply_self]

theorem lg_apply_x {n : ℕ} (C : Reg n → ℕ) {x y : Reg n} (hxy : x ≠ y) (m : ℕ) :
    lg C x y m x = C y + m := by simp [lg, Function.update_apply, hxy]

theorem lg_apply_y {n : ℕ} (C : Reg n → ℕ) (x y : Reg n) (m : ℕ) : lg C x y m y = C x - m := by
  simp [lg]

theorem lg_apply_other {n : ℕ} (C : Reg n → ℕ) {x y z : Reg n} (hx : z ≠ x) (hy : z ≠ y)
    (m : ℕ) : lg C x y m z = C z := by simp [lg, Function.update_apply, hx, hy]

theorem lg_lg {n : ℕ} (C : Reg n → ℕ) {x y : Reg n} (hxy : x ≠ y) {m : ℕ} (hm : m ≤ C x) :
    lg (lg C x y m) x y m = C := by
  funext z
  simp only [lg, Function.update_apply]
  split_ifs with h1 h2 h3 <;> subst_vars <;> simp_all <;> omega

end Podc.PPDoubleExpThresholds
