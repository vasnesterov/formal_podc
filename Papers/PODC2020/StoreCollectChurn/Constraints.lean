import Mathlib

/-!
# The parameter constraints (A)–(D) of [AKSW20], Section 5

Attiya, Kumari, Somani, Welch, *Store-Collect in the Presence of Continuous Churn with Application
to Snapshots and Lattice Agreement* (PODC 2020; arXiv 2003.07787v3), p. 11.

Parameters: churn rate `α`, failure fraction `Δ`, join-quorum fraction `γ`, phase-quorum
fraction `β`, minimum system size `Nmin`. With `Z = (1 - α)^3 - Δ (1 + α)^3`:

* (A) `Nmin ≥ 1 / (Z + γ - (1 + α)^3)`
* (B) `γ ≤ Z / (1 + α)^3`
* (C) `β ≤ Z / (1 + α)^2`
* (D) `β > ((1 - Z)(1 + α)^5 + (1 + α)^6) / (((1 - α)^3 - Δ (1 + α)^2)((1 + α)^2 + 1))`

We state each constraint literally (`ConstraintA`, …, `ConstraintD`) and, for (A) and (D), in the
"cleared" form where the denominator is multiplied out (`ConstraintA'`, `ConstraintD'`).

Findings:
* (A) as printed is vacuous when its denominator `Z + γ - (1 + α)^3` is `≤ 0`, which (B)–(D) do not
  exclude (`literal_constraints_not_imply_ZNmin`). Its use in Lemma 5 needs the cleared form
  `Nmin · (Z + γ - (1 + α)^3) ≥ 1` (`ConstraintA'`), which gives `Z · Nmin ≥ 1`
  (`ConstraintA'.one_le_Z_mul`).
* (D) literal and cleared agree as soon as `β > 0` and (C) holds (`constraintD_iff`).
* The two example parameter sets of p. 11 satisfy the constraints (`example_alpha_zero`,
  `example_alpha_004`); the first one has `α = 0`, excluded by the model (`α > 0`). For small
  `α > 0` and `Δ = 0.21` the values `γ = β = 0.79` violate (B) and (C); `γ = β = 0.78` works for
  `α = 1/1000` (`example_alpha_small`).
* (C) ∧ (D) force `α < 1/20` (hence the hypothesis `α < 0.206` of Lemma 2) and `Δ < 0.22`
  (hence the claim "`Δ < 1/3`" of Section 7).
-/

namespace Podc.StoreCollectChurn

/-- The survival fraction `Z = (1 - α)^3 - Δ · (1 + α)^3` of [AKSW20] (p. 10–11): the fraction of
nodes that survive an interval of length `3D`. -/
noncomputable def Z (α Δ : ℝ) : ℝ := (1 - α) ^ 3 - Δ * (1 + α) ^ 3

/-- Constraint (A) of [AKSW20] as printed: `Nmin ≥ 1 / (Z + γ - (1 + α)^3)`. -/
def ConstraintA (α Δ γ : ℝ) (Nmin : ℕ) : Prop := 1 / (Z α Δ + γ - (1 + α) ^ 3) ≤ Nmin

/-- Constraint (A) of [AKSW20] with the denominator cleared (the form used in Lemma 5):
`Nmin · (Z + γ - (1 + α)^3) ≥ 1`. -/
def ConstraintA' (α Δ γ : ℝ) (Nmin : ℕ) : Prop := 1 ≤ Nmin * (Z α Δ + γ - (1 + α) ^ 3)

/-- Constraint (B) of [AKSW20]: `γ ≤ Z / (1 + α)^3`. -/
def ConstraintB (α Δ γ : ℝ) : Prop := γ ≤ Z α Δ / (1 + α) ^ 3

/-- Constraint (C) of [AKSW20]: `β ≤ Z / (1 + α)^2`. -/
def ConstraintC (α Δ β : ℝ) : Prop := β ≤ Z α Δ / (1 + α) ^ 2

/-- Constraint (D) of [AKSW20] as printed:
`β > ((1 - Z)(1 + α)^5 + (1 + α)^6) / (((1 - α)^3 - Δ (1 + α)^2)((1 + α)^2 + 1))`. -/
def ConstraintD (α Δ β : ℝ) : Prop :=
  ((1 - Z α Δ) * (1 + α) ^ 5 + (1 + α) ^ 6) /
    (((1 - α) ^ 3 - Δ * (1 + α) ^ 2) * ((1 + α) ^ 2 + 1)) < β

/-- Constraint (D) of [AKSW20] with the denominator cleared. -/
def ConstraintD' (α Δ β : ℝ) : Prop :=
  (1 - Z α Δ) * (1 + α) ^ 5 + (1 + α) ^ 6 <
    β * (((1 - α) ^ 3 - Δ * (1 + α) ^ 2) * ((1 + α) ^ 2 + 1))

/-! ### Basic consequences -/

/-- (C) with `β > 0` gives `Z > 0`. -/
theorem Z_pos_of_C {α Δ β : ℝ} (hβ : 0 < β) (hC : ConstraintC α Δ β) : 0 < Z α Δ := by
  unfold ConstraintC at hC
  by_contra h
  push Not at h
  have : Z α Δ / (1 + α) ^ 2 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (by positivity)
  linarith

/-- (B) with `γ > 0` gives `Z > 0`. -/
theorem Z_pos_of_B {α Δ γ : ℝ} (hα : 0 ≤ α) (hγ : 0 < γ) (hB : ConstraintB α Δ γ) : 0 < Z α Δ := by
  unfold ConstraintB at hB
  by_contra h
  push Not at h
  have : Z α Δ / (1 + α) ^ 3 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h (by positivity)
  linarith

/-- Theorem 3's use of (B): `Z ≥ γ (1 + α)^3`. -/
theorem constraintB_iff {α Δ γ : ℝ} (hα : 0 ≤ α) :
    ConstraintB α Δ γ ↔ γ * (1 + α) ^ 3 ≤ Z α Δ := by
  unfold ConstraintB
  rw [le_div_iff₀ (by positivity)]

/-- Theorem 4's use of (C): `Z / (1 + α)^2 ≥ β`, i.e. `Z ≥ β (1 + α)^2`. -/
theorem constraintC_iff {α Δ β : ℝ} (hα : 0 ≤ α) :
    ConstraintC α Δ β ↔ β * (1 + α) ^ 2 ≤ Z α Δ := by
  unfold ConstraintC
  rw [le_div_iff₀ (by positivity)]

/-- Under (C), `β > 0`, `Δ ≥ 0`, `α ≥ 0`, the denominator `(1 - α)^3 - Δ (1 + α)^2` of (D) is
positive. -/
theorem X_pos {α Δ β : ℝ} (hα : 0 ≤ α) (hΔ : 0 ≤ Δ) (hβ : 0 < β) (hC : ConstraintC α Δ β) :
    0 < (1 - α) ^ 3 - Δ * (1 + α) ^ 2 := by
  have hZ := Z_pos_of_C hβ hC
  unfold Z at hZ
  have : Δ * (1 + α) ^ 2 ≤ Δ * (1 + α) ^ 3 := by
    apply mul_le_mul_of_nonneg_left _ hΔ
    have h1 : (1 : ℝ) ≤ 1 + α := by linarith
    calc (1 + α) ^ 2 = (1 + α) ^ 2 * 1 := by ring
      _ ≤ (1 + α) ^ 2 * (1 + α) := by gcongr
      _ = (1 + α) ^ 3 := by ring
  linarith

/-- Under (C) and `β > 0` (and `α, Δ ≥ 0`), the printed (D) and the cleared (D) agree. -/
theorem constraintD_iff {α Δ β : ℝ} (hα : 0 ≤ α) (hΔ : 0 ≤ Δ) (hβ : 0 < β)
    (hC : ConstraintC α Δ β) : ConstraintD α Δ β ↔ ConstraintD' α Δ β := by
  unfold ConstraintD ConstraintD'
  have hX := X_pos hα hΔ hβ hC
  rw [div_lt_iff₀ (by positivity)]

/-- The cleared (A) together with (B), `γ > 0`, `α ≥ 0`, `Δ ≥ 0` gives `Z · Nmin ≥ 1`, the fact
used for Corollary 1. -/
theorem ConstraintA'.one_le_Z_mul {α Δ γ : ℝ} {Nmin : ℕ} (hα : 0 ≤ α) (hΔ : 0 ≤ Δ) (hγ : 0 < γ)
    (hA : ConstraintA' α Δ γ Nmin) (hB : ConstraintB α Δ γ) : 1 ≤ Z α Δ * Nmin := by
  unfold ConstraintA' at hA
  rw [constraintB_iff hα] at hB
  have hu : (1 : ℝ) ≤ (1 + α) ^ 3 := one_le_pow₀ (by linarith)
  -- `Z ≤ 1`
  have hZ1 : Z α Δ ≤ 1 := by
    unfold Z
    have : (1 - α) ^ 3 ≤ 1 := by
      rcases le_or_gt α 1 with h | h
      · exact pow_le_one₀ (by linarith) (by linarith)
      · have : (1 - α) ^ 3 < 0 := Odd.pow_neg (by decide) (by linarith)
        linarith
    nlinarith [pow_pos (show (0 : ℝ) < 1 + α by linarith) 3]
  -- hence `γ ≤ γ (1+α)^3 ≤ Z ≤ 1 ≤ (1+α)^3`
  have hγu : γ ≤ (1 + α) ^ 3 := by nlinarith
  have hN : (0 : ℝ) ≤ Nmin := Nat.cast_nonneg _
  nlinarith

/-! ### Lemma 10, Theorems 3 and 4: the arithmetic uses of the constraints -/

/-- Arithmetic core of Lemma 10, Case II, of [AKSW20]: with `X = (1 - α)^3 - Δ (1 + α)^2`,
(D) gives `β X (1 + α)⁻¹ + β X (1 + α)⁻³ - (1 - Z)(1 + α)^2 > (1 + α)^3`. -/
theorem lemma10_core {α Δ β : ℝ} (hα : 0 ≤ α) (hD : ConstraintD' α Δ β) :
    (1 + α) ^ 3 < β * ((1 - α) ^ 3 - Δ * (1 + α) ^ 2) * ((1 + α) ^ 3)⁻¹ * (1 + α) ^ 2
      + β * ((1 - α) ^ 3 - Δ * (1 + α) ^ 2) * ((1 + α) ^ 3)⁻¹
      - (1 - Z α Δ) * (1 + α) ^ 2 := by
  unfold ConstraintD' at hD
  have hu : 0 < (1 + α) ^ 3 := by positivity
  set X := (1 - α) ^ 3 - Δ * (1 + α) ^ 2
  have key : β * X * ((1 + α) ^ 3)⁻¹ * (1 + α) ^ 2 + β * X * ((1 + α) ^ 3)⁻¹
      - (1 - Z α Δ) * (1 + α) ^ 2 - (1 + α) ^ 3
      = (β * (X * ((1 + α) ^ 2 + 1)) - ((1 - Z α Δ) * (1 + α) ^ 5 + (1 + α) ^ 6))
        * ((1 + α) ^ 3)⁻¹ := by
    field_simp
    ring
  have : 0 < (β * (X * ((1 + α) ^ 2 + 1)) - ((1 - Z α Δ) * (1 + α) ^ 5 + (1 + α) ^ 6))
        * ((1 + α) ^ 3)⁻¹ := mul_pos (by linarith) (inv_pos.mpr hu)
  linarith

/-- The same statement with negative powers, as printed in Lemma 10:
`β X (1 + α)⁻¹ + β X (1 + α)⁻³ - (1 - Z)(1 + α)^2 > (1 + α)^3`. -/
theorem lemma10_core' {α Δ β : ℝ} (hα : 0 ≤ α) (hD : ConstraintD' α Δ β) :
    (1 + α) ^ 3 < β * ((1 - α) ^ 3 - Δ * (1 + α) ^ 2) * (1 + α) ^ (-1 : ℤ)
      + β * ((1 - α) ^ 3 - Δ * (1 + α) ^ 2) * (1 + α) ^ (-3 : ℤ)
      - (1 - Z α Δ) * (1 + α) ^ 2 := by
  have h := lemma10_core hα hD
  have hu : (1 + α) ≠ 0 := by positivity
  have e1 : (1 + α) ^ (-1 : ℤ) = ((1 + α) ^ 3)⁻¹ * (1 + α) ^ 2 := by
    rw [zpow_neg_one]; field_simp
  have e3 : (1 + α) ^ (-3 : ℤ) = ((1 + α) ^ 3)⁻¹ := by
    rw [zpow_neg]; norm_cast
  rw [e1, e3]
  linarith [h, show β * ((1 - α) ^ 3 - Δ * (1 + α) ^ 2) * (((1 + α) ^ 3)⁻¹ * (1 + α) ^ 2)
    = β * ((1 - α) ^ 3 - Δ * (1 + α) ^ 2) * ((1 + α) ^ 3)⁻¹ * (1 + α) ^ 2 by ring]

/-! ### What (C) ∧ (D) force -/

/-- (C) ∧ (D) (cleared, with `β > 0`, `Δ ≥ 0`, `α ≥ 0`) force `α < 1/20`. -/
theorem alpha_lt_of_CD {α Δ β : ℝ} (hα : 0 ≤ α) (hΔ : 0 ≤ Δ) (hβ : 0 < β)
    (hC : ConstraintC α Δ β) (hD : ConstraintD' α Δ β) : α < 1 / 20 := by
  have hZ := Z_pos_of_C hβ hC
  have hX := X_pos hα hΔ hβ hC
  rw [constraintC_iff hα] at hC
  unfold ConstraintD' at hD
  set u := 1 + α with hu
  set v := 1 - α with hv
  have hu1 : 1 ≤ u := by linarith
  have hu0 : 0 < u := by linarith
  have hZv : Z α Δ ≤ v ^ 3 := by unfold Z; nlinarith [pow_pos hu0 3]
  have hXv : (1 - α) ^ 3 - Δ * (1 + α) ^ 2 ≤ v ^ 3 := by nlinarith [pow_pos hu0 2]
  set X := (1 - α) ^ 3 - Δ * (1 + α) ^ 2
  -- `α < 1`, since `v ^ 3 ≥ Z > 0`
  have hv0 : 0 < v := by
    by_contra h
    push Not at h
    have : v ^ 3 ≤ 0 := by
      have := pow_le_pow_left₀ (le_refl 0) (show 0 ≤ -v by linarith) 3
      nlinarith [this]
    linarith
  -- the key polynomial inequality
  have key : u ^ 2 * ((1 - v ^ 3) * u ^ 5 + u ^ 6) < v ^ 6 * (u ^ 2 + 1) := by
    have h1 : u ^ 2 * ((1 - Z α Δ) * u ^ 5 + u ^ 6) < u ^ 2 * (β * (X * (u ^ 2 + 1))) :=
      mul_lt_mul_of_pos_left hD (by positivity)
    have h2 : u ^ 2 * (β * (X * (u ^ 2 + 1))) ≤ v ^ 3 * v ^ 3 * (u ^ 2 + 1) := by
      have e : u ^ 2 * (β * (X * (u ^ 2 + 1))) = (β * u ^ 2) * X * (u ^ 2 + 1) := by ring
      rw [e]
      have h3 : (β * u ^ 2) * X ≤ v ^ 3 * v ^ 3 := by
        apply mul_le_mul (hC.trans hZv) hXv hX.le (by positivity)
      exact mul_le_mul_of_nonneg_right h3 (by positivity)
    have h4 : u ^ 2 * ((1 - v ^ 3) * u ^ 5 + u ^ 6) ≤ u ^ 2 * ((1 - Z α Δ) * u ^ 5 + u ^ 6) := by
      have : (1 - v ^ 3) * u ^ 5 ≤ (1 - Z α Δ) * u ^ 5 :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      nlinarith [pow_pos hu0 2]
    nlinarith
  by_contra hcon
  push Not at hcon
  have hv1 : v ≤ 19 / 20 := by linarith
  have hu2 : 21 / 20 ≤ u := by linarith
  have hv4 : v ^ 4 ≤ (19 / 20) ^ 4 := pow_le_pow_left₀ hv0.le hv1 4
  have hv6 : v ^ 6 ≤ (19 / 20) ^ 6 := pow_le_pow_left₀ hv0.le hv1 6
  have hv3 : v ^ 3 ≤ (19 / 20) ^ 3 := pow_le_pow_left₀ hv0.le hv1 3
  have hu8 : (21 / 20) ^ 8 ≤ u ^ 8 := pow_le_pow_left₀ (by norm_num) hu2 8
  have hu7 : (21 / 20) ^ 7 ≤ u ^ 7 := pow_le_pow_left₀ (by norm_num) hu2 7
  have huv : (u * v) ^ 2 ≤ 1 := by
    have : u * v = 1 - α ^ 2 := by rw [hu, hv]; ring
    rw [this]
    have : 0 ≤ 1 - α ^ 2 := by nlinarith
    nlinarith
  have hvu : v ^ 6 * u ^ 2 ≤ v ^ 4 := by
    have : v ^ 6 * u ^ 2 = v ^ 4 * (u * v) ^ 2 := by ring
    rw [this]
    nlinarith [pow_pos hv0 4]
  have hL : (21 / 20) ^ 8 + (1 - (19 / 20) ^ 3) * (21 / 20) ^ 7 ≤ u ^ 8 + (1 - v ^ 3) * u ^ 7 := by
    have : (1 - (19 / 20) ^ 3) * (21 / 20) ^ 7 ≤ (1 - v ^ 3) * u ^ 7 :=
      mul_le_mul (by linarith) hu7 (by norm_num) (by nlinarith [pow_pos hv0 3])
    linarith
  have e : u ^ 2 * ((1 - v ^ 3) * u ^ 5 + u ^ 6) = u ^ 8 + (1 - v ^ 3) * u ^ 7 := by ring
  rw [e] at key
  norm_num at hL hv4 hv6
  nlinarith

/-- (C) ∧ (D) imply the hypothesis `α < 0.206` of Lemma 2 of [AKSW20]. -/
theorem alpha_lt_0206_of_CD {α Δ β : ℝ} (hα : 0 ≤ α) (hΔ : 0 ≤ Δ) (hβ : 0 < β)
    (hC : ConstraintC α Δ β) (hD : ConstraintD' α Δ β) : α < 0.206 := by
  have := alpha_lt_of_CD hα hΔ hβ hC hD
  norm_num at this ⊢
  linarith

/-- (C) ∧ (D) (cleared, with `β > 0`, `Δ ≥ 0`, `α ≥ 0`) force `Δ < 0.22`; the true bound at
`α = 0` is `(5 - √17)/4 ≈ 0.2192`. -/
theorem Delta_lt_of_CD {α Δ β : ℝ} (hα : 0 ≤ α) (hΔ : 0 ≤ Δ) (hβ : 0 < β)
    (hC : ConstraintC α Δ β) (hD : ConstraintD' α Δ β) : Δ < 0.22 := by
  have hZ := Z_pos_of_C hβ hC
  have hX := X_pos hα hΔ hβ hC
  rw [constraintC_iff hα] at hC
  unfold ConstraintD' at hD
  set u := 1 + α with hu
  have hu1 : 1 ≤ u := by linarith
  have hu2 : 1 ≤ u ^ 2 := one_le_pow₀ hu1
  have hu3 : 1 ≤ u ^ 3 := one_le_pow₀ hu1
  have hu5 : 1 ≤ u ^ 5 := one_le_pow₀ hu1
  have hu6 : 1 ≤ u ^ 6 := one_le_pow₀ hu1
  set X := (1 - α) ^ 3 - Δ * u ^ 2 with hXdef
  -- `α < 1`
  have hα1 : α < 1 := by
    by_contra h
    push Not at h
    have : (1 - α) ^ 3 ≤ 0 := by
      have := pow_le_pow_left₀ (le_refl 0) (show 0 ≤ -(1 - α) by linarith) 3
      nlinarith [this]
    unfold Z at hZ
    nlinarith
  have hv3 : (1 - α) ^ 3 ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
  have hZ1 : Z α Δ ≤ 1 - Δ := by unfold Z; nlinarith
  have hX1 : X ≤ 1 - Δ := by rw [hXdef]; nlinarith
  have hΔ1 : Δ < 1 := by linarith
  -- `β (u^2 + 1) ≤ 2 Z`
  have hβu : β * (u ^ 2 + 1) ≤ 2 * Z α Δ := by
    have : β ≤ β * u ^ 2 := by nlinarith
    linarith
  have h1 : β * (X * (u ^ 2 + 1)) ≤ 2 * (1 - Δ) * (1 - Δ) := by
    have e : β * (X * (u ^ 2 + 1)) = (β * (u ^ 2 + 1)) * X := by ring
    rw [e]
    apply mul_le_mul (by linarith) hX1 hX.le (by linarith)
  have h2 : 1 + Δ ≤ (1 - Z α Δ) * u ^ 5 + u ^ 6 := by
    have : 1 - Z α Δ ≤ (1 - Z α Δ) * u ^ 5 := by nlinarith
    linarith
  have hq : 1 + Δ < 2 * (1 - Δ) * (1 - Δ) := by linarith
  by_contra hcon
  push Not at hcon
  norm_num at hcon
  nlinarith

/-- Section 7 of [AKSW20]: the constraints force the failure fraction below one third. -/
theorem Delta_lt_third_of_CD {α Δ β : ℝ} (hα : 0 ≤ α) (hΔ : 0 ≤ Δ) (hβ : 0 < β)
    (hC : ConstraintC α Δ β) (hD : ConstraintD' α Δ β) : Δ < 1 / 3 := by
  have := Delta_lt_of_CD hα hΔ hβ hC hD
  norm_num at this ⊢
  linarith

/-! ### The example parameter values of p. 11 -/

/-- All four constraints (A), (A'), (B), (C), (D), (D') at once. -/
def AllConstraints (α Δ γ β : ℝ) (Nmin : ℕ) : Prop :=
  ConstraintA α Δ γ Nmin ∧ ConstraintA' α Δ γ Nmin ∧ ConstraintB α Δ γ ∧ ConstraintC α Δ β ∧
    ConstraintD α Δ β ∧ ConstraintD' α Δ β

/-- First example of [AKSW20], p. 11: `α = 0`, `Δ = 0.21`, `γ = β = 0.79`, any `Nmin ≥ 2`.
(Note that the model of Section 3 requires `α > 0`.) -/
theorem example_alpha_zero (Nmin : ℕ) (hN : 2 ≤ Nmin) :
    AllConstraints 0 0.21 0.79 0.79 Nmin := by
  have hN' : (2 : ℝ) ≤ Nmin := by exact_mod_cast hN
  unfold AllConstraints ConstraintA ConstraintA' ConstraintB ConstraintC ConstraintD ConstraintD' Z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

/-- Second example of [AKSW20], p. 11: `α = 0.04`, `Δ = 0.01`, `γ = 0.77`, `β = 0.80`, any
`Nmin ≥ 2`. -/
theorem example_alpha_004 (Nmin : ℕ) (hN : 2 ≤ Nmin) :
    AllConstraints 0.04 0.01 0.77 0.80 Nmin := by
  have hN' : (2 : ℝ) ≤ Nmin := by exact_mod_cast hN
  unfold AllConstraints ConstraintA ConstraintA' ConstraintB ConstraintC ConstraintD ConstraintD' Z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

/-- With `Δ = 0.21`, the value `γ = 0.79` of the first example violates (B) for every churn rate
`α > 0` (the example is tight at `α = 0`). -/
theorem not_constraintB_021_079 {α : ℝ} (hα : 0 < α) : ¬ ConstraintB α 0.21 0.79 := by
  rw [constraintB_iff hα.le]
  unfold Z
  nlinarith [pow_pos hα 2, pow_pos hα 3]

/-- With `Δ = 0.21`, the value `β = 0.79` of the first example violates (C) for every churn rate
`α > 0`. -/
theorem not_constraintC_021_079 {α : ℝ} (hα : 0 < α) : ¬ ConstraintC α 0.21 0.79 := by
  rw [constraintC_iff hα.le]
  unfold Z
  nlinarith [pow_pos hα 2, pow_pos hα 3]

/-- A positive churn rate near the first example: `α = 1/1000`, `Δ = 0.21`, `γ = β = 0.78`, any
`Nmin ≥ 2`. -/
theorem example_alpha_small (Nmin : ℕ) (hN : 2 ≤ Nmin) :
    AllConstraints (1 / 1000) 0.21 0.78 0.78 Nmin := by
  have hN' : (2 : ℝ) ≤ Nmin := by exact_mod_cast hN
  unfold AllConstraints ConstraintA ConstraintA' ConstraintB ConstraintC ConstraintD ConstraintD' Z
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> norm_num <;> linarith

/-- Constraint (A) as printed is too weak: `α = 0.04`, `Δ = 0.01`, `γ = 0.1`, `β = 0.8`,
`Nmin = 1` satisfy the printed (A) (its denominator is negative) and (B), (C), (D), (D'), but
not the cleared (A'), and `Z · Nmin < 1`. -/
theorem literal_constraints_not_imply_ZNmin :
    ConstraintA 0.04 0.01 0.1 1 ∧ ConstraintB 0.04 0.01 0.1 ∧ ConstraintC 0.04 0.01 0.8 ∧
      ConstraintD 0.04 0.01 0.8 ∧ ConstraintD' 0.04 0.01 0.8 ∧
      ¬ ConstraintA' 0.04 0.01 0.1 1 ∧ Z 0.04 0.01 * (1 : ℕ) < 1 := by
  unfold ConstraintA ConstraintA' ConstraintB ConstraintC ConstraintD ConstraintD' Z
  norm_num

end Podc.StoreCollectChurn
