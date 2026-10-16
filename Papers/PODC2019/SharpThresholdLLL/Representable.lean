import Mathlib

/-!
# Representable triples (Section 3.2 of Brandt–Maus–Uitto, PODC 2019)

The set `S_rep` of *representable triples* (Definition 3.3) and the facts about it that the
variable-fixing lemma needs.

* `representable_iff`: a triple `(a, b, c) ≥ 0` is representable iff
  `a + b + c + √(abc) ≤ 4`. This is a cleaner, symmetric form of Lemma 3.5.
* `hval_le_of_tangent`: the *tangent-plane inequality*. For `m > 0`, the half-space below the
  tangent plane of the level surface of `hval` through `m` lies in the sublevel set of `m`.
  The proof is two weighted AM–GM inequalities (`two_sqrt_le`). It replaces the
  Hessian computation of Lemma 3.6.
* `exists_hval_le_four`: the averaging statement used in the proof of Lemma 3.2 (Lemma 3.9 in
  contrapositive form). If a weighted average of nonnegative triples is dominated by a
  representable triple, then one of the triples is representable.
* `srep_incurved` (Lemma 3.7), `srep_eq_f` (Lemma 3.5 with the parentheses of Lemma 3.6),
  `lemma_3_5_as_printed_false`, and `f_convexOn` (Lemma 3.6, derived from Lemma 3.7).
-/

open Real Finset

namespace SharpThresholdLLL

/-! ## The function `hval` -/

/-- `hval a b c = a + b + c + √(abc)`. Representable triples are exactly the nonnegative
triples with `hval ≤ 4` (`representable_iff`). -/
noncomputable def hval (a b c : ℝ) : ℝ := a + b + c + √(a * b * c)

lemma hval_mono {a b c a' b' c' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (haa : a ≤ a') (hbb : b ≤ b') (hcc : c ≤ c') : hval a b c ≤ hval a' b' c' := by
  unfold hval
  have : a * b * c ≤ a' * b' * c' := by
    apply mul_le_mul (mul_le_mul haa hbb hb (ha.trans haa)) hcc hc
    exact mul_nonneg (ha.trans haa) (hb.trans hbb)
  have := Real.sqrt_le_sqrt this
  linarith

/-! ## Weighted AM–GM -/

-- CSLib candidate
/-- Homogeneous AM–GM inequality behind the tangent-plane lemma: for weights `β` in the
standard simplex and `u ≥ 0`,
`2 √(u₁u₂u₃) ≤ (Σ (1-βᵢ) uᵢ) · √(Σ βᵢ uᵢ)`. -/
lemma two_sqrt_le {β₁ β₂ β₃ u₁ u₂ u₃ : ℝ} (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) (hβ₃ : 0 ≤ β₃)
    (hβ : β₁ + β₂ + β₃ = 1) (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hu₃ : 0 ≤ u₃) :
    2 * √(u₁ * u₂ * u₃) ≤
      ((1 - β₁) * u₁ + (1 - β₂) * u₂ + (1 - β₃) * u₃) * √(β₁ * u₁ + β₂ * u₂ + β₃ * u₃) := by
  -- first AM–GM, weights `(1-βᵢ)/2`
  have hA := Real.geom_mean_le_arith_mean3_weighted (w₁ := (1 - β₁) / 2) (w₂ := (1 - β₂) / 2)
    (w₃ := (1 - β₃) / 2) (by linarith) (by linarith) (by linarith) hu₁ hu₂ hu₃ (by linarith)
  -- second AM–GM, weights `βᵢ`
  have hB := Real.geom_mean_le_arith_mean3_weighted hβ₁ hβ₂ hβ₃ hu₁ hu₂ hu₃ hβ
  set A := u₁ ^ ((1 - β₁) / 2) * u₂ ^ ((1 - β₂) / 2) * u₃ ^ ((1 - β₃) / 2) with hAdef
  set G := u₁ ^ β₁ * u₂ ^ β₂ * u₃ ^ β₃ with hGdef
  have hA0 : 0 ≤ A := by positivity
  have hG0 : 0 ≤ G := by positivity
  -- `√u = u^((1-β)/2) * u^(β/2)` and `√(u^β) = u^(β/2)`
  have split : ∀ {u β : ℝ}, 0 ≤ u → √u = u ^ ((1 - β) / 2) * √(u ^ β) := by
    intro u β hu
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hu, ← Real.rpow_add' hu]
    · ring_nf
    · ring_nf; norm_num
  have hsq : √(u₁ * u₂ * u₃) = A * √G := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hu₁, split (β := β₁) hu₁,
      split (β := β₂) hu₂, split (β := β₃) hu₃, hGdef, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
    ring
  rw [hsq]
  have h1 : √G ≤ √(β₁ * u₁ + β₂ * u₂ + β₃ * u₃) := Real.sqrt_le_sqrt hB
  have h2 : 2 * A ≤ (1 - β₁) * u₁ + (1 - β₂) * u₂ + (1 - β₃) * u₃ := by linarith
  calc 2 * (A * √G) = (2 * A) * √G := by ring
    _ ≤ ((1 - β₁) * u₁ + (1 - β₂) * u₂ + (1 - β₃) * u₃) * √(β₁ * u₁ + β₂ * u₂ + β₃ * u₃) :=
        mul_le_mul h2 h1 (Real.sqrt_nonneg _) (by linarith)

/-! ## The tangent-plane inequality -/

/-- Normalised tangent-plane inequality. With `P = √(a₀b₀c₀)`, `λ = (a₀+P/2, b₀+P/2, c₀+P/2)`
and `u ≥ 0` with `λ·u ≤ λ·1`, we get `a₀u₁ + b₀u₂ + c₀u₃ + P√(u₁u₂u₃) ≤ a₀ + b₀ + c₀ + P`. -/
lemma tangent_core {a₀ b₀ c₀ u₁ u₂ u₃ : ℝ} (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) (hc₀ : 0 < c₀)
    (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hu₃ : 0 ≤ u₃)
    (hT : (a₀ + √(a₀ * b₀ * c₀) / 2) * u₁ + (b₀ + √(a₀ * b₀ * c₀) / 2) * u₂ +
        (c₀ + √(a₀ * b₀ * c₀) / 2) * u₃ ≤
      (a₀ + √(a₀ * b₀ * c₀) / 2) + (b₀ + √(a₀ * b₀ * c₀) / 2) + (c₀ + √(a₀ * b₀ * c₀) / 2)) :
    a₀ * u₁ + b₀ * u₂ + c₀ * u₃ + √(a₀ * b₀ * c₀) * √(u₁ * u₂ * u₃) ≤
      a₀ + b₀ + c₀ + √(a₀ * b₀ * c₀) := by
  set P := √(a₀ * b₀ * c₀) with hP
  have hP0 : 0 ≤ P := Real.sqrt_nonneg _
  set l₁ := a₀ + P / 2
  set l₂ := b₀ + P / 2
  set l₃ := c₀ + P / 2
  set L := l₁ + l₂ + l₃ with hL
  have hl₁ : 0 < l₁ := by positivity
  have hl₂ : 0 < l₂ := by positivity
  have hl₃ : 0 < l₃ := by positivity
  have hL0 : 0 < L := by positivity
  -- weights in the simplex
  have key := two_sqrt_le (β₁ := l₁ / L) (β₂ := l₂ / L) (β₃ := l₃ / L) (by positivity)
    (by positivity) (by positivity)
    (by rw [← add_div, ← add_div, ← hL, div_self hL0.ne']) hu₁ hu₂ hu₃
  set T := l₁ / L * u₁ + l₂ / L * u₂ + l₃ / L * u₃ with hTdef
  have hT0 : 0 ≤ T := by positivity
  have hLT : L * T = l₁ * u₁ + l₂ * u₂ + l₃ * u₃ := by
    rw [hTdef]; field_simp
  have hT1 : T ≤ 1 := by
    by_contra h
    push Not at h
    have : L * 1 < L * T := mul_lt_mul_of_pos_left h hL0
    linarith
  set U := u₁ + u₂ + u₃
  have hUT : (1 - l₁ / L) * u₁ + (1 - l₂ / L) * u₂ + (1 - l₃ / L) * u₃ = U - T := by
    rw [hTdef]; ring
  rw [hUT] at key
  -- `U ≥ T`
  have hUT' : T ≤ U := by
    have h1 : l₁ / L ≤ 1 := by rw [div_le_one hL0]; linarith
    have h2 : l₂ / L ≤ 1 := by rw [div_le_one hL0]; linarith
    have h3 : l₃ / L ≤ 1 := by rw [div_le_one hL0]; linarith
    rw [hTdef]
    nlinarith [mul_le_mul_of_nonneg_right h1 hu₁, mul_le_mul_of_nonneg_right h2 hu₂,
      mul_le_mul_of_nonneg_right h3 hu₃]
  set r := √T with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrr : r * r = T := Real.mul_self_sqrt hT0
  have hr1 : r ≤ 1 := by
    rw [hr]; calc √T ≤ √1 := Real.sqrt_le_sqrt hT1
      _ = 1 := Real.sqrt_one
  -- assemble
  have hlin : a₀ * u₁ + b₀ * u₂ + c₀ * u₃ = L * T - P / 2 * U := by rw [hLT]; ring
  have hS : 2 * √(u₁ * u₂ * u₃) ≤ (U - T) * r := key
  have hPS : P * √(u₁ * u₂ * u₃) ≤ P / 2 * ((U - T) * r) := by
    calc P * √(u₁ * u₂ * u₃) = P / 2 * (2 * √(u₁ * u₂ * u₃)) := by ring
      _ ≤ P / 2 * ((U - T) * r) := mul_le_mul_of_nonneg_left hS (by positivity)
  rw [hlin]
  have hl1' : P / 2 ≤ l₁ := le_add_of_nonneg_left ha₀.le
  have hLP : P / 2 ≤ L := by linarith
  -- `L*T - P/2*U + P/2*(U-T)*r ≤ L - P/2`
  have h1 : P / 2 * U * (1 - r) ≥ P / 2 * T * (1 - r) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact mul_le_mul_of_nonneg_left hUT' (by linarith)
  have h2 : (L - P / 2) * (1 - T) ≥ 0 := mul_nonneg (by linarith) (by linarith)
  nlinarith

-- CSLib candidate
/-- **Tangent-plane inequality.** Let `m = (a₀, b₀, c₀)` with positive entries, and
`w = (1 + P/(2a₀), 1 + P/(2b₀), 1 + P/(2c₀))` with `P = √(a₀b₀c₀)`, the gradient of `hval`
at `m`. Every `s ≥ 0` with `w·s ≤ w·m` satisfies `hval s ≤ hval m`. So every superlevel set
`{hval > t}` is convex in the nonnegative orthant: `hval` is quasi-concave there. -/
theorem hval_le_of_tangent {a₀ b₀ c₀ a b c : ℝ} (ha₀ : 0 < a₀) (hb₀ : 0 < b₀) (hc₀ : 0 < c₀)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hw : (1 + √(a₀ * b₀ * c₀) / (2 * a₀)) * a + (1 + √(a₀ * b₀ * c₀) / (2 * b₀)) * b +
        (1 + √(a₀ * b₀ * c₀) / (2 * c₀)) * c ≤
      (1 + √(a₀ * b₀ * c₀) / (2 * a₀)) * a₀ + (1 + √(a₀ * b₀ * c₀) / (2 * b₀)) * b₀ +
        (1 + √(a₀ * b₀ * c₀) / (2 * c₀)) * c₀) :
    hval a b c ≤ hval a₀ b₀ c₀ := by
  set P := √(a₀ * b₀ * c₀) with hP
  have core := tangent_core (u₁ := a / a₀) (u₂ := b / b₀) (u₃ := c / c₀) ha₀ hb₀ hc₀
    (by positivity) (by positivity) (by positivity) (by
      rw [← hP]
      have e1 : (a₀ + P / 2) * (a / a₀) = (1 + P / (2 * a₀)) * a := by field_simp
      have e2 : (b₀ + P / 2) * (b / b₀) = (1 + P / (2 * b₀)) * b := by field_simp
      have e3 : (c₀ + P / 2) * (c / c₀) = (1 + P / (2 * c₀)) * c := by field_simp
      have e4 : (1 + P / (2 * a₀)) * a₀ + (1 + P / (2 * b₀)) * b₀ + (1 + P / (2 * c₀)) * c₀ =
          (a₀ + P / 2) + (b₀ + P / 2) + (c₀ + P / 2) := by field_simp
      rw [e1, e2, e3, ← e4]; exact hw)
  rw [← hP] at core
  have e5 : a₀ * (a / a₀) = a := by field_simp
  have e6 : b₀ * (b / b₀) = b := by field_simp
  have e7 : c₀ * (c / c₀) = c := by field_simp
  have e8 : P * √(a / a₀ * (b / b₀) * (c / c₀)) = √(a * b * c) := by
    rw [hP, ← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  rw [e5, e6, e7, e8] at core
  unfold hval
  linarith

/-! ## Averaging: one of the outcomes is good -/

/-- **Averaging lemma** (the core of Lemmas 3.9 and 3.2). Let `w` be a probability distribution
on a finite set `Ω` with positive weights. Let `(A y, B y, C y) ≥ 0` be triples whose weighted
average is dominated by `(a, b, c)` with `hval a b c ≤ 4`. Then some `y ∈ Ω` has
`hval (A y) (B y) (C y) ≤ 4`. -/
theorem exists_hval_le_four {β : Type*} (Ω : Finset β) (w A B C : β → ℝ) {a b c : ℝ}
    (hw : ∀ y ∈ Ω, 0 < w y) (hsum : ∑ y ∈ Ω, w y = 1)
    (hA : ∀ y ∈ Ω, 0 ≤ A y) (hB : ∀ y ∈ Ω, 0 ≤ B y) (hC : ∀ y ∈ Ω, 0 ≤ C y)
    (ha : ∑ y ∈ Ω, w y * A y ≤ a) (hb : ∑ y ∈ Ω, w y * B y ≤ b)
    (hc : ∑ y ∈ Ω, w y * C y ≤ c) (habc : hval a b c ≤ 4) :
    ∃ y ∈ Ω, hval (A y) (B y) (C y) ≤ 4 := by
  have hne : Ω.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    simp [h] at hsum
  set mA := ∑ y ∈ Ω, w y * A y
  set mB := ∑ y ∈ Ω, w y * B y
  set mC := ∑ y ∈ Ω, w y * C y
  have hmA : 0 ≤ mA := Finset.sum_nonneg fun y hy => mul_nonneg (hw y hy).le (hA y hy)
  have hmB : 0 ≤ mB := Finset.sum_nonneg fun y hy => mul_nonneg (hw y hy).le (hB y hy)
  have hmC : 0 ≤ mC := Finset.sum_nonneg fun y hy => mul_nonneg (hw y hy).le (hC y hy)
  have hm4 : hval mA mB mC ≤ 4 := (hval_mono hmA hmB hmC ha hb hc).trans habc
  -- if a coordinate of the mean vanishes, it vanishes for every outcome
  have zero_of : ∀ F : β → ℝ, (∀ y ∈ Ω, 0 ≤ F y) → ∑ y ∈ Ω, w y * F y = 0 →
      ∀ y ∈ Ω, F y = 0 := by
    intro F hF h0 y hy
    have := (Finset.sum_eq_zero_iff_of_nonneg
      (fun y hy => mul_nonneg (hw y hy).le (hF y hy))).1 h0 y hy
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (hw y hy).ne'
    · exact h
  by_cases hpos : 0 < mA ∧ 0 < mB ∧ 0 < mC
  · obtain ⟨hpA, hpB, hpC⟩ := hpos
    set P := √(mA * mB * mC)
    set wA := 1 + P / (2 * mA)
    set wB := 1 + P / (2 * mB)
    set wC := 1 + P / (2 * mC)
    have hsumw : ∑ y ∈ Ω, w y * (wA * A y + wB * B y + wC * C y) =
        ∑ y ∈ Ω, w y * (wA * mA + wB * mB + wC * mC) := by
      rw [← Finset.sum_mul, hsum, one_mul]
      simp only [mul_add, Finset.sum_add_distrib, mA, mB, mC, Finset.mul_sum]
      congr 1; congr 1
      all_goals (apply Finset.sum_congr rfl; intro y _; ring)
    obtain ⟨y, hy, hle⟩ := Finset.exists_le_of_sum_le hne hsumw.le
    refine ⟨y, hy, le_trans ?_ hm4⟩
    apply hval_le_of_tangent hpA hpB hpC (hA y hy) (hB y hy) (hC y hy)
    exact le_of_mul_le_mul_left hle (hw y hy)
  · -- degenerate mean: `hval` is linear on the relevant face
    have hdeg : mA * mB * mC = 0 := by
      by_contra h
      apply hpos
      rcases mul_ne_zero_iff.1 h with ⟨h1, h3⟩
      rcases mul_ne_zero_iff.1 h1 with ⟨h1, h2⟩
      exact ⟨lt_of_le_of_ne hmA (Ne.symm h1), lt_of_le_of_ne hmB (Ne.symm h2),
        lt_of_le_of_ne hmC (Ne.symm h3)⟩
    have hdegy : ∀ y ∈ Ω, A y * B y * C y = 0 := by
      intro y hy
      rcases mul_eq_zero.1 hdeg with h | h
      · rcases mul_eq_zero.1 h with h | h
        · rw [zero_of A hA h y hy]; ring
        · rw [zero_of B hB h y hy]; ring
      · rw [zero_of C hC h y hy]; ring
    have hsuml : ∑ y ∈ Ω, w y * (A y + B y + C y) ≤
        ∑ y ∈ Ω, w y * (mA + mB + mC) := by
      rw [← Finset.sum_mul, hsum, one_mul]
      simp only [mul_add, Finset.sum_add_distrib, mA, mB, mC]
      exact le_rfl
    obtain ⟨y, hy, hle⟩ := Finset.exists_le_of_sum_le hne hsuml
    refine ⟨y, hy, ?_⟩
    have h1 := le_of_mul_le_mul_left hle (hw y hy)
    unfold hval at hm4 ⊢
    rw [hdegy y hy]
    rw [hdeg] at hm4
    simp only [Real.sqrt_zero, add_zero] at hm4 ⊢
    linarith

/-! ## Representable triples -/

/-- **Definition 3.3.** `(a, b, c) ∈ ℝ³_{≥0}` is representable if there are
`a₁, a₂, b₁, b₃, c₂, c₃ ∈ [0, 2]` with `a₁a₂ = a`, `b₁b₃ = b`, `c₂c₃ = c`,
`a₁ + b₁ ≤ 2`, `a₂ + c₂ ≤ 2`, `b₃ + c₃ ≤ 2`. (Picture: a triangle `u, v, w` with values
`a₁, b₁` on edge `uv`, `a₂, c₂` on `uw`, `b₃, c₃` on `vw`.) -/
def Representable (a b c : ℝ) : Prop :=
  0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧
    ∃ a₁ a₂ b₁ b₃ c₂ c₃ : ℝ, a₁ ∈ Set.Icc (0 : ℝ) 2 ∧ a₂ ∈ Set.Icc (0 : ℝ) 2 ∧
      b₁ ∈ Set.Icc (0 : ℝ) 2 ∧ b₃ ∈ Set.Icc (0 : ℝ) 2 ∧ c₂ ∈ Set.Icc (0 : ℝ) 2 ∧
      c₃ ∈ Set.Icc (0 : ℝ) 2 ∧ a₁ * a₂ = a ∧ b₁ * b₃ = b ∧ c₂ * c₃ = c ∧
      a₁ + b₁ ≤ 2 ∧ a₂ + c₂ ≤ 2 ∧ b₃ + c₃ ≤ 2

/-- The set `S_rep ⊆ ℝ³` of representable triples. -/
def Srep : Set (ℝ × ℝ × ℝ) := {s | Representable s.1 s.2.1 s.2.2}

/-- Representability with inequalities and tight edges: there are `X, Y, Z ∈ [0, 2]` with
`a ≤ XY`, `b ≤ (2-X)Z`, `c ≤ (2-Y)(2-Z)`. -/
def RepLe (a b c : ℝ) : Prop :=
  ∃ X Y Z : ℝ, X ∈ Set.Icc (0 : ℝ) 2 ∧ Y ∈ Set.Icc (0 : ℝ) 2 ∧ Z ∈ Set.Icc (0 : ℝ) 2 ∧
    a ≤ X * Y ∧ b ≤ (2 - X) * Z ∧ c ≤ (2 - Y) * (2 - Z)

lemma repLe_of_representable {a b c : ℝ} (h : Representable a b c) : RepLe a b c := by
  obtain ⟨-, -, -, a₁, a₂, b₁, b₃, c₂, c₃, ha₁, ha₂, hb₁, hb₃, hc₂, hc₃, ea, eb, ec, h1, h2, h3⟩ :=
    h
  refine ⟨a₁, a₂, b₃, ha₁, ha₂, hb₃, ea.ge, ?_, ?_⟩
  · rw [← eb]; exact mul_le_mul_of_nonneg_right (by linarith) hb₃.1
  · rw [← ec]; exact mul_le_mul (by linarith) (by linarith) hc₃.1 (by linarith [ha₂.2])

private lemma exists_mul_eq {t x y : ℝ} (ht : 0 ≤ t) (hxy : t ≤ x * y) (hx : 0 ≤ x)
    (hy : 0 ≤ y) : ∃ y' ∈ Set.Icc 0 y, x * y' = t := by
  rcases hx.eq_or_lt with hx0 | hx0
  · subst hx0
    refine ⟨0, ⟨le_rfl, hy⟩, ?_⟩
    simp at hxy; simp; linarith
  · refine ⟨t / x, ⟨by positivity, ?_⟩, by field_simp⟩
    rw [div_le_iff₀ hx0]; linarith

lemma representable_of_repLe {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : RepLe a b c) : Representable a b c := by
  obtain ⟨X, Y, Z, hX, hY, hZ, h1, h2, h3⟩ := h
  obtain ⟨a₂, ha₂, ea⟩ := exists_mul_eq ha h1 hX.1 hY.1
  obtain ⟨b₃, hb₃, eb⟩ := exists_mul_eq hb h2 (by linarith [hX.2]) hZ.1
  obtain ⟨c₃, hc₃, ec⟩ := exists_mul_eq hc h3 (by linarith [hY.2]) (by linarith [hZ.2])
  refine ⟨ha, hb, hc, X, a₂, 2 - X, b₃, 2 - Y, c₃, hX, ⟨ha₂.1, ha₂.2.trans hY.2⟩,
    ⟨by linarith [hX.2], by linarith [hX.1]⟩, ⟨hb₃.1, hb₃.2.trans hZ.2⟩,
    ⟨by linarith [hY.2], by linarith [hY.1]⟩, ⟨hc₃.1, by linarith [hc₃.2, hZ.1]⟩,
    ea, eb, ec, by linarith, by linarith [ha₂.2], by linarith [hb₃.2, hc₃.2]⟩

/-- Representable triples satisfy `hval ≤ 4` (AM–GM). -/
lemma hval_le_four_of_repLe {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (h : RepLe a b c) : hval a b c ≤ 4 := by
  obtain ⟨X, Y, Z, ⟨hX0, hX2⟩, ⟨hY0, hY2⟩, ⟨hZ0, hZ2⟩, h1, h2, h3⟩ := h
  have hmono : hval a b c ≤ hval (X * Y) ((2 - X) * Z) ((2 - Y) * (2 - Z)) :=
    hval_mono ha hb hc h1 h2 h3
  refine hmono.trans ?_
  unfold hval
  -- `√(UW) ≤ (U+W)/2` with `U = XZ(2-Y)`, `W = (2-X)Y(2-Z)`
  set U := X * Z * (2 - Y)
  set W := (2 - X) * Y * (2 - Z)
  have hU : 0 ≤ U := mul_nonneg (mul_nonneg hX0 hZ0) (by linarith)
  have hW : 0 ≤ W := mul_nonneg (mul_nonneg (by linarith) hY0) (by linarith)
  have e : X * Y * ((2 - X) * Z) * ((2 - Y) * (2 - Z)) = U * W := by ring
  rw [e]
  have hsq : √(U * W) ≤ (U + W) / 2 := by
    rw [Real.sqrt_le_left (by positivity)]
    nlinarith [sq_nonneg (U - W)]
  have : X * Y + (2 - X) * Z + (2 - Y) * (2 - Z) + (U + W) / 2 = 4 := by ring
  linarith

/-- Explicit representation of a point on the surface `x² + y² + z² + xyz = 4`. -/
lemma repLe_of_surface {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x ^ 2 + y ^ 2 + z ^ 2 + x * y * z = 4) : RepLe (x ^ 2) (y ^ 2) (z ^ 2) := by
  have hxyz : 0 ≤ x * y * z := by positivity
  by_cases hz2 : z ^ 2 = 4
  · have hx0 : x = 0 := by nlinarith [mul_nonneg hx hy, sq_nonneg x, sq_nonneg y]
    have hy0 : y = 0 := by nlinarith [mul_nonneg hx hy, sq_nonneg x, sq_nonneg y]
    refine ⟨0, 0, 0, ⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩,
      ?_, ?_, ?_⟩ <;> norm_num [hx0, hy0, hz2]
  by_cases hx2 : x ^ 2 = 4
  · have hy0 : y = 0 := by nlinarith [mul_nonneg hy hz, sq_nonneg z, sq_nonneg y]
    have hz0 : z = 0 := by nlinarith [mul_nonneg hy hz, sq_nonneg z, sq_nonneg y]
    refine ⟨2, 2, 0, ⟨by norm_num, le_rfl⟩, ⟨by norm_num, le_rfl⟩, ⟨le_rfl, by norm_num⟩,
      ?_, ?_, ?_⟩ <;> norm_num [hy0, hz0, hx2]
  by_cases hy2 : y ^ 2 = 4
  · have hx0 : x = 0 := by nlinarith [mul_nonneg hx hz, sq_nonneg z, sq_nonneg x]
    have hz0 : z = 0 := by nlinarith [mul_nonneg hx hz, sq_nonneg z, sq_nonneg x]
    refine ⟨0, 0, 2, ⟨le_rfl, by norm_num⟩, ⟨le_rfl, by norm_num⟩, ⟨by norm_num, le_rfl⟩,
      ?_, ?_, ?_⟩ <;> norm_num [hx0, hz0, hy2]
  have hx4 : 0 < 4 - x ^ 2 := by
    rcases (show x ^ 2 ≤ 4 by nlinarith).lt_or_eq with h' | h'
    · linarith
    · exact absurd h' hx2
  have hy4 : 0 < 4 - y ^ 2 := by
    rcases (show y ^ 2 ≤ 4 by nlinarith).lt_or_eq with h' | h'
    · linarith
    · exact absurd h' hy2
  have hz4 : 0 < 4 - z ^ 2 := by
    rcases (show z ^ 2 ≤ 4 by nlinarith).lt_or_eq with h' | h'
    · linarith
    · exact absurd h' hz2
  have k1 : (2 * x + y * z) ^ 2 = (4 - y ^ 2) * (4 - z ^ 2) := by linear_combination 4 * h
  have k2 : (2 * y + x * z) ^ 2 = (4 - x ^ 2) * (4 - z ^ 2) := by linear_combination 4 * h
  have k3 : (2 * z + x * y) ^ 2 = (4 - x ^ 2) * (4 - y ^ 2) := by linear_combination 4 * h
  set X := x * (2 * x + y * z) / (4 - z ^ 2)
  set Y := x * (2 * x + y * z) / (4 - y ^ 2)
  set Z := y * (2 * y + x * z) / (4 - x ^ 2)
  have eX : 2 - X = y * (2 * y + x * z) / (4 - z ^ 2) := by
    simp only [X]; field_simp; linear_combination -2 * h
  have eY : 2 - Y = z * (2 * z + x * y) / (4 - y ^ 2) := by
    simp only [Y]; field_simp; linear_combination -2 * h
  have eZ : 2 - Z = z * (2 * z + x * y) / (4 - x ^ 2) := by
    simp only [Z]; field_simp; linear_combination -2 * h
  have hX0 : 0 ≤ X := by positivity
  have hY0 : 0 ≤ Y := by positivity
  have hZ0 : 0 ≤ Z := by positivity
  have hX2 : 0 ≤ 2 - X := by rw [eX]; positivity
  have hY2 : 0 ≤ 2 - Y := by rw [eY]; positivity
  have hZ2 : 0 ≤ 2 - Z := by rw [eZ]; positivity
  refine ⟨X, Y, Z, ⟨hX0, by linarith⟩, ⟨hY0, by linarith⟩, ⟨hZ0, by linarith⟩, le_of_eq ?_,
    le_of_eq ?_, le_of_eq ?_⟩
  · have k := congrArg (fun t => x ^ 2 * t) k1
    simp only [X, Y]; field_simp
    first | linear_combination k | linear_combination (-1 : ℝ) * k
  · have k := congrArg (fun t => y ^ 2 * t) k2
    rw [eX]; simp only [Z]; field_simp
    first | linear_combination k | linear_combination (-1 : ℝ) * k
  · have k := congrArg (fun t => z ^ 2 * t) k3
    rw [eY, eZ]; field_simp
    first | linear_combination k | linear_combination (-1 : ℝ) * k

/-- The boundary value `z(a, b) = (√((4-a)(4-b)) - √(ab)) / 2`, the largest `√c` with
`(a, b, c)` representable. -/
noncomputable def zmax (a b : ℝ) : ℝ := (√((4 - a) * (4 - b)) - √a * √b) / 2

lemma zmax_props {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 4) :
    0 ≤ zmax a b ∧ zmax a b ^ 2 + √a * √b * zmax a b = 4 - a - b := by
  have hD : 0 ≤ (4 - a) * (4 - b) := mul_nonneg (by linarith) (by linarith)
  have hDsq := Real.sq_sqrt hD
  have hxs := Real.sq_sqrt ha
  have hys := Real.sq_sqrt hb
  have hx := Real.sqrt_nonneg a
  have hy := Real.sqrt_nonneg b
  have hDn := Real.sqrt_nonneg ((4 - a) * (4 - b))
  constructor
  · unfold zmax
    have : √a * √b ≤ √((4 - a) * (4 - b)) := by
      rw [← Real.sqrt_mul ha]; apply Real.sqrt_le_sqrt; nlinarith
    linarith
  · unfold zmax
    have e : (√a * √b) ^ 2 = a * b := by rw [mul_pow, hxs, hys]
    nlinarith [e, hDsq]

/-- **Lemma 3.5 (symmetric form).** A triple is representable iff it is nonnegative and
`a + b + c + √(abc) ≤ 4`. -/
theorem representable_iff {a b c : ℝ} :
    Representable a b c ↔ 0 ≤ a ∧ 0 ≤ b ∧ 0 ≤ c ∧ hval a b c ≤ 4 := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1,
      hval_le_four_of_repLe h.1 h.2.1 h.2.2.1 (repLe_of_representable h)⟩
  · rintro ⟨ha, hb, hc, h4⟩
    apply representable_of_repLe ha hb hc
    have hab : a + b ≤ 4 := by unfold hval at h4; linarith [Real.sqrt_nonneg (a * b * c)]
    obtain ⟨hz0, hz⟩ := zmax_props ha hb hab
    set z := zmax a b
    set x := √a
    set y := √b
    have hx := Real.sqrt_nonneg a
    have hy := Real.sqrt_nonneg b
    have hxs : x ^ 2 = a := Real.sq_sqrt ha
    have hys : y ^ 2 = b := Real.sq_sqrt hb
    -- `√c ≤ z`
    set t := √c
    have ht := Real.sqrt_nonneg c
    have hts : t ^ 2 = c := Real.sq_sqrt hc
    have htz : t ≤ z := by
      have e : √(a * b * c) = x * y * t := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul ha]
      unfold hval at h4
      rw [e] at h4
      by_contra hlt
      push Not at hlt
      have hxy : 0 ≤ x * y := mul_nonneg hx hy
      nlinarith [mul_le_mul_of_nonneg_left hlt.le hxy]
    have hsurf : x ^ 2 + y ^ 2 + z ^ 2 + x * y * z = 4 := by
      rw [hxs, hys]; linarith
    obtain ⟨X, Y, Z, hX, hY, hZ, h1, h2, h3⟩ := repLe_of_surface hx hy hz0 hsurf
    refine ⟨X, Y, Z, hX, hY, hZ, hxs ▸ h1, hys ▸ h2, ?_⟩
    calc c = t ^ 2 := hts.symm
      _ ≤ z ^ 2 := pow_le_pow_left₀ ht htz 2
      _ ≤ _ := h3

lemma mem_srep_iff {s : ℝ × ℝ × ℝ} :
    s ∈ Srep ↔ 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2 ∧ hval s.1 s.2.1 s.2.2 ≤ 4 :=
  representable_iff

/-- Representability is downward closed. -/
lemma Representable.mono {a b c a' b' c' : ℝ} (h : Representable a b c) (ha : 0 ≤ a')
    (hb : 0 ≤ b') (hc : 0 ≤ c') (haa : a' ≤ a) (hbb : b' ≤ b) (hcc : c' ≤ c) :
    Representable a' b' c' := by
  rw [representable_iff] at h ⊢
  exact ⟨ha, hb, hc, (hval_mono ha hb hc haa hbb hcc).trans h.2.2.2⟩

/-- `(1, 1, 1)` is representable (all edge values `1`): the initial state. -/
lemma representable_one : Representable 1 1 1 := by
  rw [representable_iff]; refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
  unfold hval; norm_num

/-! ## Lemma 3.7: `S_rep` is incurved -/

/-- **Definition 3.4.** `S ⊆ ℝ³_{≥0}` is incurved if no convex combination of two points of
`ℝ³_{≥0} \ S` lies in `S`. -/
def Incurved (S : Set (ℝ × ℝ × ℝ)) : Prop :=
  ¬ ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 ∧ ∃ s s' : ℝ × ℝ × ℝ,
    (0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2) ∧ s ∉ S ∧ (0 ≤ s'.1 ∧ 0 ≤ s'.2.1 ∧ 0 ≤ s'.2.2) ∧
      s' ∉ S ∧ q • s + (1 - q) • s' ∈ S

/-- **Lemma 3.7.** `S_rep` is incurved. -/
theorem srep_incurved : Incurved Srep := by
  rintro ⟨q, ⟨hq0, hq1⟩, s, s', hs0, hs, hs'0, hs', hmix⟩
  obtain ⟨a, b, c⟩ := s
  obtain ⟨a', b', c'⟩ := s'
  simp only at hs0 hs'0
  rw [mem_srep_iff] at hmix
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul] at hmix
  -- two-point distribution on `Bool`
  let w : Bool → ℝ := fun t => if t then q else 1 - q
  let A : Bool → ℝ := fun t => if t then a else a'
  let B : Bool → ℝ := fun t => if t then b else b'
  let C : Bool → ℝ := fun t => if t then c else c'
  let Ω : Finset Bool := (Finset.univ.filter fun t => 0 < w t)
  have hsumΩ : ∀ F : Bool → ℝ, ∑ t ∈ Ω, w t * F t = q * F true + (1 - q) * F false := by
    intro F
    have : ∑ t ∈ Ω, w t * F t = ∑ t, w t * F t := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro t _ ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at ht
      have : w t = 0 := le_antisymm ht (by cases t <;> simp [w] <;> linarith)
      simp [this]
    rw [this, Fintype.sum_bool]; simp [w]
  obtain ⟨t, ht, hgood⟩ := exists_hval_le_four Ω w A B C (a := q * a + (1 - q) * a')
    (b := q * b + (1 - q) * b') (c := q * c + (1 - q) * c')
    (fun t ht => (Finset.mem_filter.1 ht).2)
    (by simpa [w] using hsumΩ (fun _ => 1))
    (fun t _ => by cases t <;> simp [A, hs0.1, hs'0.1])
    (fun t _ => by cases t <;> simp [B, hs0.2.1, hs'0.2.1])
    (fun t _ => by cases t <;> simp [C, hs0.2.2, hs'0.2.2])
    (by rw [hsumΩ]; simp [A])
    (by rw [hsumΩ]; simp [B])
    (by rw [hsumΩ]; simp [C])
    hmix.2.2.2
  cases t
  · exact hs' (mem_srep_iff.2 ⟨hs'0.1, hs'0.2.1, hs'0.2.2, hgood⟩)
  · exact hs (mem_srep_iff.2 ⟨hs0.1, hs0.2.1, hs0.2.2, hgood⟩)

/-- Nonnegative orthant of `ℝ³`. -/
def Nonneg3 (s : ℝ × ℝ × ℝ) : Prop := 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2

/-- **Lemma 3.9** (for an arbitrary set `S`, in contrapositive form). If `S` is incurved, a
nonnegative weighted average of nonnegative triples that lies in `S` has some triple in `S`.
The paper argues by prefix averages; we argue by induction on the support. -/
theorem lemma_3_9 {S : Set (ℝ × ℝ × ℝ)} (hS : Incurved S) {β : Type*} (Ω : Finset β)
    (w : β → ℝ) (s : β → ℝ × ℝ × ℝ) (hw : ∀ y ∈ Ω, 0 < w y) (hsum : ∑ y ∈ Ω, w y = 1)
    (hs : ∀ y ∈ Ω, Nonneg3 (s y)) (havg : ∑ y ∈ Ω, w y • s y ∈ S) : ∃ y ∈ Ω, s y ∈ S := by
  classical
  induction Ω using Finset.induction_on generalizing w with
  | empty => simp at hsum
  | insert y₀ Ω hy₀ ih =>
    rw [Finset.sum_insert hy₀] at hsum havg
    by_cases hΩ : Ω = ∅
    · subst hΩ
      simp only [Finset.sum_empty, add_zero] at hsum havg
      rw [hsum, one_smul] at havg
      exact ⟨y₀, Finset.mem_insert_self _ _, havg⟩
    have hne : Ω.Nonempty := Finset.nonempty_iff_ne_empty.2 hΩ
    set W := ∑ y ∈ Ω, w y with hW
    have hWpos : 0 < W := Finset.sum_pos (fun y hy => hw y (Finset.mem_insert_of_mem hy)) hne
    -- the average over `Ω`
    set m := ∑ y ∈ Ω, (w y / W) • s y with hm
    have hmW : W • m = ∑ y ∈ Ω, w y • s y := by
      rw [hm, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [smul_smul, mul_div_cancel₀ _ hWpos.ne']
    by_cases hmS : m ∈ S
    · obtain ⟨y, hy, hyS⟩ := ih (fun y => w y / W)
        (fun y hy => div_pos (hw y (Finset.mem_insert_of_mem hy)) hWpos)
        (by rw [← Finset.sum_div, ← hW, div_self hWpos.ne'])
        (fun y hy => hs y (Finset.mem_insert_of_mem hy)) hmS
      exact ⟨y, Finset.mem_insert_of_mem hy, hyS⟩
    by_cases hy₀S : s y₀ ∈ S
    · exact ⟨y₀, Finset.mem_insert_self _ _, hy₀S⟩
    exfalso
    apply hS
    have hm0 : Nonneg3 m := by
      have hcomp : ∀ y ∈ Ω, 0 ≤ w y / W := fun y hy =>
        (div_pos (hw y (Finset.mem_insert_of_mem hy)) hWpos).le
      refine ⟨?_, ?_, ?_⟩
      · rw [hm, Prod.fst_sum]
        exact Finset.sum_nonneg fun y hy => by
          rw [Prod.smul_fst, smul_eq_mul]
          exact mul_nonneg (hcomp y hy) (hs y (Finset.mem_insert_of_mem hy)).1
      · rw [hm, Prod.snd_sum, Prod.fst_sum]
        exact Finset.sum_nonneg fun y hy => by
          rw [Prod.smul_snd, Prod.smul_fst, smul_eq_mul]
          exact mul_nonneg (hcomp y hy) (hs y (Finset.mem_insert_of_mem hy)).2.1
      · rw [hm, Prod.snd_sum, Prod.snd_sum]
        exact Finset.sum_nonneg fun y hy => by
          rw [Prod.smul_snd, Prod.smul_snd, smul_eq_mul]
          exact mul_nonneg (hcomp y hy) (hs y (Finset.mem_insert_of_mem hy)).2.2
    refine ⟨w y₀, ⟨(hw y₀ (Finset.mem_insert_self _ _)).le, by linarith⟩, s y₀, m,
      hs y₀ (Finset.mem_insert_self _ _), hy₀S, hm0, hmS, ?_⟩
    have : 1 - w y₀ = W := by linarith
    rw [this, hmW]; exact havg

/-- Lemma 3.9 instantiated with `S_rep` (via Lemma 3.7). -/
theorem exists_mem_srep_of_avg {β : Type*} (Ω : Finset β) (w : β → ℝ) (s : β → ℝ × ℝ × ℝ)
    (hw : ∀ y ∈ Ω, 0 < w y) (hsum : ∑ y ∈ Ω, w y = 1) (hs : ∀ y ∈ Ω, Nonneg3 (s y))
    (havg : ∑ y ∈ Ω, w y • s y ∈ Srep) : ∃ y ∈ Ω, s y ∈ Srep :=
  lemma_3_9 srep_incurved Ω w s hw hsum hs havg

/-! ## Lemma 3.5 in the paper's form, and Lemma 3.6 -/

/-- The function of Lemma 3.6: `f(a,b) = 4 + ½(ab - 2a - 2b - √(ab(4-a)(4-b)))`. -/
noncomputable def f (a b : ℝ) : ℝ := 4 + (a * b - 2 * a - 2 * b - √(a * b * (4 - a) * (4 - b))) / 2

lemma f_eq_zmax_sq {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 4) :
    f a b = zmax a b ^ 2 := by
  obtain ⟨-, hz⟩ := zmax_props ha hb hab
  have e : √(a * b * (4 - a) * (4 - b)) = √a * √b * √((4 - a) * (4 - b)) := by
    rw [← Real.sqrt_mul ha, ← Real.sqrt_mul (by positivity)]; ring_nf
  have hDsq := Real.sq_sqrt (show 0 ≤ (4 - a) * (4 - b) from
    mul_nonneg (by linarith) (by linarith))
  have hxs := Real.sq_sqrt ha
  have hys := Real.sq_sqrt hb
  unfold f; rw [e]; unfold zmax
  nlinarith [hDsq, hxs, hys]

lemma f_nonneg {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b ≤ 4) : 0 ≤ f a b := by
  rw [f_eq_zmax_sq ha hb hab]; positivity

/-- **Lemma 3.5** (with the parenthesization of Lemma 3.6):
`S_rep = {(a,b,c) ∈ ℝ³_{≥0} | a + b ≤ 4, c ≤ f(a,b)}`. -/
theorem srep_eq_f : Srep = {s : ℝ × ℝ × ℝ | 0 ≤ s.1 ∧ 0 ≤ s.2.1 ∧ 0 ≤ s.2.2 ∧
    s.1 + s.2.1 ≤ 4 ∧ s.2.2 ≤ f s.1 s.2.1} := by
  ext ⟨a, b, c⟩
  simp only [Set.mem_ofPred_eq, mem_srep_iff]
  constructor
  · rintro ⟨ha, hb, hc, h4⟩
    have hab : a + b ≤ 4 := by unfold hval at h4; linarith [Real.sqrt_nonneg (a * b * c)]
    refine ⟨ha, hb, hc, hab, ?_⟩
    -- reuse the proof of `representable_iff`: `√c ≤ zmax a b`
    obtain ⟨hz0, hz⟩ := zmax_props ha hb hab
    have hx := Real.sqrt_nonneg a
    have hy := Real.sqrt_nonneg b
    have ht := Real.sqrt_nonneg c
    have hts : √c ^ 2 = c := Real.sq_sqrt hc
    have e : √(a * b * c) = √a * √b * √c := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul ha]
    unfold hval at h4; rw [e] at h4
    have htz : √c ≤ zmax a b := by
      by_contra hlt; push Not at hlt
      have hxy : 0 ≤ √a * √b := mul_nonneg hx hy
      nlinarith [mul_le_mul_of_nonneg_left hlt.le hxy, Real.sq_sqrt ha, Real.sq_sqrt hb]
    rw [f_eq_zmax_sq ha hb hab, ← hts]
    exact pow_le_pow_left₀ ht htz 2
  · rintro ⟨ha, hb, hc, hab, hcf⟩
    refine ⟨ha, hb, hc, ?_⟩
    obtain ⟨hz0, hz⟩ := zmax_props ha hb hab
    rw [f_eq_zmax_sq ha hb hab] at hcf
    have ht := Real.sqrt_nonneg c
    have htz : √c ≤ zmax a b := by
      rw [← Real.sqrt_sq hz0]; exact Real.sqrt_le_sqrt hcf
    have hts : √c ^ 2 = c := Real.sq_sqrt hc
    have e : √(a * b * c) = √a * √b * √c := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul ha]
    unfold hval; rw [e]
    have hxy : 0 ≤ √a * √b := mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b)
    nlinarith [mul_le_mul_of_nonneg_left htz hxy, mul_le_mul htz htz ht hz0]

/-- **Lemma 3.5 as printed is false.** The statement of Lemma 3.5 omits the parentheses:
`f(a,b) = 4 + ½·ab - 2a - 2b - √(ab(4-a)(4-b))`. With this reading, `(0, 1, 3)` is
representable (`a₁ = a₂ = 0`, `b₁ = 2`, `b₃ = ½`, `c₂ = 2`, `c₃ = 3/2`), but
`3 > 4 + 0 - 0 - 2 - 0 = 2`. -/
theorem lemma_3_5_as_printed_false :
    Representable 0 1 3 ∧
      ¬ (3 : ℝ) ≤ 4 + 1 / 2 * (0 * 1) - 2 * 0 - 2 * 1 - √(0 * 1 * (4 - 0) * (4 - 1)) := by
  refine ⟨⟨le_rfl, by norm_num, by norm_num, 0, 0, 2, 1 / 2, 2, 3 / 2, ?_⟩, ?_⟩
  · norm_num
  · norm_num

/-- The domain `U = {(a, b) ∈ ℝ²_{≥0} | a + b ≤ 4}` of Lemma 3.6. -/
def U : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ p.1 + p.2 ≤ 4}

lemma convex_U : Convex ℝ U := by
  intro p hp p' hp' s t hs ht hst
  obtain ⟨h1, h2, h3⟩ := hp
  obtain ⟨h1', h2', h3'⟩ := hp'
  simp only [U, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd,
    smul_eq_mul]
  refine ⟨by positivity, by positivity, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_left h3 hs, mul_le_mul_of_nonneg_left h3' ht]

/-- **Lemma 3.6.** `f` is convex on `U`. We derive it from Lemma 3.7 (`srep_incurved`) and
Lemma 3.5 (`srep_eq_f`), so the Hessian computation of the appendix is not needed. -/
theorem f_convexOn : ConvexOn ℝ U (fun p => f p.1 p.2) := by
  refine ⟨convex_U, ?_⟩
  intro p hp p' hp' q q' hq hq' hqq
  simp only [smul_eq_mul]
  by_contra hlt
  push Not at hlt
  obtain ⟨h1, h2, h3⟩ := hp
  obtain ⟨h1', h2', h3'⟩ := hp'
  have hm : q • p + q' • p' ∈ U := convex_U ⟨h1, h2, h3⟩ ⟨h1', h2', h3'⟩ hq hq' hqq
  set m := q • p + q' • p'
  set ε := (f m.1 m.2 - (q * f p.1 p.2 + q' * f p'.1 p'.2)) / 2 with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hf := f_nonneg h1 h2 h3
  have hf' := f_nonneg h1' h2' h3'
  apply srep_incurved
  refine ⟨q, ⟨hq, by linarith⟩, (p.1, p.2, f p.1 p.2 + ε), (p'.1, p'.2, f p'.1 p'.2 + ε),
    ⟨h1, h2, by linarith⟩, ?_, ⟨h1', h2', by linarith⟩, ?_, ?_⟩
  · rw [srep_eq_f]; simp only [Set.mem_ofPred_eq, not_and, not_le]; intros; linarith
  · rw [srep_eq_f]; simp only [Set.mem_ofPred_eq, not_and, not_le]; intros; linarith
  · rw [srep_eq_f]
    have hq1 : 1 - q = q' := by linarith
    rw [hq1]
    obtain ⟨hm1, hm2, hm3⟩ := hm
    simp only [m, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
      at hm1 hm2 hm3 hε
    simp only [Set.mem_ofPred_eq, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
    refine ⟨hm1, hm2, by positivity, hm3, ?_⟩
    have e : q * (f p.1 p.2 + ε) + q' * (f p'.1 p'.2 + ε) =
        q * f p.1 p.2 + q' * f p'.1 p'.2 + ε := by linear_combination ε * hqq
    rw [e]; linarith

end SharpThresholdLLL
