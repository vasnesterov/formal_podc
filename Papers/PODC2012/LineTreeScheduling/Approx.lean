import Papers.PODC2012.LineTreeScheduling.Algorithm
import Papers.PODC2012.LineTreeScheduling.Lemma31
import Papers.PODC2012.LineTreeScheduling.Lemma61

/-!
# Approximation guarantees of the distributed algorithms on an abstract instance

Given a *layered decomposition* of the demand instances (groups `grp d < ℓ` and critical edges
`crit d ⊆ path d` with `|crit d| ≤ Δ`, such that `path(d₂)` meets `crit d₁` whenever `d₁, d₂`
overlap and `grp d₁ ≤ grp d₂`), the algorithm of Figure 7 (Section 5) with an arbitrary MIS
oracle:

* `unit_alg` (unit heights, `ξ = 2(Δ+1)/(2(Δ+1)+1)`; Theorem 5.3 for `Δ = 6`, Theorem 7.1 for
  `Δ = 3`): the output is an independent set `S` with `(1-ε)/(Δ+1) · LP ≤ p(S)`;
* `narrow_alg` (narrow instances with heights in `[h_min, 1/2]`,
  `ξ = (1+Δ²)/((1+Δ²) + h_min)`; Lemma 6.2 for `Δ = 6`): the output is a feasible solution with
  `(1-ε)/(1+2Δ²) · LP ≤ p(S)`.

In both cases the first phase consists of `ℓ · b · K` steps (one MIS computation each), where
`ξ^b ≤ ε` and `p_max < 2^K p_min`; `exists_stages` and `exists_steps` give the explicit choices
`b = ⌈log_ξ ε⌉` and `K = ⌊log₂ ⌊p_max/p_min⌋⌋ + 1`.
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open Finset

variable {A D E : Type*} [DecidableEq A] [DecidableEq D] [DecidableEq E]

noncomputable section

/-- A layered decomposition of the demand instances of an abstract instance (Section 4.4, all
networks at once): groups `grp d < ℓ`, critical edges `crit d ⊆ path d` with `|crit d| ≤ Δ`, and the
layering property. Group `0` is the paper's `G₁`. -/
structure Inst.Layered (I : Inst A D E) (Δ ℓ : ℕ) where
  /-- The group of an instance. -/
  grp : D → ℕ
  /-- The critical edges `π(d)`. -/
  crit : D → Finset E
  grp_lt : ∀ d, grp d < ℓ
  crit_subset : ∀ d, crit d ⊆ I.path d
  card_crit : ∀ d, (crit d).card ≤ Δ
  prop : ∀ d₁ d₂, grp d₁ ≤ grp d₂ → I.Overlap d₁ d₂ → (crit d₁ ∩ I.path d₂).Nonempty

/-- The progress factor of the unit-height algorithm, `ξ = 2Δ'/(2Δ'+1)` with `Δ' = Δ + 1`
(`14/15` for `Δ = 6`, `8/9` for `Δ = 3`). -/
def ξUnit (Δ : ℕ) : ℝ := 2 * ((Δ : ℝ) + 1) / (2 * ((Δ : ℝ) + 1) + 1)

lemma ξUnit_six : ξUnit 6 = 14 / 15 := by norm_num [ξUnit]
lemma ξUnit_three : ξUnit 3 = 8 / 9 := by norm_num [ξUnit]

/-- The progress factor of the narrow-instance algorithm, `ξ = c/(c + h_min)` with `c = 1 + Δ²`. -/
def ξNarrow (Δ : ℕ) (hmin : ℝ) : ℝ := (1 + (Δ : ℝ) ^ 2) / ((1 + (Δ : ℝ) ^ 2) + hmin)

/-- A number of stages `b` with `ξ^b ≤ ε` exists (the paper's `⌈log_ξ ε⌉ = O(log 1/ε)`). -/
lemma exists_stages {ξ ε : ℝ} (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hε : 0 < ε) :
    ξ ^ ⌈Real.logb ξ ε⌉₊ ≤ ε := by
  have h1 : ξ ^ (⌈Real.logb ξ ε⌉₊ : ℝ) ≤ ξ ^ Real.logb ξ ε :=
    Real.rpow_le_rpow_of_exponent_ge hξ0 hξ1.le (Nat.le_ceil _)
  rwa [Real.rpow_natCast, Real.rpow_logb hξ0 hξ1.ne hε] at h1

/-- The number of steps per stage `K = ⌊log₂ ⌊p_max/p_min⌋⌋ + 1` satisfies `p_max < 2^K p_min`. -/
lemma exists_steps {pmin pmax : ℝ} (hpmin : 0 < pmin) :
    pmax < 2 ^ (Nat.log 2 ⌊pmax / pmin⌋₊ + 1) * pmin := by
  have h1 : pmax / pmin < 2 ^ (Nat.log 2 ⌊pmax / pmin⌋₊ + 1) := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) ⌊pmax / pmin⌋₊
    have h2 : pmax / pmin < ⌊pmax / pmin⌋₊ + 1 := Nat.lt_floor_add_one _
    have h3 : ((⌊pmax / pmin⌋₊ : ℕ) : ℝ) + 1 ≤ (2 : ℝ) ^ (Nat.log 2 ⌊pmax / pmin⌋₊ + 1) := by
      exact_mod_cast this
    linarith
  rwa [div_lt_iff₀ hpmin] at h1

namespace Inst

variable {I : Inst A D E} [Fintype A] [Fintype D] [Fintype E]

/-- **The unit-height algorithm** (Section 5, Figure 7) on an abstract instance with a layered
decomposition with critical set size `Δ` and length `ℓ`: for any MIS oracle, after `ℓ b K` steps
of the first phase the second phase outputs an independent set `S` with
`(1-ε)/(Δ+1) · x ≤ p(S)` for every feasible LP solution `x`. -/
theorem unit_alg {Δ ℓ : ℕ} (L : I.Layered Δ ℓ) {pmin pmax : ℝ} (hpmin0 : 0 < pmin)
    (hpmin : ∀ d, pmin ≤ I.profit d) (hpmax : ∀ d, I.profit d ≤ pmax) {ε : ℝ}
    {b K : ℕ} (hb : ξUnit Δ ^ b ≤ ε) (hK : pmax < 2 ^ K * pmin)
    {mis : ℕ → Finset D → Finset D} (hmis : ∀ t U, I.IsMIS U (mis t U))
    {x : D → ℝ} (hx : I.IsLPFeasible (fun _ => 1) x) :
    let P : Sched D := ⟨L.grp, b, K, ξUnit Δ⟩
    let S := I.solU (I.algI (unitRule L.crit) P mis) (ℓ * b * K)
    I.IsIndep S ∧ (1 - ε) / (Δ + 1) * I.lpValue x ≤ I.profitOf S := by
  intro P S
  have hΔ0 : (0 : ℝ) ≤ Δ := Nat.cast_nonneg Δ
  have hξ0 : 0 < ξUnit Δ := by unfold ξUnit; positivity
  have hξ1 : ξUnit Δ < 1 := by
    unfold ξUnit; rw [div_lt_one (by positivity)]; linarith
  have H : I.AlgHyp (unitRule L.crit) P mis :=
    ⟨I.unitRule_wf L.crit_subset, fun d => lt_of_lt_of_le hpmin0 (hpmin d), hξ0, hξ1, hmis⟩
  have hkill : ∀ d₁ d₂, P.grp d₁ = P.grp d₂ → I.Conflict d₁ d₂ →
      (1 : ℝ) ≤ I.weight (unitRule L.crit) d₁ d₂ := by
    intro d₁ d₂ hg hc
    simp only [weight, unitRule, one_mul]
    have hcard := Nat.cast_nonneg (α := ℝ) (L.crit d₁ ∩ I.path d₂).card
    rcases hc with hdem | hov
    · simp only [hdem, ↓reduceIte]; linarith
    · have : (1 : ℝ) ≤ (L.crit d₁ ∩ I.path d₂).card := by
        exact_mod_cast Finset.card_pos.2 (L.prop d₁ d₂ hg.le hov)
      have : (0 : ℝ) ≤ if I.dem d₁ = I.dem d₂ then 1 else 0 := by split_ifs <;> norm_num
      linarith
  have hden : ∀ d, (unitRule L.crit).denom d ≤ Δ + 1 := by
    intro d
    simp only [Rule.denom, unitRule, one_mul]
    have : ((L.crit d).card : ℝ) ≤ Δ := by exact_mod_cast L.card_crit d
    linarith
  have hratio : 2 * ((Δ : ℝ) + 1) * (1 - P.ξ) ≤ 1 * P.ξ := by
    show 2 * ((Δ : ℝ) + 1) * (1 - ξUnit Δ) ≤ 1 * ξUnit Δ
    unfold ξUnit
    rw [le_iff_eq_or_lt]; left
    field_simp
    ring
  have hsat := alg_sat H one_pos hkill hden hratio hpmin hpmax hK L.grp_lt
  have hv := alg_validRun H (ℓ * b * K)
  have hint := alg_interference H L.prop (ℓ * b * K)
  have hlam : ∀ d, (1 - ε) * I.profit d ≤
      I.lhs (fun _ => 1) (I.run (unitRule L.crit) (I.algI (unitRule L.crit) P mis) (ℓ * b * K)) d := by
    intro d
    rw [← algState_eq_run]
    refine le_trans ?_ (hsat d)
    have := (H.profit_pos d).le
    have : (1 - ε) ≤ (1 - P.ξ ^ P.b) := by show 1 - ε ≤ 1 - ξUnit Δ ^ b; linarith
    nlinarith
  exact lemma_3_1 L.crit_subset hv hint (fun t _ d _ => L.card_crit d) hlam hx

/-- **The narrow-instance algorithm** (Section 6.1, Lemma 6.2) on an abstract instance with
heights in `[h_min, 1/2]` and a layered decomposition with critical set size `Δ`, length `ℓ`:
for any MIS oracle, after `ℓ b K` steps the second phase outputs a feasible solution `S` with
`(1-ε)/(1+2Δ²) · x ≤ p(S)` for every feasible solution `x` of the LP with heights. -/
theorem narrow_alg {Δ ℓ : ℕ} (L : I.Layered Δ ℓ) {h : D → ℝ} {hmin : ℝ} (hmin0 : 0 < hmin)
    (hmin12 : hmin ≤ 1 / 2) (hhmin : ∀ d, hmin ≤ h d) (hh : ∀ d, h d ≤ 1 / 2) {pmin pmax : ℝ}
    (hpmin0 : 0 < pmin) (hpmin : ∀ d, pmin ≤ I.profit d) (hpmax : ∀ d, I.profit d ≤ pmax)
    {ε : ℝ} {b K : ℕ} (hb : ξNarrow Δ hmin ^ b ≤ ε) (hK : pmax < 2 ^ K * pmin)
    {mis : ℕ → Finset D → Finset D} (hmis : ∀ t U, I.IsMIS U (mis t U))
    {x : D → ℝ} (hx : I.IsLPFeasible h x) :
    let P : Sched D := ⟨L.grp, b, K, ξNarrow Δ hmin⟩
    let S := I.solH h (I.algI (narrowRule h L.crit) P mis) (ℓ * b * K)
    I.IsHFeasible h S ∧ (1 - ε) / (1 + 2 * Δ ^ 2) * I.lpValue x ≤ I.profitOf S := by
  intro P S
  have hh0 : ∀ d, 0 ≤ h d := fun d => hmin0.le.trans (hhmin d)
  have hc1 : (1 : ℝ) ≤ 1 + (Δ : ℝ) ^ 2 := by nlinarith
  have hξ0 : 0 < ξNarrow Δ hmin := by unfold ξNarrow; positivity
  have hξ1 : ξNarrow Δ hmin < 1 := by
    unfold ξNarrow; rw [div_lt_one (by positivity)]; linarith
  have H : I.AlgHyp (narrowRule h L.crit) P mis :=
    ⟨I.narrowRule_wf hh0 L.crit_subset, fun d => lt_of_lt_of_le hpmin0 (hpmin d), hξ0, hξ1, hmis⟩
  have hkill : ∀ d₁ d₂, P.grp d₁ = P.grp d₂ → I.Conflict d₁ d₂ →
      2 * hmin ≤ I.weight (narrowRule h L.crit) d₁ d₂ := by
    intro d₁ d₂ hg hc
    simp only [weight, narrowRule]
    have hcard := Nat.cast_nonneg (α := ℝ) (L.crit d₁ ∩ I.path d₂).card
    have hcard' := Nat.cast_nonneg (α := ℝ) (L.crit d₁).card
    have hprod : 0 ≤ h d₂ * (2 * ((L.crit d₁).card : ℝ)) * (L.crit d₁ ∩ I.path d₂).card := by
      have := hh0 d₂; positivity
    rcases hc with hdem | hov
    · simp only [hdem, ↓reduceIte]; linarith
    · have hne := L.prop d₁ d₂ hg.le hov
      have h1 : (1 : ℝ) ≤ (L.crit d₁ ∩ I.path d₂).card := by exact_mod_cast Finset.card_pos.2 hne
      have h2 : (1 : ℝ) ≤ (L.crit d₁).card := by
        exact_mod_cast Finset.card_pos.2 (hne.mono Finset.inter_subset_left)
      have : (0 : ℝ) ≤ if I.dem d₁ = I.dem d₂ then 1 else 0 := by split_ifs <;> norm_num
      have h3 := hhmin d₂
      have : 2 * hmin ≤ h d₂ * (2 * ((L.crit d₁).card : ℝ)) * (L.crit d₁ ∩ I.path d₂).card := by
        have : 2 * hmin ≤ h d₂ * (2 * ((L.crit d₁).card : ℝ)) := by nlinarith
        nlinarith
      linarith
  have hden : ∀ d, (narrowRule h L.crit).denom d ≤ 1 + (Δ : ℝ) ^ 2 := by
    intro d
    simp only [Rule.denom, narrowRule]
    have h1 : ((L.crit d).card : ℝ) ≤ Δ := by exact_mod_cast L.card_crit d
    have h2 := Nat.cast_nonneg (α := ℝ) (L.crit d).card
    have := hh d
    have := hh0 d
    have : h d * (2 * ((L.crit d).card : ℝ)) * (L.crit d).card ≤ ((L.crit d).card : ℝ) ^ 2 := by
      nlinarith
    nlinarith
  have hratio : 2 * (1 + (Δ : ℝ) ^ 2) * (1 - P.ξ) ≤ 2 * hmin * P.ξ := by
    show 2 * (1 + (Δ : ℝ) ^ 2) * (1 - ξNarrow Δ hmin) ≤ 2 * hmin * ξNarrow Δ hmin
    unfold ξNarrow
    rw [le_iff_eq_or_lt]; left
    field_simp
    ring
  have hsat := alg_sat H (by linarith) hkill hden hratio hpmin hpmax hK L.grp_lt
  have hv := alg_validRun H (ℓ * b * K)
  have hint := alg_interference H L.prop (ℓ * b * K)
  have hlam : ∀ d, (1 - ε) * I.profit d ≤
      I.lhs h (I.run (narrowRule h L.crit) (I.algI (narrowRule h L.crit) P mis) (ℓ * b * K)) d := by
    intro d
    rw [← algState_eq_run]
    refine le_trans ?_ (hsat d)
    have := (H.profit_pos d).le
    have : (1 - ε) ≤ (1 - P.ξ ^ P.b) := by show 1 - ε ≤ 1 - ξNarrow Δ hmin ^ b; linarith
    nlinarith
  exact lemma_6_1 hh0 hh L.crit_subset hv hint (fun t _ d _ => L.card_crit d) hlam hx

end Inst

end

end Podc.LineTreeScheduling
