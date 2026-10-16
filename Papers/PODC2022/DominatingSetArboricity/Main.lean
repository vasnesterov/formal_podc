import Papers.PODC2022.DominatingSetArboricity.Randomized
import Papers.PODC2022.DominatingSetArboricity.Theorem12Asymptotic
import Papers.PODC2022.DominatingSetArboricity.Theorem13Gap

/-!
# Combined statements of Theorems 1.2 and 1.3

* `theorem_1_2_full`: with `γ = max(2, α^{1/(2t)})`, `α ≥ 2`, `1 ≤ t ≤ α/ln α`: the randomized
  algorithm always outputs a dominating set, its expected weight is `≤ (α + 417 α/t) · w(D)` for
  every dominating set `D`, and Lemma 4.6 runs `≤ 50 t (ln(Δ+1) + 1)` iterations.
* `theorem_1_3_full`: for `Δ ≥ 2`, `k ≥ 1`, `γ = Δ^{1/k}`: if `(Δ+1)^k ≤ Δ^{k+1}`, Lemma 4.6's
  algorithm from the trivial packing gives expected factor `γ(γ+1)(k+1)`; otherwise the trivial
  one-round algorithm already achieves that factor.
-/

set_option linter.unusedSectionVars false

namespace DominatingSetArboricity

open Finset SimpleGraph

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- **Theorem 1.2** (combined, asymptotic form; requires `α ≥ 2` so that `t ≤ α/ln α` makes
sense). -/
theorem theorem_1_2_full {α : ℕ} (o : G.OutOrientation α) (hα : 2 ≤ α) {t : ℕ} (ht : 1 ≤ t)
    (htα : (t : ℝ) * Real.log α ≤ α) {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) {D : Finset V}
    (hD : IsDominating G D) :
    let γ : ℝ := max 2 ((α : ℝ) ^ (1 / (2 * (t : ℝ))))
    let ε : ℝ := 1 / (4 * t)
    let lam : ℝ := ε / (α + 1)
    let p := partialDS G ε lam w
    (∀ cs, IsDominating G (runCoins (rstep G w γ) cs 0 (numSteps G γ lam) (rinit p.S p.x)).T) ∧
    expect (sampProb G γ) (rstep G w γ) (fun s => wt w s.T) 0 (numSteps G γ lam)
        (rinit p.S p.x) ≤ (α + 417 * α / t) * wt w D ∧
    ((numSteps G γ lam : ℕ) : ℝ) ≤ 50 * t * (Real.log (G.maxDegree + 1) + 1) := by
  intro γ ε lam p
  have hγ : 1 < γ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  obtain ⟨h1, h2⟩ := theorem_1_2 o (by omega) ht hw hγ hD
  have harith := theorem_1_2_arith hα ht htα
  have hwD : 0 ≤ wt w D := sum_nonneg fun v _ => hw v
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht
  refine ⟨h1, h2.trans ?_, ?_⟩
  · refine mul_le_mul_of_nonneg_right ?_ hwD
    calc (α : ℝ) * (1 + 1 / t) + γ * (γ + 1) * ⌈Real.logb γ (4 * t * (α + 1))⌉₊
        ≤ α * (1 + 1 / t) + 416 * α / t := by gcongr
      _ = α + 417 * α / t := by field_simp; ring
  · have hr := theorem_1_2_rounds_arith (Δ := G.maxDegree) hα ht htα
    have hlam : lam⁻¹ = 4 * t * (α + 1) := by
      simp only [lam, ε]; field_simp
    simp only [numSteps, numPhases, itersPerPhase, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      hlam]
    exact hr

/-- **Theorem 1.3** (combined). For `Δ ≥ 2`, `k ≥ 1` and `γ = Δ^{1/k}`: in the regime
`(Δ+1)^k ≤ Δ^{k+1}` the algorithm of Lemma 4.6 (from `S = ∅`, `x = τ/(Δ+1)`) always dominates and
has expected weight `≤ γ(γ+1)(k+1) · w(D)`; in the other regime the trivial one-round algorithm
`completion G w ∅` has weight `≤ γ(γ+1)(k+1) · w(D)`. -/
theorem theorem_1_3_full {w : V → ℝ} (hw : ∀ v, 0 ≤ w v) (hΔ : 2 ≤ G.maxDegree) {k : ℕ}
    (hk : 1 ≤ k) {D : Finset V} (hD : IsDominating G D) :
    let γ : ℝ := (G.maxDegree : ℝ) ^ (1 / (k : ℝ))
    (((G.maxDegree : ℝ) + 1) ^ k ≤ (G.maxDegree : ℝ) ^ (k + 1) →
      (∀ cs, IsDominating G (runCoins (rstep G w γ) cs 0 (numSteps G γ (1 / (G.maxDegree + 1)))
        (rinit ∅ (init G w).x)).S') ∧
      expect (sampProb G γ) (rstep G w γ) (fun s => wt w s.S') 0
        (numSteps G γ (1 / (G.maxDegree + 1))) (rinit ∅ (init G w).x) ≤
        γ * (γ + 1) * (k + 1) * wt w D) ∧
    ((G.maxDegree : ℝ) ^ (k + 1) < ((G.maxDegree : ℝ) + 1) ^ k →
      IsDominating G (completion G w ∅) ∧ wt w (completion G w ∅) ≤ γ * (γ + 1) * (k + 1) * wt w D) := by
  intro γ
  have hwD : 0 ≤ wt w D := sum_nonneg fun v _ => hw v
  have hΔr : (2 : ℝ) ≤ G.maxDegree := by exact_mod_cast hΔ
  have hγ : 1 < γ := Real.one_lt_rpow (by linarith) (by positivity)
  refine ⟨fun hgap => ?_, fun hgap => ?_⟩
  · obtain ⟨h1, h2⟩ := theorem_1_3 hw hγ (by omega) hD
    refine ⟨h1, h2.trans ?_⟩
    have := theorem_1_3_param hΔ hk hgap
    have hc : (⌈Real.logb γ ((G.maxDegree : ℝ) + 1)⌉₊ : ℝ) ≤ k + 1 := by exact_mod_cast this
    gcongr
  · obtain ⟨h1, h2⟩ := trivial_approx hw hD
    refine ⟨h1, h2.trans ?_⟩
    gcongr
    exact claimed_factor_ge (by omega) hk hgap

end DominatingSetArboricity
