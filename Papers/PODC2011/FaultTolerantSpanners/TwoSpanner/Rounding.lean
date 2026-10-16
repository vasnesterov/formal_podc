import Papers.PODC2011.FaultTolerantSpanners.TwoSpanner.Defs

/-!
# Probabilistic analysis of the rounding (Theorem 3.3 of Dinitz–Krauthgamer, PODC'11)

Algorithm 1 draws independent thresholds `T_v` uniform on `[0, 1]` and keeps the arc `(u, v)` iff
`min {T_u, T_v} ≤ α x_{(u,v)}` (`roundE`). The threshold vector is distributed according to
`thresholdMeasure V := Measure.pi (fun _ => unifI)`, where `unifI` is Lebesgue measure restricted
to `[0, 1]`.

Main results (all constants explicit):
* `prob_not_satisfies_le`: for `(x, f)` feasible for LP (4) and `α ≥ 4`, each arc `(u, v) ∈ E` is
  left unsatisfied with probability at most `exp(-α/4)`.
* `expected_cost_le`: `E[cost] ≤ 2 α · ∑_e c_e x_e` (for `c, x ≥ 0`, `α ≥ 0`).
* `prob_cost_gt_le`: `Pr[cost > 6 α · ∑_e c_e x_e] ≤ 1/3` (Markov; also when the LP value is `0`).
* `rounding_success` (**Theorem 3.3**): with probability at least `2/3 - |E| exp(-α/4)` all arcs are
  satisfied and the cost is at most `6 α · LP`.
* `rounding_success_log`: with `α = 12 ln n` (`n = |V| ≥ 2`) the success probability is at least
  `2/3 - 1/n` and the cost bound is `72 ln n · LP`.

The lower-tail bound is a multiplicative Chernoff bound proved from scratch via the product formula
for `E[2^{-X}]` (`chernoff_count`).
-/

open Finset MeasureTheory ProbabilityTheory

namespace DinitzKrauthgamer

/-- Uniform distribution on `[0, 1]`: Lebesgue measure restricted to `[0, 1]`. -/
noncomputable def unifI : Measure ℝ := (volume : Measure ℝ).restrict (Set.Icc 0 1)

instance : IsProbabilityMeasure unifI := by
  constructor
  simp [unifI]

lemma unifI_Iic {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : unifI.real (Set.Iic a) = a := by
  have : Set.Iic a ∩ Set.Icc (0 : ℝ) 1 = Set.Icc 0 a := by
    ext t; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Icc]; constructor
    · rintro ⟨h, h', _⟩; exact ⟨h', h⟩
    · rintro ⟨h, h'⟩; exact ⟨h', h, h'.trans h1⟩
  simp [unifI, Measure.real, Measure.restrict_apply measurableSet_Iic, this, h0]

lemma unifI_Iic_le {a : ℝ} (h0 : 0 ≤ a) : unifI.real (Set.Iic a) ≤ a := by
  have : Set.Iic a ∩ Set.Icc (0 : ℝ) 1 ⊆ Set.Icc 0 a := by
    rintro t ⟨h, h', _⟩; exact ⟨h', h⟩
  calc unifI.real (Set.Iic a) = (volume : Measure ℝ).real (Set.Iic a ∩ Set.Icc 0 1) := by
        simp [unifI, Measure.real, Measure.restrict_apply measurableSet_Iic]
    _ ≤ (volume : Measure ℝ).real (Set.Icc 0 a) := measureReal_mono this measure_Icc_lt_top.ne
    _ = a := by simp [h0]

variable (V : Type*) [Fintype V]

/-- The distribution of the thresholds of Algorithm 1: `(T_v)_{v ∈ V}` i.i.d. uniform on
`[0, 1]`. -/
noncomputable def thresholdMeasure : Measure (V → ℝ) := Measure.pi fun _ : V => unifI

instance : IsProbabilityMeasure (thresholdMeasure V) := by
  unfold thresholdMeasure; infer_instance

variable {V}

lemma thresholdMeasure_eval_le (z : V) (a : ℝ) :
    (thresholdMeasure V).real {T | T z ≤ a} = unifI.real (Set.Iic a) := by
  have := (measurePreserving_eval (fun _ : V => unifI) z).measure_preimage
    (s := Set.Iic a) measurableSet_Iic.nullMeasurableSet
  simp only [Measure.real]
  exact congrArg ENNReal.toReal this

/-- Almost surely all thresholds lie in `[0, 1]`. -/
lemma ae_thresholds_mem :
    ∀ᵐ T ∂(thresholdMeasure V), ∀ z, T z ∈ Set.Icc (0 : ℝ) 1 := by
  rw [ae_all_iff]
  intro z
  exact (measurePreserving_eval (fun _ : V => unifI) z).quasiMeasurePreserving.ae
    (ae_restrict_mem measurableSet_Icc)

/-- **Multiplicative Chernoff lower tail** for independent threshold indicators: if `0 ≤ a_z ≤ 1`
on `s`, the number of `z ∈ s` with `T_z ≤ a_z` (a sum of independent Bernoulli(`a_z`) variables,
with mean `∑ a_z`) is at most `K` with probability at most `2^K · exp(-(∑_{z ∈ s} a_z) / 2)`.
(Proof: Markov's inequality for `2^{-X}` and `E[2^{-X}] = ∏ (1 - a_z/2) ≤ exp(-∑ a_z / 2)`.) -/
-- CSLib candidate
lemma chernoff_count (s : Finset V) (a : V → ℝ) (ha0 : ∀ z ∈ s, 0 ≤ a z)
    (ha1 : ∀ z ∈ s, a z ≤ 1) (K : ℕ) :
    (thresholdMeasure V).real {T | #(s.filter fun z => T z ≤ a z) ≤ K} ≤
      2 ^ K * Real.exp (-(∑ z ∈ s, a z) / 2) := by
  classical
  set g : V → ℝ → ℝ := fun z t => if z ∈ s then (if t ≤ a z then 1 / 2 else 1) else 1 with hg
  set F : (V → ℝ) → ℝ := fun T => ∏ z, g z (T z) with hFdef
  have hF : ∀ T, F T = (1 / 2 : ℝ) ^ #(s.filter fun z => T z ≤ a z) := by
    intro T
    simp only [hFdef, hg]
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_ite, Finset.prod_const,
      Finset.prod_const_one, mul_one]
  have hgm : ∀ z, Measurable (g z) := by
    intro z
    simp only [hg]
    split_ifs
    · exact Measurable.ite measurableSet_Iic measurable_const measurable_const
    · exact measurable_const
  have hFm : Measurable F :=
    Finset.measurable_prod _ fun z _ => (hgm z).comp (measurable_pi_apply z)
  have hF0 : ∀ T, 0 ≤ F T := fun T => by rw [hF]; positivity
  have hF1 : ∀ T, F T ≤ 1 := fun T => by rw [hF]; exact pow_le_one₀ (by norm_num) (by norm_num)
  have hFi : Integrable F (thresholdMeasure V) :=
    Integrable.of_bound hFm.aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun T => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hF0 T)]; exact hF1 T)
  have hgz : ∀ z ∈ s, ∫ t, g z t ∂unifI = 1 - a z / 2 := by
    intro z hz
    have : g z = fun t => 1 - (1 / 2 : ℝ) * (Set.Iic (a z)).indicator 1 t := by
      funext t
      simp only [hg, hz, ite_true, Set.indicator, Set.mem_Iic, Pi.one_apply]
      split_ifs <;> norm_num
    rw [this, integral_sub (integrable_const _) ((integrable_const _).indicator measurableSet_Iic
      |>.const_mul _), integral_const, integral_const_mul, integral_indicator_one measurableSet_Iic,
      unifI_Iic (ha0 z hz) (ha1 z hz)]
    simp; ring
  have hint : ∫ T, F T ∂(thresholdMeasure V) ≤ Real.exp (-(∑ z ∈ s, a z) / 2) := by
    simp only [hFdef, thresholdMeasure]
    rw [integral_fintype_prod_eq_prod g]
    have : ∀ z, ∫ t, g z t ∂unifI = if z ∈ s then 1 - a z / 2 else 1 := by
      intro z
      split_ifs with hz
      · exact hgz z hz
      · simp [hg, hz]
    simp_rw [this]
    rw [Finset.prod_ite_mem, Finset.univ_inter, neg_div, Finset.sum_div, ← Finset.sum_neg_distrib,
      Real.exp_sum]
    refine Finset.prod_le_prod₀ (fun z hz => by linarith [ha1 z hz]) fun z hz => ?_
    have := Real.add_one_le_exp (-(a z / 2))
    linarith
  have hsub : {T | #(s.filter fun z => T z ≤ a z) ≤ K} ⊆ {T | (1 / 2 : ℝ) ^ K ≤ F T} := by
    intro T hT
    simp only [Set.mem_ofPred_eq] at hT ⊢
    rw [hF]
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hT
  have hmk := mul_meas_ge_le_integral_of_nonneg (Filter.Eventually.of_forall hF0) hFi
    ((1 / 2 : ℝ) ^ K)
  have h2 : (0 : ℝ) < (1 / 2) ^ K := by positivity
  calc (thresholdMeasure V).real {T | #(s.filter fun z => T z ≤ a z) ≤ K}
      ≤ (thresholdMeasure V).real {T | (1 / 2 : ℝ) ^ K ≤ F T} := measureReal_mono hsub
    _ = 2 ^ K * ((1 / 2 : ℝ) ^ K * (thresholdMeasure V).real {T | (1 / 2 : ℝ) ^ K ≤ F T}) := by
        rw [← mul_assoc, ← mul_pow]; norm_num
    _ ≤ 2 ^ K * Real.exp (-(∑ z ∈ s, a z) / 2) := by gcongr; exact hmk.trans hint

/-! ### Per-arc analysis -/

section Arc

variable [DecidableEq V] {E : Finset (V × V)} {r : ℕ} {x : V × V → ℝ} {f : V × V → V → ℝ}
  {α : ℝ}

omit [Fintype V] [DecidableEq V] in
lemma mem_roundE {T : V → ℝ} {e : V × V} :
    e ∈ roundE E x α T ↔ e ∈ E ∧ min (T e.1) (T e.2) ≤ α * x e := by
  simp [roundE]

/-- If the threshold of the midpoint `z` of a path `P = (u, z, v)` is at most `α f_P`, then both
arcs of `P` are kept by Algorithm 1 (proof of Theorem 3.3). -/
lemma mem_mids_roundE (hE : IsLP4Feasible E r x f) (hα : 0 ≤ α) {uv : V × V} (huv : uv ∈ E)
    {T : V → ℝ} {z : V} (hz : z ∈ mids E uv.1 uv.2) (hT : T z ≤ α * f uv z) :
    z ∈ mids (roundE E x α T) uv.1 uv.2 := by
  have h1 := hE.flow_le_left huv hz
  have h2 := hE.flow_le_right huv hz
  rw [mem_mids] at hz ⊢
  refine ⟨mem_roundE.mpr ⟨hz.1, ?_⟩, mem_roundE.mpr ⟨hz.2, ?_⟩⟩
  · exact (min_le_right _ _).trans (hT.trans (mul_le_mul_of_nonneg_left h1 hα))
  · exact (min_le_left _ _).trans (hT.trans (mul_le_mul_of_nonneg_left h2 hα))

omit [DecidableEq V] in
/-- The null set of threshold vectors with some coordinate outside `[0, 1]`. -/
lemma thresholdMeasure_bad_null :
    (thresholdMeasure V).real {T | ¬ ∀ z, T z ∈ Set.Icc (0 : ℝ) 1} = 0 := by
  simp only [Measure.real, ae_iff.mp ae_thresholds_mem, ENNReal.toReal_zero]

/-- **Theorem 3.3, per-arc failure probability.** For an LP (4)-feasible `(x, f)` and inflation
`α ≥ 4`, every arc `(u, v) ∈ E` is satisfied by the output of Algorithm 1 except with probability
at most `exp(-α/4)`. -/
theorem prob_not_satisfies_le (hE : IsLP4Feasible E r x f) (hα : 4 ≤ α) {uv : V × V}
    (huv : uv ∈ E) :
    (thresholdMeasure V).real {T | ¬ Satisfies (roundE E x α T) r uv} ≤ Real.exp (-α / 4) := by
  classical
  have hα0 : 0 ≤ α := by linarith
  set μ := thresholdMeasure V
  set M := mids E uv.1 uv.2 with hM
  set S := M.filter (fun z => 1 ≤ α * f uv z) with hS
  set N : Set (V → ℝ) := {T | ¬ ∀ z, T z ∈ Set.Icc (0 : ℝ) 1}
  -- reduce to a "bad" set outside the null set `N`
  suffices H : ∃ Bad : Set (V → ℝ), μ.real Bad ≤ Real.exp (-α / 4) ∧
      ∀ T, (∀ z, T z ∈ Set.Icc (0 : ℝ) 1) → ¬ Satisfies (roundE E x α T) r uv → T ∈ Bad by
    obtain ⟨Bad, hBad, hsub⟩ := H
    calc μ.real {T | ¬ Satisfies (roundE E x α T) r uv} ≤ μ.real (N ∪ Bad) := by
          refine measureReal_mono (fun T hT => ?_)
          by_cases h : ∀ z, T z ∈ Set.Icc (0 : ℝ) 1
          · exact Or.inr (hsub T h hT)
          · exact Or.inl h
      _ ≤ μ.real N + μ.real Bad := measureReal_union_le _ _
      _ ≤ Real.exp (-α / 4) := by rw [thresholdMeasure_bad_null, zero_add]; exact hBad
  -- the paths of `S` (flow `≥ 1/α`) are kept surely
  have hSkept : ∀ T, (∀ z, T z ∈ Set.Icc (0 : ℝ) 1) → S ⊆ mids (roundE E x α T) uv.1 uv.2 := by
    intro T hT z hz
    rw [hS, Finset.mem_filter] at hz
    exact mem_mids_roundE hE hα0 huv hz.1 ((hT z).2.trans hz.2)
  by_cases hSr : r + 1 ≤ #S
  · refine ⟨∅, by simp; positivity, fun T hT hns => ?_⟩
    exact hns (Or.inr (hSr.trans (Finset.card_le_card (hSkept T hT))))
  by_cases hx : 1 / 2 ≤ x uv
  · refine ⟨∅, by simp; positivity, fun T hT hns => ?_⟩
    refine hns (Or.inl (mem_roundE.mpr ⟨huv, ?_⟩))
    calc min (T uv.1) (T uv.2) ≤ 1 := (min_le_left _ _).trans (hT _).2
      _ ≤ α * x uv := by nlinarith
  push Not at hSr hx
  set K := r - #S with hK
  have hKr : (K : ℝ) + 1 = (r : ℝ) + 1 - #S := by
    rw [hK, Nat.cast_sub (by omega)]; ring
  set a : V → ℝ := fun z => α * f uv z with ha
  refine ⟨{T | #((M \ S).filter fun z => T z ≤ a z) ≤ K}, ?_, fun T hT hns => ?_⟩
  · have hS_sub : S ⊆ M := Finset.filter_subset _ _
    have hknap := hE.knapsack uv huv S hS_sub (by omega)
    rw [← hKr] at hknap
    have hxn : 0 ≤ x uv := hE.x_nonneg uv huv
    have hsumf : ((K : ℝ) + 1) / 2 ≤ ∑ z ∈ M \ S, f uv z := by nlinarith
    have hsuma : α * (((K : ℝ) + 1) / 2) ≤ ∑ z ∈ M \ S, a z := by
      rw [ha, ← Finset.mul_sum]; exact mul_le_mul_of_nonneg_left hsumf hα0
    refine (chernoff_count (M \ S) a (fun z hz => ?_) (fun z hz => ?_) K).trans ?_
    · have := hE.f_nonneg uv huv z (Finset.mem_sdiff.mp hz).1
      exact mul_nonneg hα0 this
    · have h := (Finset.mem_sdiff.mp hz).2
      rw [hS, Finset.mem_filter, not_and, not_le] at h
      exact (h (Finset.mem_sdiff.mp hz).1).le
    · have hlog : Real.log 2 ≤ α / 4 := by
        have := Real.log_two_lt_d9; linarith
      have h2K : (2 : ℝ) ^ K = Real.exp (K * Real.log 2) := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
      rw [h2K, ← Real.exp_add, Real.exp_le_exp]
      have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      nlinarith
  · simp only [Set.mem_ofPred_eq]
    have hB : (M \ S).filter (fun z => T z ≤ a z) ⊆ mids (roundE E x α T) uv.1 uv.2 := by
      intro z hz
      rw [Finset.mem_filter, Finset.mem_sdiff] at hz
      exact mem_mids_roundE hE hα0 huv hz.1.1 hz.2
    have hdisj : Disjoint S ((M \ S).filter (fun z => T z ≤ a z)) :=
      Finset.disjoint_left.mpr fun z hzS hzB =>
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hzB).1).2 hzS
    have hcard := Finset.card_le_card (Finset.union_subset (hSkept T hT) hB)
    rw [Finset.card_union_of_disjoint hdisj] at hcard
    have hlt : #(mids (roundE E x α T) uv.1 uv.2) ≤ r := by
      by_contra h; exact hns (Or.inr (by omega))
    omega

end Arc

/-! ### Cost analysis -/

section Cost

variable {E : Finset (V × V)} {x : V × V → ℝ} {c : V × V → ℝ} {α : ℝ}

omit [Fintype V] in
lemma measurableSet_selected (e : V × V) (b : ℝ) :
    MeasurableSet {T : V → ℝ | min (T e.1) (T e.2) ≤ b} :=
  measurableSet_le ((measurable_pi_apply e.1).min (measurable_pi_apply e.2)) measurable_const

/-- Proof of Theorem 3.3: an arc `e` is selected by Algorithm 1 with probability at most
`2 α x_e`. -/
lemma prob_selected_le (e : V × V) (hb : 0 ≤ α * x e) :
    (thresholdMeasure V).real {T | min (T e.1) (T e.2) ≤ α * x e} ≤ 2 * α * x e := by
  have : {T : V → ℝ | min (T e.1) (T e.2) ≤ α * x e} =
      {T | T e.1 ≤ α * x e} ∪ {T | T e.2 ≤ α * x e} := by
    ext T; simp [min_le_iff]
  rw [this]
  refine (measureReal_union_le _ _).trans ?_
  rw [thresholdMeasure_eval_le, thresholdMeasure_eval_le]
  have := unifI_Iic_le hb
  linarith

omit [Fintype V] in
lemma cost_roundE_eq [DecidableEq V] (T : V → ℝ) :
    cost c (roundE E x α T) =
      ∑ e ∈ E, {T : V → ℝ | min (T e.1) (T e.2) ≤ α * x e}.indicator (fun _ => c e) T := by
  simp only [cost, roundE, Finset.sum_filter, Set.indicator_apply, Set.mem_ofPred_eq]

lemma integrable_cost_roundE [DecidableEq V] :
    Integrable (fun T => cost c (roundE E x α T)) (thresholdMeasure V) := by
  simp_rw [cost_roundE_eq]
  exact integrable_finsetSum _ fun e _ =>
    (integrable_const (c e)).indicator (measurableSet_selected e _)

omit [Fintype V] in
lemma cost_roundE_nonneg [DecidableEq V] (hc : ∀ e ∈ E, 0 ≤ c e) (T : V → ℝ) :
    0 ≤ cost c (roundE E x α T) :=
  Finset.sum_nonneg fun e he => hc e (Finset.mem_filter.mp he).1

omit [Fintype V] in
lemma lpValue_nonneg (hc : ∀ e ∈ E, 0 ≤ c e) (hx : ∀ e ∈ E, 0 ≤ x e) : 0 ≤ lpValue c E x :=
  Finset.sum_nonneg fun e he => mul_nonneg (hc e he) (hx e he)

/-- **Theorem 3.3, expected cost.** With nonnegative costs and `x ≥ 0`, the expected cost of the
output of Algorithm 1 is at most `2 α ∑_e c_e x_e`. -/
theorem expected_cost_le [DecidableEq V] (hc : ∀ e ∈ E, 0 ≤ c e) (hx : ∀ e ∈ E, 0 ≤ x e)
    (hα : 0 ≤ α) :
    ∫ T, cost c (roundE E x α T) ∂(thresholdMeasure V) ≤ 2 * α * lpValue c E x := by
  simp_rw [cost_roundE_eq]
  rw [integral_finsetSum _ fun e _ =>
    (integrable_const (c e)).indicator (measurableSet_selected e _), lpValue, Finset.mul_sum]
  refine Finset.sum_le_sum fun e he => ?_
  rw [integral_indicator_const _ (measurableSet_selected e _), smul_eq_mul]
  have := prob_selected_le (V := V) e (mul_nonneg hα (hx e he))
  have hce := hc e he
  calc (thresholdMeasure V).real {T | min (T e.1) (T e.2) ≤ α * x e} * c e
      ≤ 2 * α * x e * c e := mul_le_mul_of_nonneg_right this hce
    _ = 2 * α * (c e * x e) := by ring

/-- **Theorem 3.3, cost tail** (Markov's inequality): the cost of the output of Algorithm 1
exceeds `6 α ∑_e c_e x_e` with probability at most `1/3`. -/
theorem prob_cost_gt_le [DecidableEq V] (hc : ∀ e ∈ E, 0 ≤ c e) (hx : ∀ e ∈ E, 0 ≤ x e)
    (hα : 0 < α) :
    (thresholdMeasure V).real {T | 6 * α * lpValue c E x < cost c (roundE E x α T)} ≤ 1 / 3 := by
  set μ := thresholdMeasure V
  have hL := lpValue_nonneg hc hx
  have hexp := expected_cost_le hc hx hα.le
  rcases hL.lt_or_eq with hL | hL
  · have hmk := mul_meas_ge_le_integral_of_nonneg
      (Filter.Eventually.of_forall (cost_roundE_nonneg (x := x) (α := α) hc))
      integrable_cost_roundE (6 * α * lpValue c E x)
    have hmono : μ.real {T | 6 * α * lpValue c E x < cost c (roundE E x α T)} ≤
        μ.real {T | 6 * α * lpValue c E x ≤ cost c (roundE E x α T)} :=
      measureReal_mono fun T hT => by
        simp only [Set.mem_ofPred_eq] at hT ⊢; exact hT.le
    have hpos : 0 < 6 * α * lpValue c E x := by positivity
    have : 6 * α * lpValue c E x * μ.real {T | 6 * α * lpValue c E x ≤ cost c (roundE E x α T)}
        ≤ 6 * α * lpValue c E x * (1 / 3) := by linarith
    exact hmono.trans (le_of_mul_le_mul_left this hpos)
  · rw [← hL, mul_zero] at hexp ⊢
    have h0 : (fun T => cost c (roundE E x α T)) =ᵐ[μ] 0 :=
      (integral_eq_zero_iff_of_nonneg (cost_roundE_nonneg hc) integrable_cost_roundE).mp
        (le_antisymm hexp (integral_nonneg (cost_roundE_nonneg hc)))
    have hnull : μ {T | 0 < cost c (roundE E x α T)} = 0 := by
      refine measure_mono_null (fun T hT => ?_) (ae_iff.mp h0)
      simp only [Set.mem_ofPred_eq, Pi.zero_apply] at hT ⊢
      exact hT.ne'
    simp [Measure.real, hnull]

end Cost

/-! ### Theorem 3.3 -/

section Main

variable [DecidableEq V] {E : Finset (V × V)} {r : ℕ} {x : V × V → ℝ} {f : V × V → V → ℝ}
  {c : V × V → ℝ} {α : ℝ}

/-- **Theorem 3.3 (analysis of Algorithm 1).** Let `(x, f)` be feasible for LP (4), costs
`c ≥ 0` and inflation `α ≥ 4`. With thresholds `T_v` i.i.d. uniform on `[0, 1]`, the output
`E' = roundE E x α T` of Algorithm 1 satisfies every arc of `E` (hence, by Lemma 3.1, is an
`r`-fault-tolerant 2-spanner) and has cost at most `6 α ∑_e c_e x_e`, with probability at least
`2/3 - |E| · exp(-α/4)`. -/
theorem rounding_success (hE : IsLP4Feasible E r x f) (hc : ∀ e ∈ E, 0 ≤ c e) (hα : 4 ≤ α) :
    2 / 3 - #E * Real.exp (-α / 4) ≤
      (thresholdMeasure V).real {T | (∀ uv ∈ E, Satisfies (roundE E x α T) r uv) ∧
        cost c (roundE E x α T) ≤ 6 * α * lpValue c E x} := by
  set μ := thresholdMeasure V
  set G := {T : V → ℝ | (∀ uv ∈ E, Satisfies (roundE E x α T) r uv) ∧
        cost c (roundE E x α T) ≤ 6 * α * lpValue c E x}
  have hsub : Gᶜ ⊆ (⋃ uv ∈ E, {T | ¬ Satisfies (roundE E x α T) r uv}) ∪
      {T | 6 * α * lpValue c E x < cost c (roundE E x α T)} := by
    intro T hT
    simp only [G, Set.mem_compl_iff, Set.mem_ofPred_eq, not_and_or, not_forall, not_le] at hT
    rcases hT with ⟨uv, huv, h⟩ | h
    · exact Or.inl (Set.mem_biUnion huv h)
    · exact Or.inr h
  have h1 : μ.real Gᶜ ≤ #E * Real.exp (-α / 4) + 1 / 3 := by
    refine (measureReal_mono hsub).trans ((measureReal_union_le _ _).trans (add_le_add ?_ ?_))
    · refine (measureReal_biUnion_finset_le _ _).trans ?_
      refine (Finset.sum_le_sum fun uv huv => prob_not_satisfies_le hE hα huv).trans ?_
      simp
    · exact prob_cost_gt_le hc hE.x_nonneg (by linarith)
  have h2 : (1 : ℝ) ≤ μ.real G + μ.real Gᶜ := by
    have := measureReal_union_le (μ := μ) G Gᶜ
    rwa [Set.union_compl_self, probReal_univ] at this
  linarith

/-- **Theorem 3.3 with `α = 12 ln n`** (`n = |V| ≥ 2`): with probability at least `2/3 - 1/n`,
Algorithm 1 outputs an arc set that satisfies every arc of `E` (an `r`-fault-tolerant 2-spanner, by
Lemma 3.1) of cost at most `72 ln n · ∑_e c_e x_e`, i.e. an `O(log n)`-approximation of the LP
value. -/
theorem rounding_success_log (hE : IsLP4Feasible E r x f) (hc : ∀ e ∈ E, 0 ≤ c e)
    (hn : 2 ≤ Fintype.card V) :
    2 / 3 - 1 / (Fintype.card V : ℝ) ≤
      (thresholdMeasure V).real {T |
        (∀ uv ∈ E, Satisfies (roundE E x (12 * Real.log (Fintype.card V)) T) r uv) ∧
        cost c (roundE E x (12 * Real.log (Fintype.card V)) T) ≤
          72 * Real.log (Fintype.card V) * lpValue c E x} := by
  set n := Fintype.card V with hn_def
  have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hlog : (1 / 3 : ℝ) ≤ Real.log n := by
    have h2 : Real.log 2 ≤ Real.log n := Real.log_le_log (by norm_num) hn'
    have := Real.log_two_gt_d9
    linarith
  have hα : (4 : ℝ) ≤ 12 * Real.log n := by linarith
  have key := rounding_success (c := c) hE hc hα
  have h72 : 6 * (12 * Real.log n) = 72 * Real.log n := by ring
  simp only [h72] at key
  refine le_trans ?_ key
  have hE2 : (#E : ℝ) ≤ (n : ℝ) ^ 2 := by
    have : #E ≤ n ^ 2 := by
      calc #E ≤ #(Finset.univ : Finset (V × V)) := Finset.card_le_univ E
        _ = n ^ 2 := by rw [Finset.card_univ, Fintype.card_prod, sq]
    exact_mod_cast this
  have hexp : Real.exp (-(12 * Real.log n) / 4) = 1 / (n : ℝ) ^ 3 := by
    rw [show -(12 * Real.log n) / 4 = -((3 : ℕ) * Real.log n) by push_cast; ring,
      Real.exp_neg, Real.exp_nat_mul, Real.exp_log hn0, one_div]
  rw [hexp]
  have : (#E : ℝ) * (1 / (n : ℝ) ^ 3) ≤ 1 / n := by
    rw [mul_one_div, div_le_div_iff₀ (by positivity) hn0]
    nlinarith
  linarith

end Main

end DinitzKrauthgamer
