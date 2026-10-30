import Mathlib

/-!
# Lemma 2 of Boppana–Halldórsson–Rawitz (PODC 2018): success probability of `Max`

Weighted algorithm `Max`: every node `v` draws `x_v` uniformly from `[0,1]`, independently,
computes `r_v = x_v ^ (1 / w_v)` and joins the output iff `r_v > r_u` for all neighbours `u`.

* `lemma2`: `P[v ∈ Max] = w(v) / w(N[v])`.
* `expected_weight_max`: eq. (7) with `S = V`, `E[w(Max)] = ∑_v w(v)² / w(N[v])`.
* `maxSet_isIndepSet`: the output of `Max` is always an independent set.
-/

namespace Podc.LocalISApproximation

open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
  (w : V → ℝ)

/-- The uniform distribution on `[0,1]`. -/
noncomputable abbrev unif01 : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) 1)

instance : IsProbabilityMeasure unif01 := ⟨by simp [Real.volume_Icc]⟩

/-- Product of independent uniform `[0,1]` distributions, one per node. -/
noncomputable def unifCube : Measure (V → ℝ) := Measure.pi fun _ => unif01

instance : IsProbabilityMeasure (unifCube (V := V)) := by
  unfold unifCube; infer_instance

/-- The output of the algorithm `Max` on the random draws `x`. -/
noncomputable def maxSet (x : V → ℝ) : Finset V :=
  Finset.univ.filter fun v => ∀ u, G.Adj v u → x u ^ (1 / w u) < x v ^ (1 / w v)

omit [DecidableEq V] in
/-- The output of `Max` is an independent set (for every draw). -/
theorem maxSet_isIndepSet (x : V → ℝ) : G.IsIndepSet (maxSet G w x : Set V) := by
  intro a ha b hb _ hab
  simp only [maxSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at ha hb
  exact lt_asymm (ha b hab) (hb a hab.symm)

/-- One coordinate: `P[x^(1/w) < c] = c^w` for `x` uniform on `[0,1]`, `c ∈ [0,1]`. -/
lemma unif01_rpow_lt {a c : ℝ} (ha : 0 < a) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    unif01 {y : ℝ | y ^ (1 / a) < c} = ENNReal.ofReal (c ^ a) := by
  have hca0 : 0 ≤ c ^ a := Real.rpow_nonneg hc0 a
  have hca1 : c ^ a ≤ 1 := Real.rpow_le_one hc0 hc1 ha.le
  have hmeas : MeasurableSet {y : ℝ | y ^ (1 / a) < c} :=
    measurableSet_lt (by fun_prop) measurable_const
  rw [unif01, Measure.restrict_apply hmeas]
  have : {y : ℝ | y ^ (1 / a) < c} ∩ Set.Icc 0 1 = Set.Ico 0 (c ^ a) := by
    ext y
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_Icc, Set.mem_Ico, one_div]
    constructor
    · rintro ⟨h, hy0, -⟩
      exact ⟨hy0, (Real.rpow_inv_lt_iff_of_pos hy0 hc0 ha).1 h⟩
    · rintro ⟨hy0, h⟩
      exact ⟨(Real.rpow_inv_lt_iff_of_pos hy0 hc0 ha).2 h, hy0, h.le.trans hca1⟩
  rw [this, Real.volume_Ico, sub_zero]

variable {G w}

omit [DecidableEq V] in
/-- The event `v ∈ Max` is measurable. -/
lemma measurableSet_mem_maxSet (v : V) : MeasurableSet {x : V → ℝ | v ∈ maxSet G w x} := by
  have : {x : V → ℝ | v ∈ maxSet G w x} =
      ⋂ u ∈ G.neighborFinset v, {x : V → ℝ | x u ^ (1 / w u) < x v ^ (1 / w v)} := by
    ext x; simp [maxSet]
  rw [this]
  exact Finset.measurableSet_biInter _ fun u _ => measurableSet_lt (by fun_prop) (by fun_prop)

/-- The inner (conditional) probability: given `x_v = t`, all neighbours `u` of `v` satisfy
`r_u < t^(1/w_v)` with probability `∏_u t^(w_u/w_v) = t^(w(N(v))/w_v)`. -/
lemma inner_prob (hw : ∀ v, 0 < w v) (v : V) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    Measure.pi (fun _ : (Finset.univ.erase v : Finset V) => unif01)
      (Set.univ.pi fun i => {a : ℝ | G.Adj v i → a ^ (1 / w i) < t ^ (1 / w v)}) =
      ENNReal.ofReal (t ^ (1 / w v * ∑ u ∈ G.neighborFinset v, w u)) := by
  have hc0 : 0 ≤ t ^ (1 / w v) := Real.rpow_nonneg ht.1 _
  have hc1 : t ^ (1 / w v) ≤ 1 := Real.rpow_le_one ht.1 ht.2 (by have := hw v; positivity)
  rw [Measure.pi_pi]
  have hterm : ∀ i : V, unif01 {a : ℝ | G.Adj v i → a ^ (1 / w i) < t ^ (1 / w v)} =
      if G.Adj v i then ENNReal.ofReal ((t ^ (1 / w v)) ^ w i) else 1 := by
    intro i
    split_ifs with h
    · simpa [h] using unif01_rpow_lt (hw i) hc0 hc1
    · simp [h]
  rw [Finset.prod_coe_sort (Finset.univ.erase v)
    (fun i => unif01 {a : ℝ | G.Adj v i → a ^ (1 / w i) < t ^ (1 / w v)})]
  simp_rw [hterm]
  rw [← Finset.prod_filter]
  have hN : (Finset.univ.erase v).filter (G.Adj v) = G.neighborFinset v := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, and_true,
      SimpleGraph.mem_neighborFinset]
    exact ⟨fun h => h.2, fun h => ⟨h.ne.symm, h⟩⟩
  rw [hN, ← ENNReal.ofReal_prod_of_nonneg (fun i _ => Real.rpow_nonneg hc0 _),
    ← Real.rpow_sum_of_nonneg hc0 (fun i _ => (hw i).le), ← Real.rpow_mul ht.1]

/-- **Lemma 2** of [Boppana–Halldórsson–Rawitz, PODC 2018]: in the weighted algorithm `Max`,
`P[v ∈ Max] = w(v) / w(N[v])`, where `w(N[v]) = w(v) + ∑_{u ∈ N(v)} w(u)`. -/
theorem lemma2 (hw : ∀ v, 0 < w v) (v : V) :
    unifCube {x | v ∈ maxSet G w x} =
      ENNReal.ofReal (w v / (w v + ∑ u ∈ G.neighborFinset v, w u)) := by
  set W := ∑ u ∈ G.neighborFinset v, w u with hW
  have hW0 : 0 ≤ W := Finset.sum_nonneg fun u _ => (hw u).le
  have hwv := hw v
  set E := {x : V → ℝ | v ∈ maxSet G w x} with hE
  have hEm : MeasurableSet E := measurableSet_mem_maxSet v
  set s : Finset V := Finset.univ.erase v
  rw [← lintegral_indicator_one hEm, unifCube, lintegral_eq_lmarginal_univ (0 : V → ℝ),
    ← Finset.insert_erase (Finset.mem_univ v),
    lmarginal_insert _ (measurable_one.indicator hEm) (Finset.notMem_erase v _)]
  have hinner : Set.EqOn (fun t => (∫⋯∫⁻_s, E.indicator 1 ∂fun _ => unif01)
      (Function.update (0 : V → ℝ) v t)) (fun t => ENNReal.ofReal (t ^ (1 / w v * W)))
      (Set.Icc 0 1) := by
    intro t ht
    simp only [lmarginal]
    rw [← inner_prob hw v ht, ← lintegral_indicator_one
      (MeasurableSet.univ_pi fun i => ?_)]
    · congr 1
      funext z
      simp only [Set.indicator, Pi.one_apply]
      congr 1
      apply propext
      simp only [hE, maxSet, Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq,
        Set.mem_pi, Set.mem_univ, forall_const, Function.updateFinset_def, s,
        Finset.notMem_erase, dite_false, Function.update_self]
      constructor
      · intro h i hi
        have := h i hi
        rwa [dite_eq_left
          (Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase i.2, Finset.mem_univ _⟩)] at this
      · intro h u hu
        rw [dite_eq_left (Finset.mem_erase.2 ⟨hu.ne.symm, Finset.mem_univ _⟩)]
        exact h ⟨u, Finset.mem_erase.2 ⟨hu.ne.symm, Finset.mem_univ _⟩⟩ hu
    · by_cases h : G.Adj v i
      · simpa [h] using measurableSet_lt (by fun_prop) measurable_const
      · simp [h]
  rw [unif01, setLIntegral_congr_fun measurableSet_Icc hinner]
  have hint : IntegrableOn (fun t : ℝ => t ^ (1 / w v * W)) (Set.Icc 0 1) :=
    (Real.continuous_rpow_const (by positivity)).continuousOn.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hint
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall
      fun t ht => Real.rpow_nonneg ht.1 _)),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le zero_le_one,
    integral_rpow (Or.inl (by linarith [show 0 ≤ 1 / w v * W by positivity]))]
  congr 1
  rw [Real.one_rpow, Real.zero_rpow (by positivity)]
  field_simp
  ring

/-- Eq. (7) of [Boppana–Halldórsson–Rawitz, PODC 2018] with `S = V` (linearity of expectation):
the expected weight of the output of `Max` is `∑_v w(v)² / w(N[v])`. -/
theorem expected_weight_max (hw : ∀ v, 0 < w v) :
    ∫ x, (∑ v ∈ maxSet G w x, w v) ∂unifCube =
      ∑ v, w v ^ 2 / (w v + ∑ u ∈ G.neighborFinset v, w u) := by
  have h : ∀ x : V → ℝ, ∑ v ∈ maxSet G w x, w v =
      ∑ v, {x : V → ℝ | v ∈ maxSet G w x}.indicator (fun _ => w v) x := by
    intro x
    rw [maxSet, Finset.sum_filter]
    simp [Set.indicator, maxSet]
  simp_rw [h]
  rw [integral_finsetSum _ fun v _ =>
    (integrable_const (w v)).indicator (measurableSet_mem_maxSet v)]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [integral_indicator_const _ (measurableSet_mem_maxSet v), smul_eq_mul, measureReal_def,
    lemma2 hw, ENNReal.toReal_ofReal (div_nonneg (hw v).le
      (add_nonneg (hw v).le (Finset.sum_nonneg fun u _ => (hw u).le)))]
  ring

end Podc.LocalISApproximation
