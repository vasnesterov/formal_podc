import Papers.PODC2016.GreedySpanner.Section4
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Section 4 (continued): doubling metrics, Observation 7 and Theorem 6

* `IsMetricW w` — `w` is a metric on `V`, viewed as the complete weighted graph `(V, ⊤, w)`.
* `IsDoubling w D` — every closed ball `B(x, r)` is covered by at most `2^D` balls of radius `r/2`
  (doubling dimension `≤ D`); `metricFamily V D` = `M(n, D)` for `n = |V|`.
* `observation7` — a `t`-spanner `H` (`t ≤ 2`) of a metric in `M(n, D)` induces a metric
  `M_H ∈ M(n, 2D)`.
* `mstWeight_inducedW` — `M` and `M_H` have the same MST weight (Observations 2 and 4).
* `theorem6` — **Theorem 6**: for `M ∈ M(n, D)` and `1 ≤ t < 2`, the greedy `t`-spanner of `M` has at
  most `OPT_t^sparse(M(n, 2D))` edges and lightness at most `OPT_t^light(M(n, 2D))`.
* `corollary3_of_forall_exists` — Corollary 3 with the cited Theorem 4 [Got15] as a hypothesis.
-/

open Finset SimpleGraph
open scoped ENNReal NNReal

namespace GreedySpanner

variable {V : Type*} {H : SimpleGraph V} {w : Sym2 V → ℝ≥0} {t : ℝ≥0}

-- CSLib candidate
/-- `w` is a metric on `V`: `d(x, y) = w({x, y})`. -/
def IsMetricW (w : Sym2 V → ℝ≥0) : Prop :=
  (∀ x, w s(x, x) = 0) ∧ (∀ x y, x ≠ y → 0 < w s(x, y)) ∧
    ∀ x y z, w s(x, z) ≤ w s(x, y) + w s(y, z)

lemma IsMetricW.le_wlength (hw : IsMetricW w) {K : SimpleGraph V} {x y : V} (p : K.Walk x y) :
    (w s(x, y) : ℝ≥0∞) ≤ p.wlength w := by
  induction p with
  | nil => simp [hw.1]
  | @cons a b c hab q ih =>
    rw [Walk.wlength_cons]
    calc (w s(a, c) : ℝ≥0∞) ≤ w s(a, b) + w s(b, c) := by exact_mod_cast hw.2.2 a b c
      _ ≤ _ := add_le_add le_rfl ih

lemma IsMetricW.le_wdist (hw : IsMetricW w) {K : SimpleGraph V} {x y : V} :
    (w s(x, y) : ℝ≥0∞) ≤ K.wdist w x y :=
  le_iInf fun p => hw.le_wlength p

lemma IsMetricW.top_wdist (hw : IsMetricW w) (x y : V) :
    (⊤ : SimpleGraph V).wdist w x y = w s(x, y) := by
  refine le_antisymm ?_ hw.le_wdist
  by_cases hxy : x = y
  · subst hxy
    exact (wdist_le (Walk.nil : (⊤ : SimpleGraph V).Walk x x)).trans (by simp)
  · exact top_wdist_le hxy

lemma top_reachable (x y : V) : (⊤ : SimpleGraph V).Reachable x y := by
  by_cases h : x = y
  · subst h; rfl
  · exact ((top_adj x y).mpr h).reachable

lemma mem_edgeSet_top {e : Sym2 V} : e ∈ (⊤ : SimpleGraph V).edgeSet ↔ ¬ e.IsDiag := by
  induction e using Sym2.ind with
  | _ x y => simp

/-! ### The induced metric of a spanner of a metric -/

lemma reachable_of_spanner_top (hH : IsWSpanner ⊤ H w t) (x y : V) : H.Reachable x y :=
  hH.reachable (top_reachable x y)

section Induced

variable (hw : IsMetricW w) (hH : IsWSpanner ⊤ H w t)
include hw hH

lemma le_inducedW (e : Sym2 V) : w e ≤ inducedW H w e := by
  induction e using Sym2.ind with
  | _ x y =>
  have := coe_inducedW (w := w) (reachable_of_spanner_top hH x y)
  have h2 : (w s(x, y) : ℝ≥0∞) ≤ inducedW H w s(x, y) := this ▸ hw.le_wdist
  exact_mod_cast h2

lemma inducedW_le (e : Sym2 V) : inducedW H w e ≤ t * w e := by
  induction e using Sym2.ind with
  | _ x y =>
  have h1 := coe_inducedW (w := w) (reachable_of_spanner_top hH x y)
  have h2 : (inducedW H w s(x, y) : ℝ≥0∞) ≤ t * w s(x, y) := by
    rw [h1, ← hw.top_wdist x y]; exact hH.2 x y
  exact_mod_cast h2

lemma inducedW_eq_of_mem {e : Sym2 V} (he : e ∈ H.edgeSet) : inducedW H w e = w e := by
  induction e using Sym2.ind with
  | _ x y =>
  refine le_antisymm ?_ (le_inducedW hw hH _)
  have h1 := coe_inducedW (w := w) (reachable_of_spanner_top hH x y)
  have h2 : (inducedW H w s(x, y) : ℝ≥0∞) ≤ w s(x, y) := h1 ▸ wdist_le_of_adj he
  exact_mod_cast h2

/-- The metric `M_H` induced by a spanner of a metric is a metric. -/
lemma isMetricW_inducedW : IsMetricW (inducedW H w) := by
  refine ⟨fun x => ?_, fun x y hxy => (hw.2.1 x y hxy).trans_le (le_inducedW hw hH _), ?_⟩
  · have h1 := coe_inducedW (w := w) (reachable_of_spanner_top hH x x)
    have h0 : H.wdist w x x = 0 :=
      le_antisymm ((wdist_le (Walk.nil : H.Walk x x)).trans (by simp)) zero_le
    rw [h0] at h1
    exact_mod_cast h1
  · intro x y z
    have hc := fun a b => coe_inducedW (w := w) (reachable_of_spanner_top hH a b)
    have : (inducedW H w s(x, z) : ℝ≥0∞) ≤ inducedW H w s(x, y) + inducedW H w s(y, z) := by
      rw [hc, hc, hc]; exact wdist_triangle
    exact_mod_cast this

end Induced

/-! ### Doubling dimension and Observation 7 -/

/-- The closed ball `B(x, r)` of the metric `w`. -/
def ball (w : Sym2 V → ℝ≥0) (x : V) (r : ℝ≥0) : Set V := {y | w s(x, y) ≤ r}

-- CSLib candidate
/-- The metric `w` has doubling dimension at most `D`: every ball of radius `r` is covered by at
most `2^D` balls of radius `r/2`. -/
def IsDoubling (w : Sym2 V → ℝ≥0) (D : ℝ) : Prop :=
  ∀ x (r : ℝ≥0), ∃ C : Finset V, (#C : ℝ) ≤ (2 : ℝ) ^ D ∧ ball w x r ⊆ ⋃ c ∈ C, ball w c (r / 2)

variable (V) in
/-- `M(n, D)`: the metrics on the `n`-point set `V` with doubling dimension at most `D`. -/
def metricFamily (D : ℝ) : Set (Sym2 V → ℝ≥0) := {w | IsMetricW w ∧ IsDoubling w D}

/-- **Observation 7.** If `H` is a `t`-spanner of a metric `M ∈ M(n, D)` and `t ≤ 2`, then the
metric `M_H` induced by `H` belongs to `M(n, 2D)`. -/
theorem observation7 {D : ℝ} (hw : IsMetricW w) (hD : IsDoubling w D) (hH : IsWSpanner ⊤ H w t)
    (ht2 : t ≤ 2) : inducedW H w ∈ metricFamily V (2 * D) := by
  classical
  refine ⟨isMetricW_inducedW hw hH, fun x r => ?_⟩
  obtain ⟨C, hCcard, hCcov⟩ := hD x r
  choose C' hC'card hC'cov using fun c => hD c (r / 2)
  refine ⟨C.biUnion C', ?_, ?_⟩
  · calc (#(C.biUnion C') : ℝ) ≤ ∑ c ∈ C, (#(C' c) : ℝ) := by exact_mod_cast card_biUnion_le
      _ ≤ ∑ _c ∈ C, (2 : ℝ) ^ D := Finset.sum_le_sum fun c _ => hC'card c
      _ = #C * (2 : ℝ) ^ D := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (2 : ℝ) ^ D * (2 : ℝ) ^ D := by gcongr
      _ = (2 : ℝ) ^ (2 * D) := by rw [← Real.rpow_add two_pos, two_mul]
  · intro y hy
    -- `B_{M_H}(x, r) ⊆ B_M(x, r)`
    have hy' : y ∈ ball w x r := (le_inducedW hw hH _).trans hy
    obtain ⟨c, hc, hyc⟩ := Set.mem_iUnion₂.mp (hCcov hy')
    obtain ⟨c', hc', hyc'⟩ := Set.mem_iUnion₂.mp (hC'cov c hyc)
    refine Set.mem_iUnion₂.mpr ⟨c', Finset.mem_biUnion.mpr ⟨c, hc, hc'⟩, ?_⟩
    -- `B_M(c', r/4) ⊆ B_{M_H}(c', t r/4) ⊆ B_{M_H}(c', r/2)`
    calc inducedW H w s(c', y) ≤ t * w s(c', y) := inducedW_le hw hH _
      _ ≤ 2 * (r / 2 / 2) := mul_le_mul' ht2 hyc'
      _ = r / 2 := by rw [mul_div_cancel₀ _ two_ne_zero]

/-! ### Theorem 6 -/

variable (V) in
/-- `OPT_t^sparse(M(n, D))`. -/
noncomputable def metricOptSparse (D : ℝ) (t : ℝ≥0) : ℕ∞ :=
  ⨆ w' ∈ metricFamily V D, optSparse ⊤ w' t

variable (V) in
/-- `OPT_t^light(M(n, D))`. -/
noncomputable def metricOptLight [Fintype V] (D : ℝ) (t : ℝ≥0) : ℝ≥0∞ :=
  ⨆ w' ∈ metricFamily V D, optLight ⊤ w' t

lemma wt_le_wt_of_le [Fintype V] {w₁ w₂ : Sym2 V → ℝ≥0} {T : SimpleGraph V}
    (h : ∀ e ∈ T.edgeSet, w₁ e ≤ w₂ e) : wt w₁ T ≤ wt w₂ T := by
  refine Finset.sum_le_sum fun e _ => ?_
  by_cases he : e ∈ T.edgeSet
  · simp only [Set.indicator_of_mem he]; exact_mod_cast h e he
  · simp [Set.indicator_of_notMem he]

/-- Observations 2 and 4: a metric `M` and the metric `M_H` induced by its greedy spanner have the
same MST weight. -/
theorem mstWeight_inducedW [Fintype V] (hw : IsMetricW w) (ht : 1 ≤ t)
    (hH : IsGreedySpanner ⊤ w t H) : mstWeight ⊤ (inducedW H w) = mstWeight ⊤ w := by
  have hsp := hH.isWSpanner ht
  refine le_antisymm ?_ (le_iInf₂ fun T hT =>
    (mstWeight_le_wt hT).trans (wt_le_wt_of_le fun e _ => le_inducedW hw hsp e))
  obtain ⟨Z, hZH, hZ, hZw⟩ := hH.exists_mst_le
  calc mstWeight ⊤ (inducedW H w) ≤ wt (inducedW H w) Z := mstWeight_le_wt hZ
    _ ≤ wt w Z := wt_le_wt_of_le fun e he => (inducedW_eq_of_mem hw hsp (edgeSet_mono hZH he)).le
    _ = mstWeight ⊤ w := hZw

/-- **Theorem 6** of Filtser–Solomon (*greedy is near-optimal in doubling metrics*). For every metric
`M ∈ M(n, D)` and every stretch `1 ≤ t < 2`, the greedy `t`-spanner `H` of `M` has at most
`OPT_t^sparse(M(n, 2D))` edges and lightness at most `OPT_t^light(M(n, 2D))`. -/
theorem theorem6 [Fintype V] [DecidableEq V] {D : ℝ} (hw : IsMetricW w) (hD : IsDoubling w D)
    (ht : 1 ≤ t) (ht2 : t < 2) (hH : IsGreedySpanner ⊤ w t H) :
    (H.edgeSet.ncard : ℕ∞) ≤ metricOptSparse V (2 * D) t ∧
      lightness ⊤ w H ≤ metricOptLight V (2 * D) t := by
  have hsp := hH.isWSpanner ht
  have hmem := observation7 hw hD hsp ht2.le
  have hpos : ∀ e ∈ (⊤ : SimpleGraph V).edgeSet, 0 < w e := by
    intro e he
    induction e using Sym2.ind with
    | _ x y => exact hw.2.1 x y ((top_adj x y).mp he)
  refine ⟨le_iSup₂_of_le _ hmem (le_iInf₂ fun H' hH' => ?_),
    le_iSup₂_of_le _ hmem (le_iInf₂ fun H' hH' => ?_)⟩
  · exact_mod_cast lemma6 top_reachable hpos ht ht2 hH hH'
  · unfold lightness
    rw [mstWeight_inducedW hw ht hH]
    exact ENNReal.div_le_div_right (lemma5 top_reachable ht hH hH') _

/-- **Corollary 3** (with the cited existential bound, e.g. Theorem 4 of [Got15], as a hypothesis):
if every metric of `M(n, 2D)` has a `t`-spanner with at most `m` edges and lightness at most `ℓ`,
then so does the greedy `t`-spanner of every metric of `M(n, D)`. -/
theorem corollary3_of_forall_exists [Fintype V] [DecidableEq V] {D : ℝ} {m : ℕ} {ℓ : ℝ≥0∞}
    (hex : ∀ w' ∈ metricFamily V (2 * D), ∃ H', IsWSpanner ⊤ H' w' t ∧
      H'.edgeSet.ncard ≤ m ∧ lightness ⊤ w' H' ≤ ℓ)
    (hw : IsMetricW w) (hD : IsDoubling w D) (ht : 1 ≤ t) (ht2 : t < 2)
    (hH : IsGreedySpanner ⊤ w t H) : H.edgeSet.ncard ≤ m ∧ lightness ⊤ w H ≤ ℓ := by
  obtain ⟨h1, h2⟩ := theorem6 hw hD ht ht2 hH
  refine ⟨?_, h2.trans (iSup₂_le fun w' hw' => ?_)⟩
  · have : metricOptSparse V (2 * D) t ≤ m := iSup₂_le fun w' hw' => by
      obtain ⟨H', hH', hm, -⟩ := hex w' hw'
      exact (optSparse_le hH').trans (by exact_mod_cast hm)
    exact_mod_cast h1.trans this
  · obtain ⟨H', hH', -, hl⟩ := hex w' hw'
    exact (optLight_le hH').trans hl

/-! ### Non-vacuity of Theorem 6 -/

/-- Every metric on `n ≥ 1` points has doubling dimension at most `log₂ n`. -/
lemma isDoubling_logb_card [Fintype V] [Nonempty V] (hw : IsMetricW w) :
    IsDoubling w (Real.logb 2 (Fintype.card V)) := by
  classical
  intro x r
  refine ⟨univ, ?_, fun y _ => Set.mem_iUnion₂.mpr ⟨y, mem_univ y, ?_⟩⟩
  · rw [card_univ, Real.rpow_logb two_pos (by norm_num) (by exact_mod_cast Fintype.card_pos)]
  · change w s(y, y) ≤ r / 2
    rw [hw.1]
    exact zero_le

variable (V) in
/-- The uniform metric (all distances `1`). -/
noncomputable def uniformW : Sym2 V → ℝ≥0 :=
  open Classical in fun e => if e.IsDiag then 0 else 1

lemma isMetricW_uniformW : IsMetricW (uniformW V) := by
  classical
  refine ⟨fun x => by simp [uniformW], fun x y hxy => by simp [uniformW, hxy], fun x y z => ?_⟩
  by_cases hxz : x = z
  · subst hxz; simp [uniformW]
  · by_cases hxy : x = y
    · subst hxy; simp [uniformW]
    · simp only [uniformW, Sym2.mk_isDiag_iff, hxy, ite_false]
      split_ifs <;> simp

/-- The hypotheses of Theorem 6 are satisfiable: the uniform metric lies in `M(n, log₂ n)` and has a
greedy `t`-spanner. -/
example [Fintype V] [Nonempty V] (t : ℝ≥0) :
    uniformW V ∈ metricFamily V (Real.logb 2 (Fintype.card V)) ∧
      ∃ H, IsGreedySpanner ⊤ (uniformW V) t H :=
  ⟨⟨isMetricW_uniformW, isDoubling_logb_card isMetricW_uniformW⟩, exists_isGreedySpanner _ _ _⟩

end GreedySpanner
