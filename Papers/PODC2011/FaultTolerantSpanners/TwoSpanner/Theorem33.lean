import Papers.PODC2011.FaultTolerantSpanners.TwoSpanner.Characterization
import Papers.PODC2011.FaultTolerantSpanners.TwoSpanner.Rounding

/-!
# Theorem 3.3 of Dinitz–Krauthgamer (PODC'11): `O(log n)`-approximation for Minimum Cost
`r`-Fault Tolerant 2-Spanner

Combines the rounding analysis (`rounding_success_log`, `Rounding.lean`) with Lemma 3.1
(`isFTSpanner_two_iff`) and `LP ≤ OPT` (`exists_lp4_of_isFTSpanner`, `Characterization.lean`).

Solving LP (4) (Lemma 3.2, Ellipsoid) is not modelled: the theorem is stated for *any* LP (4)-feasible
solution whose value is at most the cost of a given spanner `H⋆`; an optimal LP solution has this
property for an optimal spanner `H⋆` (`exists_lp4_of_isFTSpanner`).
-/

open MeasureTheory

namespace DinitzKrauthgamer

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Theorem 3.3 of Dinitz–Krauthgamer (PODC'11).** Let `E` be a loopless digraph on `n ≥ 2`
vertices with arc costs `c ≥ 0`, `(x, f)` an LP (4)-feasible solution, and `H⋆` any `r`-fault-tolerant
2-spanner with `lpValue ≤ cost(H⋆)` (e.g. `x` an LP optimum, `H⋆` an optimal spanner). Rounding
with independent uniform thresholds and `α = 12 ln n` (Algorithm 1) yields, with probability at least
`2/3 - 1/n`, an `r`-fault-tolerant 2-spanner of cost at most `72 ln n · cost(H⋆)`. -/
theorem theorem_3_3 {E : Finset (V × V)} {r : ℕ} {x : V × V → ℝ} {f : V × V → V → ℝ}
    {c : V × V → ℝ} (hloop : Loopless E) (hx : IsLP4Feasible E r x f) (hc : ∀ e ∈ E, 0 ≤ c e)
    (hn : 2 ≤ Fintype.card V) {Hstar : Finset (V × V)} (hopt : lpValue c E x ≤ cost c Hstar) :
    2 / 3 - 1 / (Fintype.card V : ℝ) ≤
      (thresholdMeasure V).real {T |
        IsFTSpanner E (roundE E x (12 * Real.log (Fintype.card V)) T) r 2 ∧
        cost c (roundE E x (12 * Real.log (Fintype.card V)) T) ≤
          72 * Real.log (Fintype.card V) * cost c Hstar} := by
  refine (rounding_success_log hx hc hn).trans (measureReal_mono ?_ (measure_ne_top _ _))
  rintro T ⟨hsat, hcost⟩
  refine ⟨(isFTSpanner_two_iff hloop (Finset.filter_subset _ _)).mpr hsat, hcost.trans ?_⟩
  have : 0 ≤ Real.log (Fintype.card V) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ _))
  gcongr

/-- `LP ≤ OPT` makes `theorem_3_3` applicable: every `r`-fault-tolerant 2-spanner `H⋆` yields an
LP (4)-feasible solution of value `cost(H⋆)`. -/
theorem theorem_3_3' {E : Finset (V × V)} {r : ℕ} {c : V × V → ℝ} (hloop : Loopless E)
    (hc : ∀ e ∈ E, 0 ≤ c e) (hn : 2 ≤ Fintype.card V) {Hstar : Finset (V × V)}
    (hH : IsFTSpanner E Hstar r 2) :
    ∃ x f, IsLP4Feasible E r x f ∧ lpValue c E x = cost c Hstar ∧
      2 / 3 - 1 / (Fintype.card V : ℝ) ≤
      (thresholdMeasure V).real {T |
        IsFTSpanner E (roundE E x (12 * Real.log (Fintype.card V)) T) r 2 ∧
        cost c (roundE E x (12 * Real.log (Fintype.card V)) T) ≤
          72 * Real.log (Fintype.card V) * cost c Hstar} := by
  obtain ⟨x, f, hx, hval⟩ := exists_lp4_of_isFTSpanner hloop hH c
  exact ⟨x, f, hx, hval, theorem_3_3 hloop hx hc hn hval.le⟩

end DinitzKrauthgamer
