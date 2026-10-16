import Papers.PODC2021.RestorableTiebreaking.Existence

/-!
# Theorem 20: random perturbations are ATW functions with probability 1

Bodwin–Parter, PODC 2021, Theorem 20. The random weights are `r(u, v) = sgn(u, v) · ρ({u, v})`
where the values `ρ(e)`, `e : Sym2 V`, are independent and uniform on `[-ε, ε]`: `ρ` is drawn
from the uniform probability measure `volume[|box ε]` on the box `[-ε, ε]^{Sym2 V}`. (The paper
draws one value per edge of `G`; values on non-edges are unused, so this is the same
distribution on the relevant coordinates.)

The proof: a bad `ρ` satisfies a nontrivial linear equation `∑ₑ cₑ ρ(e) = 0` with
`c ∈ {-1, 0, 1}^{Sym2 V}` (`generic_of_coeff`); there are countably many such hyperplanes, each of
Lebesgue measure zero.
-/

open Finset SimpleGraph MeasureTheory ProbabilityTheory

set_option linter.unusedSectionVars false

namespace RestorableTiebreaking

variable {V : Type*} [DecidableEq V] [Fintype V] [LinearOrder V] {G : SimpleGraph V}

/-- The box `[-ε, ε]^{Sym2 V}`. -/
def box (V : Type*) (ε : ℝ) : Set (Sym2 V → ℝ) := Set.univ.pi fun _ => Set.Icc (-ε) ε

omit [DecidableEq V] [LinearOrder V] in
lemma measurableSet_box (ε : ℝ) : MeasurableSet (box V ε) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

omit [DecidableEq V] [LinearOrder V] in
/-- For `ε > 0` the uniform distribution on the box is a probability measure. -/
lemma isProbabilityMeasure_box {ε : ℝ} (hε : 0 < ε) :
    IsProbabilityMeasure (volume[|box V ε]) := by
  classical
  apply cond_isProbabilityMeasure_of_finite
  · rw [box, Set.pi_univ_Icc, Real.volume_Icc_pi]
    exact prod_ne_zero_iff.mpr fun _ _ => by simp; linarith
  · rw [box, Set.pi_univ_Icc, Real.volume_Icc_pi]
    exact ENNReal.prod_ne_top fun _ _ => ENNReal.ofReal_ne_top

omit [DecidableEq V] [LinearOrder V] in
/-- The degenerate `ρ` (some nonzero `{-1,0,1}`-combination vanishes) form a Lebesgue-null set. -/
lemma volume_degenerate :
    volume {ρ : Sym2 V → ℝ | ∃ c : Sym2 V → ℤ, (∀ e, |c e| ≤ 1) ∧ c ≠ 0 ∧
      ∑ e, (c e : ℝ) * ρ e = 0} = 0 := by
  classical
  let L : (Sym2 V → ℤ) → (Sym2 V → ℝ) →ₗ[ℝ] ℝ := fun c =>
    ∑ e, (c e : ℝ) • (LinearMap.proj e : (Sym2 V → ℝ) →ₗ[ℝ] ℝ)
  have hL : ∀ c ρ, L c ρ = ∑ e, (c e : ℝ) * ρ e := by
    intro c ρ; simp [L, LinearMap.sum_apply]
  have hsub : {ρ : Sym2 V → ℝ | ∃ c : Sym2 V → ℤ, (∀ e, |c e| ≤ 1) ∧ c ≠ 0 ∧
      ∑ e, (c e : ℝ) * ρ e = 0} ⊆
      ⋃ c : {c : Sym2 V → ℤ // c ≠ 0}, (LinearMap.ker (L c.1) : Set (Sym2 V → ℝ)) := by
    rintro ρ ⟨c, -, hc0, hc⟩
    exact Set.mem_iUnion.mpr ⟨⟨c, hc0⟩, by simp [hL, hc]⟩
  refine measure_mono_null hsub (measure_iUnion_null fun c => ?_)
  apply Measure.addHaar_submodule
  intro htop
  obtain ⟨e, he⟩ : ∃ e, c.1 e ≠ 0 := by
    by_contra h; push Not at h; exact c.2 (funext h)
  have : Pi.single e 1 ∈ LinearMap.ker (L c.1) := htop ▸ Submodule.mem_top
  rw [LinearMap.mem_ker, hL] at this
  simp [Pi.single_apply] at this
  exact he this

/-- **Theorem 20 of [Bodwin–Parter].** Let `0 < ε < 1/(2n)`. If every value `ρ(e)` is drawn
independently and uniformly from `[-ε, ε]`, then with probability 1 the antisymmetric weights
`r(u, v) = sgn(u, v) · ρ({u, v})` form an `f`-fault tiebreaking weight function for every `f`. -/
theorem theorem20 {ε : ℝ} (hε : 0 < ε) (hεn : ε < 1 / (2 * Fintype.card V)) :
    ∀ᵐ ρ ∂(volume[|box V ε]), ∀ f, IsATW G f (rOf ρ) := by
  have h2n : 2 * Fintype.card V * ε < 1 := by
    rcases Nat.eq_zero_or_pos (Fintype.card V) with hn | hn
    · simp [hn]
    · have : (0 : ℝ) < 2 * Fintype.card V := by positivity
      rw [lt_div_iff₀ this] at hεn; linarith
  have hae : ∀ᵐ ρ ∂(volume : Measure (Sym2 V → ℝ)), ρ ∈ box V ε → ∀ f, IsATW G f (rOf ρ) := by
    rw [ae_iff]
    refine measure_mono_null ?_ volume_degenerate
    intro ρ hρ
    simp only [Set.mem_ofPred_eq, not_imp] at hρ
    obtain ⟨hbox, hbad⟩ := hρ
    by_contra hgood
    simp only [Set.mem_ofPred_eq, not_exists, not_and] at hgood
    apply hbad
    intro f
    refine isATW_of_coeff hε.le (by linarith) (fun e => abs_le.mpr (hbox e (Set.mem_univ e)))
      (fun c hc hc0 hsum => hgood c hc hc0 hsum) f
  rw [ProbabilityTheory.cond]
  exact Measure.ae_smul_measure ((ae_restrict_iff' (measurableSet_box ε)).mpr hae) _

end RestorableTiebreaking
