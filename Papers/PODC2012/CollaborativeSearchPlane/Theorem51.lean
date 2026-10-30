import Papers.PODC2012.CollaborativeSearchPlane.Geometry

/-!
# Theorem 5.1: the harmonic search algorithm

Each agent (1) goes to a node `u` chosen with probability `p(u) = c / d(u)^(2+δ)`, (2) performs a
spiral search of length `t(u) = d(u)^(2+δ)`, (3) returns. (For `u = s` the paper's `p(u)` divides
by `0`; we put `p(s) = 0`.) With the spiral guarantee of `Phases.lean` (a spiral from `u` reaches
every `v` with `σ d(u, v)² ≤ t` within `σ d(u, v)²` steps), an agent that picked `u` with
`σ d(u, τ)² ≤ t(u)` finds the treasure by time `d(u) + σ d(u, τ)²` (`harmonicBound`); the
running time of the `k` agents is at most the minimum of these bounds (`harmonicTime`).

`theorem_5_1`: for every `δ > 0` and `ε ∈ (0, 1)` there are `α, C > 0` such that whenever
`k > α D^δ`, with probability at least `1 - ε` the running time is at most `C (D + D^(2+δ)/k)`.
(The paper states "with probability at least `1 - ε`, the *expected* running time is
`O(D + D^(2+δ)/k)`" and assumes `δ ≤ 0.8`; the restriction on `δ` is not needed.)
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset
open scoped ENNReal

/-! ### The harmonic distribution -/

/-- The unnormalized harmonic weight `d(u)^-(2+δ)` (`0` at the source). -/
noncomputable def hWeight (δ : ℝ) (u : Node) : ℝ := if u = 0 then 0 else (dist u : ℝ) ^ (-(2 + δ))

theorem hWeight_nonneg (δ : ℝ) (u : Node) : 0 ≤ hWeight δ u := by
  unfold hWeight; split_ifs <;> positivity

theorem dist_pos_of_ne {u : Node} (hu : u ≠ 0) : 0 < dist u := by
  unfold dist
  by_contra h
  apply hu
  have : u.1 = 0 ∧ u.2 = 0 := by omega
  exact Prod.ext this.1 this.2

/-- The one-dimensional majorant `(|x| + 1)^-(1 + δ/2)`. -/
noncomputable def hMaj (δ : ℝ) (x : ℤ) : ℝ := ((x.natAbs : ℝ) + 1) ^ (-(1 + δ / 2))

theorem summable_hMaj {δ : ℝ} (hδ : 0 < δ) : Summable (hMaj δ) := by
  have h1 : Summable fun n : ℕ => ((n : ℝ) + 1) ^ (-(1 + δ / 2)) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 (by linarith : -(1 + δ / 2) < -1))
    simpa using this
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa [hMaj] using h1
  · simpa [hMaj] using h1

theorem hWeight_le {δ : ℝ} (hδ : 0 < δ) (u : Node) :
    hWeight δ u ≤ 2 ^ (2 + δ) * (hMaj δ u.1 * hMaj δ u.2) := by
  unfold hWeight
  split_ifs with hu
  · unfold hMaj; positivity
  set d : ℝ := (dist u : ℝ)
  have hd : 1 ≤ d := by
    have : 1 ≤ dist u := dist_pos_of_ne hu
    simp only [d]; exact_mod_cast this
  set a : ℝ := (u.1.natAbs : ℝ) + 1
  set b : ℝ := (u.2.natAbs : ℝ) + 1
  have ha : 1 ≤ a := by simp [a]
  have hb : 1 ≤ b := by simp [b]
  have hab : a * b ≤ (2 * d) ^ 2 := by
    have : a + b = d + 2 := by simp only [a, b, d, dist]; push_cast; ring
    nlinarith
  have e1 : hMaj δ u.1 * hMaj δ u.2 = (a * b) ^ (-(1 + δ / 2)) := by
    unfold hMaj; rw [Real.mul_rpow (by positivity) (by positivity)]
  have e2 : ((2 * d) ^ 2) ^ (-(1 + δ / 2)) = 2 ^ (-(2 + δ)) * d ^ (-(2 + δ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.mul_rpow (by norm_num)
      (by positivity)]
    congr 2 <;> push_cast <;> ring
  have h3 : ((2 * d) ^ 2) ^ (-(1 + δ / 2)) ≤ (a * b) ^ (-(1 + δ / 2)) :=
    Real.rpow_le_rpow_of_nonpos (by positivity) hab (by linarith)
  rw [e1]
  rw [e2] at h3
  have h4 : (2 : ℝ) ^ (2 + δ) * 2 ^ (-(2 + δ)) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  calc d ^ (-(2 + δ)) = 2 ^ (2 + δ) * (2 ^ (-(2 + δ)) * d ^ (-(2 + δ))) := by
        rw [← mul_assoc, h4, one_mul]
    _ ≤ 2 ^ (2 + δ) * (a * b) ^ (-(1 + δ / 2)) := by gcongr

theorem summable_hWeight {δ : ℝ} (hδ : 0 < δ) : Summable (hWeight δ) := by
  have hprod : Summable fun u : Node => hMaj δ u.1 * hMaj δ u.2 :=
    Summable.mul_of_nonneg (summable_hMaj hδ) (summable_hMaj hδ)
      (fun x => by unfold hMaj; positivity) (fun x => by unfold hMaj; positivity)
  exact Summable.of_nonneg_of_le (hWeight_nonneg δ) (hWeight_le hδ) (hprod.mul_left _)

/-- The normalizing factor `1/c = ∑_u d(u)^-(2+δ)`. -/
noncomputable def hTotal (δ : ℝ) : ℝ := ∑' u, hWeight δ u

theorem hTotal_pos {δ : ℝ} (hδ : 0 < δ) : 0 < hTotal δ := by
  have h1 : hWeight δ (1, 0) = 1 := by simp [hWeight, dist]
  have := (summable_hWeight hδ).le_tsum (1, 0) (fun u _ => hWeight_nonneg δ u)
  unfold hTotal; linarith

theorem tsum_ofReal_hWeight {δ : ℝ} (hδ : 0 < δ) :
    ∑' u, ENNReal.ofReal (hWeight δ u) = ENNReal.ofReal (hTotal δ) :=
  (ENNReal.ofReal_tsum_of_nonneg (hWeight_nonneg δ) (summable_hWeight hδ)).symm

/-- The harmonic distribution `p(u) = c / d(u)^(2+δ)`. -/
noncomputable def harmonicPMF {δ : ℝ} (hδ : 0 < δ) : PMF Node :=
  PMF.normalize (fun u => ENNReal.ofReal (hWeight δ u))
    (by rw [tsum_ofReal_hWeight hδ]; simpa using hTotal_pos hδ)
    (by rw [tsum_ofReal_hWeight hδ]; exact ENNReal.ofReal_ne_top)

theorem harmonicPMF_apply {δ : ℝ} (hδ : 0 < δ) (u : Node) :
    harmonicPMF hδ u = ENNReal.ofReal (hWeight δ u / hTotal δ) := by
  rw [harmonicPMF, PMF.normalize_apply, tsum_ofReal_hWeight hδ, ← ENNReal.ofReal_inv_of_pos
    (hTotal_pos hδ), ← ENNReal.ofReal_mul (hWeight_nonneg δ u), div_eq_mul_inv]

/-! ### The algorithm and its running time -/

/-- Spiral length `t(u) = ⌊d(u)^(2+δ)⌋`. -/
noncomputable def hSpiral (δ : ℝ) (u : Node) : ℕ := ⌊(dist u : ℝ) ^ (2 + δ)⌋₊

/-- Time by which an agent that picked `u` has found the treasure at `τ`: `d(u) + σ d(u, τ)²` if the
spiral of length `t(u)` reaches `τ`, `⊤` otherwise. -/
noncomputable def harmonicBound (σ : ℕ) (δ : ℝ) (τ u : Node) : ℝ≥0∞ :=
  if σ * dist (u - τ) ^ 2 ≤ hSpiral δ u then ((dist u + σ * dist (u - τ) ^ 2 : ℕ) : ℝ≥0∞) else ⊤

/-- Running time (bound) of the harmonic algorithm when agent `a` picks `ω a`. -/
noncomputable def harmonicTime (σ : ℕ) (δ : ℝ) (τ : Node) {k : ℕ} (ω : Fin k → Node) : ℝ≥0∞ :=
  ⨅ a, harmonicBound σ δ τ (ω a)

/-- The nodes within distance `r` of `τ`. -/
def ballAround (τ : Node) (r : ℕ) : Finset Node := (ballFinset r).image fun v => v + τ

theorem mem_ballAround {τ u : Node} {r : ℕ} : u ∈ ballAround τ r ↔ dist (u - τ) ≤ r := by
  unfold ballAround
  rw [Finset.mem_image]
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_ballFinset] at hv
    simpa using hv
  · intro h
    exact ⟨u - τ, mem_ballFinset.2 h, by abel⟩

/-- **Theorem 5.1** of [Feinerman–Korman–Lotker–Sereni]: for every `δ > 0` and `ε ∈ (0, 1)` there
are `α, C > 0` such that if `k > α D^δ`, then with probability at least `1 - ε` the harmonic
algorithm finds the treasure within time `C (D + D^(2+δ)/k)`. -/
theorem theorem_5_1 {δ : ℝ} (hδ : 0 < δ) {σ : ℕ} (hσ : 1 ≤ σ) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < 1) : ∃ α C : ℝ, 0 < α ∧ 0 < C ∧ ∀ {k : ℕ} (τ : Node), 1 ≤ dist τ →
      α * (dist τ : ℝ) ^ δ < k →
      ENNReal.ofReal (1 - ε) ≤ Measure.pi (fun _ : Fin k => (harmonicPMF hδ).toMeasure)
        {ω | harmonicTime σ δ τ ω ≤
          ENNReal.ofReal (C * (dist τ + (dist τ : ℝ) ^ (2 + δ) / k))} := by
  set s : ℝ := 2 + δ
  set K : ℝ := (5 / 4 : ℝ) ^ s
  set Z := hTotal δ
  set L : ℝ := Real.log (1 / ε)
  have hK : 0 < K := by positivity
  have hZ : 0 < Z := hTotal_pos hδ
  have hL : 0 < L := Real.log_pos (by rw [lt_div_iff₀ hε0]; linarith)
  set γ : ℝ := 2 * K * Z * L
  have hγ : 0 < γ := by positivity
  have hσ' : (1 : ℝ) ≤ σ := by exact_mod_cast hσ
  refine ⟨16 * σ * γ, 2 + σ * γ, by positivity, by positivity, ?_⟩
  intro k τ hτ hk
  set D := dist τ
  have hD : (1 : ℝ) ≤ D := by exact_mod_cast hτ
  have hD0 : (0 : ℝ) < D := by linarith
  have hDδ : 0 < (D : ℝ) ^ δ := by positivity
  have hk0 : (0 : ℝ) < k := lt_of_le_of_lt (by positivity) hk
  have hDs : (D : ℝ) ^ s = (D : ℝ) ^ 2 * (D : ℝ) ^ δ := by
    rw [Real.rpow_add hD0]; norm_cast
  -- the radius of the good ball around `τ`
  set ρ2 : ℝ := γ * (D : ℝ) ^ s / k
  have hρ2 : 0 ≤ ρ2 := by positivity
  set r := ⌊Real.sqrt ρ2⌋₊
  have hr2 : (r : ℝ) ^ 2 ≤ ρ2 := by
    calc (r : ℝ) ^ 2 ≤ (Real.sqrt ρ2) ^ 2 := by
          gcongr; exact Nat.floor_le (Real.sqrt_nonneg _)
      _ = ρ2 := Real.sq_sqrt hρ2
  have hr1 : ρ2 < ((r : ℝ) + 1) ^ 2 := by
    have h := Nat.lt_floor_add_one (Real.sqrt ρ2)
    calc ρ2 = (Real.sqrt ρ2) ^ 2 := (Real.sq_sqrt hρ2).symm
      _ < ((r : ℝ) + 1) ^ 2 := by gcongr
  have hρD : ρ2 ≤ (D : ℝ) ^ 2 / (16 * σ) := by
    simp only [ρ2]
    rw [div_le_div_iff₀ hk0 (by positivity), hDs]
    have : 16 * σ * γ * (D : ℝ) ^ δ ≤ k := hk.le
    nlinarith [sq_nonneg (D : ℝ)]
  have hσr : (σ : ℝ) * (r : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 / 16 := by
    have := hr2.trans hρD
    rw [le_div_iff₀ (by positivity)] at this
    rw [le_div_iff₀ (by norm_num)]; nlinarith
  have hrD : 4 * (r : ℝ) ≤ D := by
    have h1 : (r : ℝ) ^ 2 ≤ (D : ℝ) ^ 2 / 16 := by nlinarith
    nlinarith [sq_nonneg (4 * (r : ℝ) - D), (Nat.cast_nonneg r : (0 : ℝ) ≤ r)]
  set B := ballAround τ r
  -- properties of the nodes of the good ball
  have hB : ∀ u ∈ B, 3 * (D : ℝ) / 4 ≤ dist u ∧ (dist u : ℝ) ≤ 5 * D / 4 := by
    intro u hu
    rw [mem_ballAround] at hu
    have h1 := dist_add_le u (τ - u)
    have h2 := dist_add_le τ (u - τ)
    simp only [add_sub_cancel] at h1 h2
    rw [dist_sub_comm τ u] at h1
    have hu' : (dist (u - τ) : ℝ) ≤ r := by exact_mod_cast hu
    have h1' : (D : ℝ) ≤ dist u + dist (u - τ) := by exact_mod_cast h1
    have h2' : (dist u : ℝ) ≤ D + dist (u - τ) := by exact_mod_cast h2
    constructor <;> linarith
  have hbound : ∀ u ∈ B, harmonicBound σ δ τ u ≤
      ENNReal.ofReal ((2 + σ * γ) * (D + (D : ℝ) ^ (2 + δ) / k)) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hB u hu
    have hu' : (dist (u - τ) : ℝ) ≤ r := by exact_mod_cast (mem_ballAround.1 hu)
    have hdu1 : (1 : ℝ) ≤ dist u := by
      have : (0 : ℝ) < dist u := by linarith
      have : 0 < dist u := by exact_mod_cast this
      exact_mod_cast this
    have hsp : σ * dist (u - τ) ^ 2 ≤ hSpiral δ u := by
      unfold hSpiral
      apply Nat.le_floor
      push_cast
      calc (σ : ℝ) * (dist (u - τ) : ℝ) ^ 2 ≤ σ * (r : ℝ) ^ 2 := by gcongr
        _ ≤ (D : ℝ) ^ 2 / 16 := hσr
        _ ≤ (dist u : ℝ) ^ 2 := by nlinarith
        _ = (dist u : ℝ) ^ (2 : ℝ) := by norm_cast
        _ ≤ (dist u : ℝ) ^ (2 + δ) := Real.rpow_le_rpow_of_exponent_le hdu1 (by linarith)
    unfold harmonicBound
    simp only [hsp, ↓reduceIte]
    rw [← ENNReal.ofReal_natCast]
    apply ENNReal.ofReal_le_ofReal
    push_cast
    have h3 : (σ : ℝ) * (dist (u - τ) : ℝ) ^ 2 ≤ σ * γ * (D : ℝ) ^ s / k := by
      calc (σ : ℝ) * (dist (u - τ) : ℝ) ^ 2 ≤ σ * (r : ℝ) ^ 2 := by gcongr
        _ ≤ σ * ρ2 := by gcongr
        _ = σ * γ * (D : ℝ) ^ s / k := by simp only [ρ2]; ring
    set X : ℝ := (D : ℝ) ^ (2 + δ) / k
    have h4 : 0 ≤ X := by positivity
    have e : σ * γ * (D : ℝ) ^ s / k = σ * γ * X := by simp only [X, s]; ring
    have e2 : (2 + σ * γ) * (D + X) = 2 * D + 2 * X + σ * γ * D + σ * γ * X := by ring
    have h5 : 0 ≤ (σ : ℝ) * γ * D := by positivity
    rw [e2]
    linarith
  -- the probability that a single agent picks a node of the good ball
  have hw : ∀ u ∈ B, ENNReal.ofReal (1 / (K * (D : ℝ) ^ s * Z)) ≤ harmonicPMF hδ u := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := hB u hu
    rw [harmonicPMF_apply]
    apply ENNReal.ofReal_le_ofReal
    have hu0 : u ≠ 0 := by
      intro h; rw [h] at hu1; simp [dist] at hu1; linarith
    have hdu : (0 : ℝ) < dist u := by linarith
    have h1 : ((5 / 4 : ℝ) * D) ^ (-s) ≤ (dist u : ℝ) ^ (-s) :=
      Real.rpow_le_rpow_of_nonpos hdu (by linarith) (by linarith)
    rw [Real.mul_rpow (by norm_num) hD0.le, Real.rpow_neg (by norm_num),
      Real.rpow_neg hD0.le] at h1
    simp only [hWeight, hu0, ↓reduceIte]
    rw [div_le_div_iff₀ (by positivity) hZ, one_mul]
    calc Z = (K * (D : ℝ) ^ s) * (K⁻¹ * ((D : ℝ) ^ s)⁻¹) * Z := by field_simp
      _ ≤ (K * (D : ℝ) ^ s) * (dist u : ℝ) ^ (-s) * Z := by gcongr
      _ = _ := by ring
  have hcard : ((r : ℝ) + 1) ^ 2 ≤ 2 * B.card := by
    have h := card_ball_around_ge τ r B fun v hv => mem_ballAround.2 hv
    have h' : (((r + 1) * (r + 2) : ℕ) : ℝ) ≤ ((2 * B.card : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at h'
    nlinarith
  have hμB : ENNReal.ofReal (L / k) ≤ (harmonicPMF hδ).toMeasure B := by
    rw [PMF.toMeasure_apply_finset]
    calc ENNReal.ofReal (L / k) ≤ ∑ _u ∈ B, ENNReal.ofReal (1 / (K * (D : ℝ) ^ s * Z)) := by
          rw [Finset.sum_const, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
            ← ENNReal.ofReal_mul (by positivity)]
          apply ENNReal.ofReal_le_ofReal
          rw [div_le_iff₀ hk0]
          have : (B.card : ℝ) * (1 / (K * (D : ℝ) ^ s * Z)) * k
              = B.card * k / (K * (D : ℝ) ^ s * Z) := by ring
          rw [this, le_div_iff₀ (by positivity)]
          have h5 : γ * (D : ℝ) ^ s < ((r : ℝ) + 1) ^ 2 * k := by
            have := hr1; simp only [ρ2] at this; rwa [div_lt_iff₀ hk0] at this
          simp only [γ] at h5
          nlinarith
      _ ≤ _ := Finset.sum_le_sum hw
  -- the failure event is a box
  set μ := (harmonicPMF hδ).toMeasure
  have hBm : MeasurableSet ((B : Set Node)ᶜ) := (B : Set Node)ᶜ.to_countable.measurableSet
  have hfail : Measure.pi (fun _ : Fin k => μ) (Set.univ.pi fun _ => (B : Set Node)ᶜ)
      ≤ ENNReal.ofReal ε := by
    rw [Measure.pi_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    have h1 : μ (B : Set Node)ᶜ ≤ ENNReal.ofReal (Real.exp (-(L / k))) := by
      rw [prob_compl_eq_one_sub (B : Set Node).to_countable.measurableSet]
      calc 1 - μ B ≤ 1 - ENNReal.ofReal (L / k) := tsub_le_tsub_left hμB 1
        _ = ENNReal.ofReal (1 - L / k) := by
            rw [ENNReal.ofReal_sub _ (by positivity), ENNReal.ofReal_one]
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (-(L / k))])
    calc μ (B : Set Node)ᶜ ^ k ≤ ENNReal.ofReal (Real.exp (-(L / k))) ^ k := by gcongr
      _ = ENNReal.ofReal (Real.exp (-(L / k)) ^ k) := by
          rw [ENNReal.ofReal_pow (by positivity)]
      _ = ENNReal.ofReal ε := by
          rw [← Real.exp_nat_mul]
          congr 1
          have : (k : ℝ) * -(L / k) = -L := by field_simp
          rw [this, Real.exp_neg, Real.exp_log (by positivity)]
          simp
  -- conclusion
  have hsub : (Set.univ.pi fun _ : Fin k => (B : Set Node)ᶜ)ᶜ ⊆
      {ω | harmonicTime σ δ τ ω ≤
        ENNReal.ofReal ((2 + σ * γ) * (D + (D : ℝ) ^ (2 + δ) / k))} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_pi, Set.mem_univ, forall_const, not_forall,
      not_not, Finset.mem_coe] at hω
    obtain ⟨a, ha⟩ := hω
    exact (iInf_le (fun a => harmonicBound σ δ τ (ω a)) a).trans (hbound _ ha)
  have hboxm : MeasurableSet (Set.univ.pi fun _ : Fin k => (B : Set Node)ᶜ) :=
    MeasurableSet.univ_pi fun _ => hBm
  calc ENNReal.ofReal (1 - ε) = 1 - ENNReal.ofReal ε := by
        rw [ENNReal.ofReal_sub _ hε0.le, ENNReal.ofReal_one]
    _ ≤ 1 - Measure.pi (fun _ : Fin k => μ) (Set.univ.pi fun _ => (B : Set Node)ᶜ) :=
        tsub_le_tsub_left hfail 1
    _ = Measure.pi (fun _ : Fin k => μ) (Set.univ.pi fun _ => (B : Set Node)ᶜ)ᶜ :=
        (prob_compl_eq_one_sub hboxm).symm
    _ ≤ _ := measure_mono hsub

end Podc.CollaborativeSearchPlane
