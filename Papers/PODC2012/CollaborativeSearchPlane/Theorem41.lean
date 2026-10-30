import Papers.PODC2012.CollaborativeSearchPlane.Basic

/-!
# Theorem 4.1: no uniform search algorithm is `O(log k)`-competitive

The paper's proof fixes a large time `T`, uses `kᵢ = 2ⁱ` agents and the radii
`Dᵢ = √(T kᵢ / φ(kᵢ))`, so that every node of the ball `B(Dᵢ)` is found with probability `≥ 1/2` by
time `2T` (Markov), hence visited by one agent with probability `≥ 1/(2kᵢ)`; the shells
`Sᵢ = B(Dᵢ) \ B(Dᵢ₋₁)` are disjoint, and since one agent visits at most `2T + 1` nodes,
`T · ∑ᵢ 1/φ(2ⁱ) = O(T)`: the series `∑ᵢ 1/φ(2ⁱ)` converges, contradicting `φ(k) = O(log k)`.

The paper's estimate `|Sᵢ|/kᵢ = Ω(T/φ(kᵢ))` needs `Dᵢ₋₁ < Dᵢ`, i.e. `φ(2ⁱ) < 2 φ(2ⁱ⁻¹)`, which does
not follow from `φ(k) = O(log k)`. We repair this with two changes: the radii are replaced by their
running maxima `R'ᵢ = max_{j ≤ i} Rⱼ` (a node within distance `Rⱼ`, `j ≤ i`, is visited with
probability `≥ 1/(2·2ʲ) ≥ 1/(2·2ⁱ)`), and the shell sums are combined by Abel summation
(`abel_shell`) instead of term-wise. This proves the paper's intermediate claim for *every* `φ`:

* `summable_inv_of_isCompetitive` — if a uniform algorithm is `φ`-competitive, then
  `∑ᵢ 1/φ(2ⁱ) ≤ 320`; in particular the series converges;
* `theorem_4_1` — hence `φ` is not `O(log k)`.
-/

namespace Podc.CollaborativeSearchPlane

open MeasureTheory Finset Filter Asymptotics
open scoped ENNReal

/-! ### Elementary sums -/

theorem sum_Ico_ge (A B : ℕ) (h : A ≤ B) :
    ((B : ℝ) ^ 2 - (A : ℝ) ^ 2) / 2 ≤ ∑ n ∈ Ico (A + 1) (B + 1), ((n : ℝ) + 1) := by
  induction B, h using Nat.le_induction with
  | base => simp
  | succ B hAB ih =>
    rw [Finset.sum_Ico_succ_top (by omega)]
    push_cast
    nlinarith

/-- Abel summation over nested balls: if `f n ≥ (n+1)/2^(i+1)` for all `n ≤ R i` (`R` monotone),
then `∑_{n ≤ R b} f n ≥ R_b²/2^(b+2) + ∑_{i<b} R_i²/2^(i+3)`. -/
theorem abel_shell (f : ℕ → ℝ) (R : ℕ → ℕ) (hR : Monotone R) (b : ℕ)
    (h : ∀ i ≤ b, ∀ n ≤ R i, ((n : ℝ) + 1) / 2 ^ (i + 1) ≤ f n) :
    ((R b : ℝ) ^ 2 / 2 ^ (b + 2) + ∑ i ∈ range b, (R i : ℝ) ^ 2 / 2 ^ (i + 3))
      ≤ ∑ n ∈ range (R b + 1), f n := by
  induction b with
  | zero =>
    simp only [range_zero, sum_empty, add_zero, zero_add]
    have h1 : ∑ n ∈ range (R 0 + 1), ((n : ℝ) + 1) / 2 ≤ ∑ n ∈ range (R 0 + 1), f n :=
      Finset.sum_le_sum fun n hn => by
        simpa using h 0 le_rfl n (Nat.lt_succ_iff.1 (mem_range.1 hn))
    have h2 := sum_Ico_ge 0 (R 0) (Nat.zero_le _)
    simp only [zero_add, Nat.cast_zero] at h2
    have h3 : ∑ n ∈ range (R 0 + 1), ((n : ℝ) + 1) / 2
        = (∑ n ∈ Ico 1 (R 0 + 1), ((n : ℝ) + 1) + 1) / 2 := by
      rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (by omega), ← Finset.sum_div]
      simp; ring
    rw [h3] at h1
    have : (R 0 : ℝ) ^ 2 / 2 ^ 2 ≤ (∑ n ∈ Ico 1 (R 0 + 1), ((n : ℝ) + 1) + 1) / 2 := by
      have : (0:ℝ) ≤ R 0 := by positivity
      nlinarith
    linarith
  | succ b ih =>
    have ih' := ih fun i hi => h i (by omega)
    have hle : R b ≤ R (b + 1) := hR (Nat.le_succ b)
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : R b + 1 ≤ R (b + 1) + 1), sum_range_succ]
    have hsh : ((R (b + 1) : ℝ) ^ 2 - (R b : ℝ) ^ 2) / 2 / 2 ^ (b + 2)
        ≤ ∑ n ∈ Ico (R b + 1) (R (b + 1) + 1), f n := by
      calc ((R (b + 1) : ℝ) ^ 2 - (R b : ℝ) ^ 2) / 2 / 2 ^ (b + 2)
          ≤ (∑ n ∈ Ico (R b + 1) (R (b + 1) + 1), ((n : ℝ) + 1)) / 2 ^ (b + 2) := by
            gcongr; exact sum_Ico_ge _ _ hle
        _ = ∑ n ∈ Ico (R b + 1) (R (b + 1) + 1), ((n : ℝ) + 1) / 2 ^ (b + 1 + 1) := by
            rw [Finset.sum_div]
        _ ≤ _ := Finset.sum_le_sum fun n hn => h (b + 1) le_rfl n (by
            have := (mem_Ico.1 hn).2; omega)
    have e1 : (2 : ℝ) ^ (b + 3) = 2 * 2 ^ (b + 2) := by ring
    have e2 : (2 : ℝ) ^ (b + 1 + 2) = 2 * 2 ^ (b + 2) := by ring
    rw [e1] at *
    rw [e2]
    have hp : (0 : ℝ) < 2 ^ (b + 2) := by positivity
    have : (R (b + 1) : ℝ) ^ 2 / (2 * 2 ^ (b + 2)) + (R b : ℝ) ^ 2 / (2 * 2 ^ (b + 2))
        = (R b : ℝ) ^ 2 / 2 ^ (b + 2)
          + ((R (b + 1) : ℝ) ^ 2 - (R b : ℝ) ^ 2) / 2 / 2 ^ (b + 2) := by
      field_simp; ring
    linarith

/-! ### Positivity of competitive ratios -/

/-- Every competitive ratio is positive: otherwise all nodes would be found at time `0`, but one
agent occupies only one node at a time. -/
theorem pos_of_expectedTime_le (μ : Measure Traj) [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    (c : ℝ) (h : ∀ τ : Node, 1 ≤ dist τ →
      expectedTime (fun _ : Fin k => μ) τ ≤ ENNReal.ofReal (c * optBound k τ)) :
    0 < c := by
  by_contra hc
  replace hc := not_lt.1 hc
  have hE : ∀ u : Node, dist u = 2 * k → expectedTime (fun _ : Fin k => μ) u ≤ ENNReal.ofReal 0 := by
    intro u hu
    refine (h u (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ optBound k u := by unfold optBound; positivity
    nlinarith
  have h1 := diagMass_ge μ (by omega : 0 < k) 0 (2 * k) 0 (by norm_num) hE
  have h2 := sum_diagMass_le μ {2 * k} 0
  simp only [sum_singleton, CharP.cast_eq_zero, zero_add] at h2
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have : (1 : ℝ) < ((2 * k : ℕ) + 1 : ℝ) / (2 * k) := by
    rw [lt_div_iff₀ (by positivity)]; push_cast; linarith
  linarith

theorem IsCompetitive.pos {μ : Measure Traj} [IsProbabilityMeasure μ] {φ : ℕ → ℝ}
    (hA : IsCompetitive μ φ) {k : ℕ} (hk : 1 ≤ k) : 0 < φ k :=
  pos_of_expectedTime_le μ hk (φ k) (hA k hk)

/-! ### The main estimate -/

/-- **The harmonic-sum argument of Theorem 4.1** (the claim "`∑ᵢ 1/φ(2ⁱ)` must converge" at the end
of the paper's proof), for an arbitrary `φ`: if a uniform algorithm is `φ`-competitive then all
partial sums of `∑ᵢ 1/φ(2ⁱ)` are at most `320`. -/
theorem sum_inv_le_of_isCompetitive (μ : Measure Traj) [IsProbabilityMeasure μ] (φ : ℕ → ℝ)
    (hA : IsCompetitive μ φ) (b : ℕ) : ∑ i ∈ range b, 1 / φ (2 ^ i) ≤ 320 := by
  -- notation
  set ψ : ℕ → ℝ := fun i => φ (2 ^ i) with hψ
  have hψpos : ∀ i, 0 < ψ i := fun i => hA.pos (Nat.one_le_two_pow)
  set T : ℝ := 1 + ∑ i ∈ range (b + 1), 2 * 2 ^ i * ψ i with hTdef
  have hT1 : 1 ≤ T := by
    have : 0 ≤ ∑ i ∈ range (b + 1), 2 * 2 ^ i * ψ i :=
      Finset.sum_nonneg fun i _ => by have := hψpos i; positivity
    linarith
  have hTi : ∀ i ≤ b, 2 * 2 ^ i * ψ i ≤ T := by
    intro i hi
    have : 2 * 2 ^ i * ψ i ≤ ∑ j ∈ range (b + 1), 2 * 2 ^ j * ψ j :=
      Finset.single_le_sum (f := fun j => 2 * 2 ^ j * ψ j)
        (fun j _ => by have := hψpos j; positivity) (mem_range.2 (by omega))
    linarith
  set N : ℕ := ⌈2 * T⌉₊ with hN
  have hN1 : 2 * T ≤ N + 1 := by
    have := Nat.le_ceil (2 * T); linarith
  have hN2 : (N : ℝ) + 1 ≤ 4 * T := by
    have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ 2 * T); linarith
  -- the radii
  set X : ℕ → ℝ := fun i => T * 2 ^ i / (2 * ψ i) with hX
  set R : ℕ → ℕ := fun i => Nat.sqrt ⌊X i⌋₊ with hR
  have hXpos : ∀ i, 0 < X i := fun i => by have := hψpos i; positivity
  have hRsq : ∀ i, ((R i : ℝ)) ^ 2 ≤ X i := by
    intro i
    have h1 := Nat.sqrt_le' ⌊X i⌋₊
    have h2 : ((⌊X i⌋₊ : ℕ) : ℝ) ≤ X i := Nat.floor_le (hXpos i).le
    have h3 : ((R i : ℝ)) ^ 2 ≤ ((⌊X i⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
    linarith
  have hRbig : ∀ i ≤ b, 2 ^ i ≤ R i := by
    intro i hi
    rw [hR, Nat.le_sqrt']
    apply Nat.le_floor
    have := hTi i hi
    have hp := hψpos i
    rw [hX]; push_cast
    rw [le_div_iff₀ (by positivity)]
    have : (0 : ℝ) < 2 ^ i := by positivity
    nlinarith
  have hRlow : ∀ i ≤ b, X i ≤ 4 * (R i : ℝ) ^ 2 := by
    intro i hi
    have h1 := Nat.lt_succ_sqrt' ⌊X i⌋₊
    have h2 : X i < ((⌊X i⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : ((⌊X i⌋₊ : ℕ) : ℝ) + 1 ≤ ((R i : ℝ) + 1) ^ 2 := by exact_mod_cast h1
    have h4 : (1 : ℝ) ≤ R i := by
      have := hRbig i hi
      exact_mod_cast le_trans Nat.one_le_two_pow this
    nlinarith
  -- every node within distance `R j` (`j ≤ b`) is found by time `T` in expectation with `2ʲ` agents
  have hfound : ∀ j ≤ b, ∀ n ≤ R j, 1 ≤ n → ∀ u : Node, dist u = n →
      expectedTime (fun _ : Fin (2 ^ j) => μ) u ≤ ENNReal.ofReal T := by
    intro j hj n hn hn1 u hu
    refine (hA (2 ^ j) Nat.one_le_two_pow u (by omega)).trans (ENNReal.ofReal_le_ofReal ?_)
    have hp := hψpos j
    have hk : (0 : ℝ) < 2 ^ j := by positivity
    have hnR : (n : ℝ) ≤ R j := by exact_mod_cast hn
    have hRk : (2 : ℝ) ^ j ≤ R j := by exact_mod_cast hRbig j hj
    have hn0 : (0 : ℝ) ≤ n := by positivity
    have hopt : optBound (2 ^ j) u ≤ 2 * (R j : ℝ) ^ 2 / 2 ^ j := by
      unfold optBound; rw [hu]; push_cast
      have : (n : ℝ) ≤ (R j : ℝ) ^ 2 / 2 ^ j := by
        rw [le_div_iff₀ hk]; nlinarith
      have : (n : ℝ) ^ 2 / 2 ^ j ≤ (R j : ℝ) ^ 2 / 2 ^ j := by gcongr
      linarith [show 2 * (R j : ℝ) ^ 2 / 2 ^ j = (R j : ℝ) ^ 2 / 2 ^ j + (R j : ℝ) ^ 2 / 2 ^ j by ring]
    have hX' : 2 * (R j : ℝ) ^ 2 / 2 ^ j * ψ j ≤ T := by
      have := hRsq j
      rw [hX] at this
      rw [le_div_iff₀ (by positivity)] at this
      rw [div_mul_eq_mul_div, div_le_iff₀ hk]; nlinarith
    calc φ (2 ^ j) * optBound (2 ^ j) u ≤ ψ j * (2 * (R j : ℝ) ^ 2 / 2 ^ j) := by
          rw [hψ]; exact mul_le_mul_of_nonneg_left hopt hp.le
      _ ≤ T := by linarith
  -- running maxima of the radii
  set R' : ℕ → ℕ := fun i => (range (i + 1)).sup R with hR'
  have hR'mono : Monotone R' := fun i j hij =>
    Finset.sup_mono (Finset.range_subset_range.2 (by omega))
  have hRR' : ∀ i, R i ≤ R' i := fun i => Finset.le_sup (f := R) (mem_range.2 (by omega))
  -- the source (distance `0`) gets the trivial weight `1`
  set f : ℕ → ℝ := fun n => if n = 0 then 1 else diagMass μ N n
  have hcond : ∀ i ≤ b, ∀ n ≤ R' i, ((n : ℝ) + 1) / 2 ^ (i + 1) ≤ f n := by
    intro i hi n hn
    rcases Nat.eq_zero_or_pos n with h0 | hn1
    · simp only [f, h0, ↓reduceIte, CharP.cast_eq_zero, zero_add]
      rw [div_le_one (by positivity)]
      exact one_le_pow₀ (by norm_num)
    simp only [f, hn1.ne', ↓reduceIte]
    obtain ⟨j, hj, hjeq⟩ := Finset.exists_mem_eq_sup (range (i + 1)) nonempty_range_add_one R
    have hj' : j ≤ i := Nat.lt_succ_iff.1 (mem_range.1 hj)
    have hnj : n ≤ R j := by rw [← hjeq]; exact hn
    have h1 := diagMass_ge μ (Nat.two_pow_pos j) N n T hN1 (hfound j (by omega) n hnj hn1)
    refine le_trans ?_ h1
    push_cast
    gcongr
    calc (2 : ℝ) * 2 ^ j = 2 ^ (j + 1) := by ring
      _ ≤ 2 ^ (i + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have habel := abel_shell f R' hR'mono b hcond
  have hsum : ∑ n ∈ range (R' b + 1), f n ≤ 1 + (N + 1) := by
    have h1 : ∀ n ∈ range (R' b + 1), f n ≤ (if n = 0 then 1 else 0) + diagMass μ N n := by
      intro n _
      simp only [f]
      split_ifs
      · linarith [diagMass_nonneg μ N n]
      · simp
    refine (Finset.sum_le_sum h1).trans ?_
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp only [mem_range, add_pos_iff, zero_lt_one, or_true, ↓reduceIte]
    linarith [sum_diagMass_le μ (range (R' b + 1)) N]
  have hpos : 0 ≤ (R' b : ℝ) ^ 2 / 2 ^ (b + 2) := by positivity
  -- compare with the harmonic-type sum
  have hterm : ∀ i ∈ range b, T / 64 * (1 / ψ i) ≤ (R' i : ℝ) ^ 2 / 2 ^ (i + 3) := by
    intro i hi
    have hib : i ≤ b := (Nat.lt_of_lt_of_le (mem_range.1 hi) le_rfl).le
    have h1 := hRlow i hib
    have h2 : (R i : ℝ) ≤ R' i := by exact_mod_cast hRR' i
    have h0 : (0 : ℝ) ≤ R i := by positivity
    have h3 : (R i : ℝ) ^ 2 ≤ (R' i : ℝ) ^ 2 := by gcongr
    have hp := hψpos i
    rw [hX] at h1
    rw [le_div_iff₀ (by positivity)]
    have e : T / 64 * (1 / ψ i) * 2 ^ (i + 3) = T * 2 ^ i / (2 * ψ i) / 4 := by
      field_simp; ring
    rw [e]; linarith
  have hsum' : T / 64 * ∑ i ∈ range b, 1 / ψ i ≤ 5 * T := by
    rw [Finset.mul_sum]
    have := Finset.sum_le_sum hterm
    linarith
  have : ∑ i ∈ range b, 1 / ψ i ≤ 320 := by
    have hT0 : 0 < T := by linarith
    nlinarith
  simpa [hψ] using this

/-- If a uniform algorithm is `φ`-competitive, then `∑ᵢ 1/φ(2ⁱ)` converges. -/
theorem summable_inv_of_isCompetitive (μ : Measure Traj) [IsProbabilityMeasure μ] (φ : ℕ → ℝ)
    (hA : IsCompetitive μ φ) : Summable fun i : ℕ => 1 / φ (2 ^ i) :=
  summable_of_sum_range_le (fun _ => (one_div_pos.2 (hA.pos Nat.one_le_two_pow)).le)
    (sum_inv_le_of_isCompetitive μ φ hA)

/-- **Theorem 4.1** of [Feinerman–Korman–Lotker–Sereni]: there is no uniform search algorithm that is
`O(log k)`-competitive. -/
theorem theorem_4_1 (μ : Measure Traj) [IsProbabilityMeasure μ] (φ : ℕ → ℝ)
    (hA : IsCompetitive μ φ) : ¬ φ =O[atTop] fun k : ℕ => Real.log k := by
  intro hO
  obtain ⟨c, hc⟩ := hO.bound
  have h2 : Tendsto (fun i : ℕ => 2 ^ i) atTop atTop :=
    tendsto_atTop_mono (fun _ => Nat.lt_two_pow_self.le) tendsto_id
  have hev := h2.eventually hc
  have hO' : (fun i : ℕ => ((i : ℝ))⁻¹) =O[atTop] fun i : ℕ => 1 / φ (2 ^ i) := by
    refine IsBigO.of_bound (c * Real.log 2) ?_
    filter_upwards [hev, eventually_ge_atTop 1] with i hi hi1
    have hp := hA.pos (Nat.one_le_two_pow (n := i))
    have hlog : Real.log ((2 ^ i : ℕ) : ℝ) = i * Real.log 2 := by
      push_cast; rw [Real.log_pow]
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp, hlog,
      abs_of_nonneg (by positivity)] at hi
    have hi0 : (0 : ℝ) < i := by exact_mod_cast hi1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (inv_pos.2 hi0),
      abs_of_pos (one_div_pos.2 hp)]
    rw [inv_eq_one_div, div_le_iff₀ hi0, mul_one_div, mul_comm, ← mul_div_assoc,
      le_div_iff₀ hp]
    linarith
  exact Real.not_summable_natCast_inv
    (summable_of_isBigO_nat (summable_inv_of_isCompetitive μ φ hA) hO')

end Podc.CollaborativeSearchPlane
