import Papers.PODC2026.OrderStatisticsPP.BiasedMedian
import Papers.PODC2026.OrderStatisticsPP.BetaBinomial

/-!
# Self-Excluding Median: Beta-Binomial fixation law (Theorem 8, Corollary 4)

Section 4.7: an agent `u` drawn u.a.r. samples three agents `a, b, d` u.a.r. (independently, with
replacement, possibly including `u`) and adopts `median(X_a, X_b, X_d)`.

* `selfExcludingMedian_fixation(_injective)` (**Theorem 8**): fixation on the `k`-th smallest
  opinion has probability `Γ(n+2)/(Γ(2n+1)Γ(n/2+1)²) · C(n-1,k-1) Γ(n/2+k) Γ(3n/2-k+1)`.
* `threeMajority_eq`, `threeMajority_fixation` (**Corollary 4**): binary 3-Majority with `n₁`
  agents holding `1` fixes on `1` with probability `P[X < n₁]`,
  `X ~ BetaBinomial(n-1, n/2+1, n/2+1)`.
-/

set_option linter.unusedSectionVars false

namespace OrderStatisticsPP

open Finset Matrix Filter Topology Cslib.Probability.Markov

variable {n : ℕ} {α : Type*} [LinearOrder α] [Fintype α]

/-- Uniform weights on the random choices `(u, a, b, d)`. -/
noncomputable def sxμ (n : ℕ) (_ : Fin n × Fin n × Fin n × Fin n) : ℝ := 1 / (n : ℝ) ^ 4

/-- **Self-Excluding Median dynamics** on the clique (Section 4.7). -/
noncomputable def selfExcludingMedian (n : ℕ) (α : Type*) [LinearOrder α] :
    Matrix (Config n α) (Config n α) ℝ :=
  randomMap (sxμ n) (fun ω c => Function.update c ω.1 (med3 (c ω.2.1) (c ω.2.2.1) (c ω.2.2.2)))

lemma sxμ_sum (hn : 0 < n) : ∑ ω, sxμ n ω = 1 := by
  unfold sxμ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  push_cast
  field_simp

lemma selfExcludingMedian_mem (hn : 0 < n) : selfExcludingMedian n α ∈ rowStochastic ℝ _ :=
  randomMap_mem_rowStochastic (μ := sxμ n) (fun _ => by unfold sxμ; positivity) (sxμ_sum hn) _

lemma selfExcludingMedian_absorbing (z : α) (s : Config n α) (hs : s ≠ const z) :
    selfExcludingMedian n α (const z) s = 0 :=
  randomMap_eq_zero_of_fixed (fun ω => by
    funext v; simp [const, med3_self, Function.update_apply]) hs

lemma selfExcludingMedian_reach (hn : 0 < n) (c : Config n α) :
    ∃ z, Relation.ReflTransGen (fun a b => 0 < selfExcludingMedian n α a b) c (const z) := by
  refine reach_const_of_step hn _ (fun c M hle hex hlt => ?_) c
  obtain ⟨t, ht⟩ := hex
  obtain ⟨u, hu⟩ := hlt
  refine ⟨u, hu, ?_⟩
  have := randomMap_pos (μ := sxμ n) (fun _ => by unfold sxμ; positivity)
    (fun ω (c : Config n α) => Function.update c ω.1 (med3 (c ω.2.1) (c ω.2.2.1) (c ω.2.2.2)))
    (ω := (u, t, t, t)) (by unfold sxμ; positivity) c
  unfold selfExcludingMedian
  simpa [med3_self, ht] using this

/-- `∑_{a,b,d} maj(I_a, I_b, I_d) = 3 n S² - 2 S³` for `0/1`-valued `I` with `S = ∑ I`. -/
lemma sum_maj (I : Fin n → ℝ) :
    ∑ a, ∑ b, ∑ d, (I a * I b + I b * I d + I a * I d - 2 * (I a * I b * I d)) =
      3 * n * (∑ a, I a) ^ 2 - 2 * (∑ a, I a) ^ 3 := by
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

lemma sum4 (k : ℝ) (f : Fin n → ℝ) (g : Fin n → Fin n → Fin n → ℝ) :
    ∑ u, ∑ a, ∑ b, ∑ d, k * (f u * g a b d) = k * (∑ u, f u) * (∑ a, ∑ b, ∑ d, g a b d) := by
  calc ∑ u, ∑ a, ∑ b, ∑ d, k * (f u * g a b d) = ∑ u, k * f u * ∑ a, ∑ b, ∑ d, g a b d := by
        refine Finset.sum_congr rfl fun u _ => ?_
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
          Finset.sum_congr rfl fun d _ => by ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

lemma sum3_one_sub (g : Fin n → Fin n → Fin n → ℝ) :
    ∑ a, ∑ b, ∑ d, (1 - g a b d) = (n : ℝ) ^ 3 - ∑ a, ∑ b, ∑ d, g a b d := by
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  ring

lemma sx_upMass {D : Set α} (hD : IsLowerSet D) (c : Config n α) :
    upMass (sxμ n) (fun ω _ => ω.1) (fun ω c => med3 (c ω.2.1) (c ω.2.2.1) (c ω.2.2.2))
      D c = 1 / (n : ℝ) ^ 4 * ((n : ℝ) - cnt D c) *
        (3 * n * (cnt D c : ℝ) ^ 2 - 2 * (cnt D c : ℝ) ^ 3) := by
  have hS : ∑ u, ind D (c u) = cnt D c := (cnt_eq_sum D c).symm
  have hM := sum_maj (fun u => ind D (c u))
  simp only [hS] at hM
  unfold upMass sxμ
  simp only [Fintype.sum_prod_type, ind_med3 hD]
  rw [sum4 (1 / (n : ℝ) ^ 4) (fun u => 1 - ind D (c u)) (fun a b d =>
    ind D (c a) * ind D (c b) + ind D (c b) * ind D (c d) + ind D (c a) * ind D (c d) -
      2 * (ind D (c a) * ind D (c b) * ind D (c d))), hM, sum_one_sub_ind]

lemma sx_downMass {D : Set α} (hD : IsLowerSet D) (c : Config n α) :
    downMass (sxμ n) (fun ω _ => ω.1)
      (fun ω c => med3 (c ω.2.1) (c ω.2.2.1) (c ω.2.2.2)) D c =
      1 / (n : ℝ) ^ 4 * (cnt D c : ℝ) *
        ((n : ℝ) ^ 3 - (3 * n * (cnt D c : ℝ) ^ 2 - 2 * (cnt D c : ℝ) ^ 3)) := by
  have hS : ∑ u, ind D (c u) = cnt D c := (cnt_eq_sum D c).symm
  have hM := sum_maj (fun u => ind D (c u))
  simp only [hS] at hM
  unfold downMass sxμ
  simp only [Fintype.sum_prod_type, ind_med3 hD]
  rw [sum4 (1 / (n : ℝ) ^ 4) (fun u => ind D (c u)) (fun a b d =>
    1 - (ind D (c a) * ind D (c b) + ind D (c b) * ind D (c d) + ind D (c a) * ind D (c d) -
      2 * (ind D (c a) * ind D (c b) * ind D (c d)))), hS, sum3_one_sub, hM]

lemma selfExcludingMedian_harmonic (hn : 0 < n) (D : Set α) (hD : IsLowerSet D) :
    selfExcludingMedian n α *ᵥ (fun c : Config n α => cumul (sxLaw n) (cnt D c)) =
      fun c => cumul (sxLaw n) (cnt D c) := by
  refine harmonic_of_balance (sxμ n) (sxμ_sum hn) (fun ω _ => ω.1)
    (fun ω c => med3 (c ω.2.1) (c ω.2.2.1) (c ω.2.2.2)) _ D ?_
  intro c
  rw [sx_upMass hD, sx_downMass hD]
  set m := cnt D c with hm
  have hmn : m ≤ n := cnt_le D c
  by_cases h0 : m = 0
  · rw [h0]; simp
  by_cases hn' : m = n
  · rw [hn']; ring
  have hr := sxLaw_ratio n m (by omega) (by omega)
  linear_combination (-(1 / (n : ℝ) ^ 4 * ((m : ℝ) * ((n : ℝ) - m)))) * hr

/-- **Theorem 8** (general initial configurations, ties summed). -/
theorem selfExcludingMedian_fixation (hn : 0 < n) (c : Config n α) (x : α) :
    Tendsto (fun t => (selfExcludingMedian n α ^ t) c (const x)) atTop
      (𝓝 (∑ k ∈ Ioc (cnt (Set.Iio x) c) (cnt (Set.Iic x) c), sxLaw n k)) :=
  fixation_of_harmonic (selfExcludingMedian_mem hn) hn _ (sum_sxLaw n hn)
    selfExcludingMedian_absorbing (selfExcludingMedian_reach hn)
    (fun D hD => selfExcludingMedian_harmonic hn D hD) c x

/-- **Theorem 8.** The Self-Excluding Median dynamics on the clique converges to the `k`-th
smallest initial value with probability
`Γ(n+2) / (Γ(2n+1) Γ(n/2+1)²) · C(n-1, k-1) Γ(n/2+k) Γ(3n/2-k+1)` (distinct initial values). -/
theorem selfExcludingMedian_fixation_injective (hn : 0 < n) (c : Config n α)
    (hc : Function.Injective c) (u : Fin n) :
    Tendsto (fun t => (selfExcludingMedian n α ^ t) c (const (c u))) atTop
      (𝓝 (Real.Gamma (n + 2) / (Real.Gamma (2 * n + 1) * Real.Gamma (n / 2 + 1) ^ 2) *
        ((Nat.choose (n - 1) (rank c (c u) - 1) : ℝ) * Real.Gamma (n / 2 + rank c (c u)) *
          Real.Gamma (3 * n / 2 - rank c (c u) + 1)))) :=
  fixation_of_harmonic_injective (selfExcludingMedian_mem hn) hn _ (sum_sxLaw n hn)
    selfExcludingMedian_absorbing (selfExcludingMedian_reach hn)
    (fun D hD => selfExcludingMedian_harmonic hn D hD) c hc u

/-! ### Corollary 4: 3-Majority -/

/-- **3-Majority** on binary opinions: an agent drawn u.a.r. samples three agents u.a.r.
(independently, with replacement) and adopts the majority opinion among the three samples. -/
noncomputable def threeMajority (n : ℕ) : Matrix (Config n Bool) (Config n Bool) ℝ :=
  randomMap (sxμ n) (fun ω c => Function.update c ω.1
    (if c ω.2.1 = c ω.2.2.1 then c ω.2.1 else c ω.2.2.2))

/-- On binary opinions, 3-Majority *is* the Self-Excluding Median dynamics. -/
theorem threeMajority_eq : threeMajority n = selfExcludingMedian n Bool := by
  have h : ∀ a b d : Bool, med3 a b d = if a = b then a else d := by decide
  unfold threeMajority selfExcludingMedian
  simp_rw [h]

/-- **Corollary 4.** Binary 3-Majority on the clique with `n₁` agents initially holding `1`
(`true`) converges to `1` with probability `P[X < n₁]`,
`X ~ BetaBinomial(n-1, n/2+1, n/2+1)`. -/
theorem threeMajority_fixation (hn : 0 < n) (c : Config n Bool) :
    Tendsto (fun t => (threeMajority n ^ t) c (const true)) atTop
      (𝓝 (∑ x ∈ range (univ.filter fun u => c u = true).card,
        betaBinomial (n - 1) (n / 2 + 1) (n / 2 + 1) x)) := by
  rw [threeMajority_eq]
  have h := selfExcludingMedian_fixation (α := Bool) hn c true
  set n₁ := (univ.filter fun u => c u = true).card
  have hIic : cnt (Set.Iic true) c = n := (cnt_eq_n_iff _ c).mpr fun u => by simp
  have hIio : cnt (Set.Iio true) c = n - n₁ := by
    rw [cnt_eq_card]
    have := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun u => c u = true)
    simp only [Finset.card_univ, Fintype.card_fin] at this
    have e : (univ.filter fun u => c u ∈ Set.Iio true) = univ.filter fun u => ¬ c u = true := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Set.mem_Iio]
      generalize c u = b
      cases b <;> decide
    rw [e]; omega
  rw [hIic, hIio] at h
  convert h using 2
  have hn₁ : n₁ ≤ n := by
    simpa using Finset.card_filter_le (univ : Finset (Fin n)) (fun u => c u = true)
  refine Finset.sum_nbij' (fun x => n - x) (fun k => n - k) ?_ ?_ ?_ ?_ ?_
  · intro x hx; simp only [Finset.mem_range] at hx; simp only [Finset.mem_Ioc]; omega
  · intro k hk; simp only [Finset.mem_Ioc] at hk; simp only [Finset.mem_range]; omega
  · intro x hx; simp only [Finset.mem_range] at hx; omega
  · intro k hk; simp only [Finset.mem_Ioc] at hk; omega
  · intro x hx
    simp only [Finset.mem_range] at hx
    rw [sxLaw_eq_betaBinomial n (n - x) hn (by omega) (by omega),
      show n - x - 1 = n - 1 - x by omega, betaBinomial_symm _ _ _ (by omega)]

end OrderStatisticsPP
