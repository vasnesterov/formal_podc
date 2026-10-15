import Papers.PODC2026.OrderStatisticsPP.CopyOrMax

/-!
# Biased-Median dynamics: binomial fixation law (Theorem 2, Corollary 3)

Section 4.5: an agent `u` is drawn uniformly at random and samples two agents `v, s`
(independently and uniformly, `v = s` and `v = u` allowed; this is what Lemma 4.8's counts
`2(n-j)+1` and `2j-1` correspond to). With `m = median(X_u, X_v, X_s)`:
* if `m > X_u`, set `X_u ← m`;
* otherwise, with probability `p/(1-p)` set `X_u ← m`.
Here `p ∈ (0, 1/2]`. The Median dynamics is `p = 1/2`.

* `biasedMedian_fixation`, `biasedMedian_fixation_injective` (**Theorem 2**): fixation on the
  `k`-th smallest opinion has probability `C(n-1, k-1) p^(n-k) (1-p)^(k-1)`.
* `twoChoices_eq_median`, `twoChoices_fixation` (**Corollary 3**): binary 2-Choices with `n₁`
  agents holding `1` (`true`) fixes on `1` with probability `P[X < n₁]`, `X ~ Bin(n-1, 1/2)`.
-/

set_option linter.unusedSectionVars false

namespace OrderStatisticsPP

open Finset Matrix Filter Topology Cslib.Probability.Markov

variable {n : ℕ} {α : Type*} [LinearOrder α] [Fintype α]

/-! ### The binomial law -/

/-- The shifted binomial law on ranks `1, …, n`: `π_k = C(n-1, k-1) p^(n-k) (1-p)^(k-1)`. -/
noncomputable def binomLaw (n : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  (Nat.choose (n - 1) (k - 1) : ℝ) * p ^ (n - k) * (1 - p) ^ (k - 1)

lemma cumul_binomLaw (p : ℝ) (hn : 0 < n) : cumul (binomLaw n p) n = 1 := by
  rw [cumul_eq_sum_range]
  obtain ⟨N, rfl⟩ : ∃ N, n = N + 1 := ⟨n - 1, by omega⟩
  have h := add_pow (1 - p) p N
  rw [show (1 - p) + p = 1 by ring, one_pow] at h
  rw [h]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj := Finset.mem_range.mp hj
  unfold binomLaw
  simp only [Nat.add_sub_cancel]
  rw [show N + 1 - (j + 1) = N - j by omega]
  ring

lemma binomLaw_balance {p : ℝ} (hp1 : p < 1) {m : ℕ} (hm : 1 ≤ m) (hmn : m + 1 ≤ n) :
    binomLaw n p (m + 1) * (p / (1 - p)) * m = binomLaw n p m * (n - m : ℕ) := by
  unfold binomLaw
  have h1p : (1 - p) ≠ 0 := by linarith
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hc := Nat.choose_succ_right_eq (n - 1) k
  have hc' : ((n - 1).choose (k + 1) : ℝ) * (k + 1) = ((n - 1).choose k : ℝ) * (n - (k + 1) : ℕ) := by
    rw [show n - (k + 1) = n - 1 - k by omega]
    exact_mod_cast hc
  simp only [Nat.add_sub_cancel]
  have e1 : (1 - p) ^ (k + 1) * (p / (1 - p)) = (1 - p) ^ k * p := by
    rw [pow_succ]; field_simp
  have e2 : p ^ (n - (k + 1)) = p ^ (n - (k + 1 + 1)) * p := by
    rw [← pow_succ]; congr 1; omega
  rw [e2]
  push_cast
  calc ((n - 1).choose (k + 1) : ℝ) * p ^ (n - (k + 1 + 1)) * (1 - p) ^ (k + 1) * (p / (1 - p)) *
        ((k : ℝ) + 1)
      = (((n - 1).choose (k + 1) : ℝ) * ((k : ℝ) + 1)) *
          (p ^ (n - (k + 1 + 1)) * ((1 - p) ^ (k + 1) * (p / (1 - p)))) := by ring
    _ = (((n - 1).choose k : ℝ) * (n - (k + 1) : ℕ)) *
          (p ^ (n - (k + 1 + 1)) * ((1 - p) ^ k * p)) := by rw [hc', e1]
    _ = _ := by ring

lemma binomLaw_pos {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {k : ℕ} (hk : k ≤ n) :
    0 < binomLaw n p k := by
  unfold binomLaw
  have : 0 < ((n - 1).choose (k - 1) : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega)
  have : 0 < 1 - p := by linarith
  positivity

/-! ### The dynamics -/

/-- Weights of the random choices `(u, v, s, coin)`; `coin` succeeds with probability `p/(1-p)`. -/
noncomputable def bmμ (n : ℕ) (p : ℝ) (ω : Fin n × Fin n × Fin n × Bool) : ℝ :=
  1 / (n : ℝ) ^ 3 * (if ω.2.2.2 then p / (1 - p) else 1 - p / (1 - p))

/-- New opinion of the activated agent `ω.1`. -/
def bmNew (c : Config n α) (ω : Fin n × Fin n × Fin n × Bool) : α :=
  if c ω.1 < med3 (c ω.1) (c ω.2.1) (c ω.2.2.1) ∨ ω.2.2.2 then
    med3 (c ω.1) (c ω.2.1) (c ω.2.2.1) else c ω.1

/-- **Biased-Median dynamics** on the clique (Section 4.5). -/
noncomputable def biasedMedian (n : ℕ) (α : Type*) [LinearOrder α] (p : ℝ) :
    Matrix (Config n α) (Config n α) ℝ :=
  randomMap (bmμ n p) (fun ω c => Function.update c ω.1 (bmNew c ω))

variable {p : ℝ}

lemma bmμ_nonneg (hp0 : 0 < p) (hp : p ≤ 1 / 2) (ω : Fin n × Fin n × Fin n × Bool) :
    0 ≤ bmμ n p ω := by
  unfold bmμ
  have h1 : 0 < 1 - p := by linarith
  have h2 : p / (1 - p) ≤ 1 := by rw [div_le_one h1]; linarith
  refine mul_nonneg (by positivity) ?_
  split_ifs
  · exact div_nonneg hp0.le h1.le
  · linarith

lemma bmμ_sum (hn : 0 < n) : ∑ ω, bmμ n p ω = 1 := by
  unfold bmμ
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  simp only [← mul_add, add_sub_cancel, mul_one, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  have : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

lemma biasedMedian_mem (hn : 0 < n) (hp0 : 0 < p) (hp : p ≤ 1 / 2) :
    biasedMedian n α p ∈ rowStochastic ℝ _ :=
  randomMap_mem_rowStochastic (bmμ_nonneg hp0 hp) (bmμ_sum hn) _

lemma biasedMedian_absorbing (z : α) (s : Config n α) (hs : s ≠ const z) :
    biasedMedian n α p (const z) s = 0 :=
  randomMap_eq_zero_of_fixed (fun ω => by
    funext v; simp [bmNew, const, med3_self, Function.update_apply]) hs

lemma biasedMedian_reach (hn : 0 < n) (hp0 : 0 < p) (hp : p ≤ 1 / 2) (c : Config n α) :
    ∃ z, Relation.ReflTransGen (fun a b => 0 < biasedMedian n α p a b) c (const z) := by
  refine reach_const_of_step hn _ (fun c M hle hex hlt => ?_) c
  obtain ⟨t, ht⟩ := hex
  obtain ⟨u, hu⟩ := hlt
  refine ⟨u, hu, ?_⟩
  have h1 : 0 < 1 - p := by linarith
  have := randomMap_pos (bmμ_nonneg hp0 hp)
    (fun ω (c : Config n α) => Function.update c ω.1 (bmNew c ω))
    (ω := (u, t, t, true)) (by unfold bmμ; simp only [ite_true]; positivity) c
  unfold biasedMedian
  have hm : med3 (c u) (c t) (c t) = M := by rw [ht]; exact med3_eq_of_eq (hle u)
  simpa [bmNew, hm, hu] using this

/-- Per-choice contributions of the Biased-Median dynamics to the up/down probabilities. -/
lemma bm_up_term {D : Set α} (hD : IsLowerSet D) (c : Config n α)
    (ω : Fin n × Fin n × Fin n × Bool) :
    (1 - ind D (c ω.1)) * ind D (bmNew c ω) =
      (if ω.2.2.2 then 1 else 0) * ((1 - ind D (c ω.1)) * (ind D (c ω.2.1) * ind D (c ω.2.2.1))) := by
  obtain ⟨u, v, s, b⟩ := ω
  simp only [bmNew]
  by_cases hu : c u ∈ D
  · simp [ind_mem hu]
  · have hm : med3 (c u) (c v) (c s) ∈ D ↔ c v ∈ D ∧ c s ∈ D := by
      rw [med3_mem_iff hD]; tauto
    by_cases hms : med3 (c u) (c v) (c s) ∈ D
    · have hnlt : ¬ c u < med3 (c u) (c v) (c s) := fun h => hu (hD h.le hms)
      obtain ⟨hv, hs⟩ := hm.mp hms
      cases b <;> simp [hnlt, ind_mem, ind_not_mem, hu, hms, hv, hs]
    · have hvs : ¬ (c v ∈ D ∧ c s ∈ D) := fun h => hms (hm.mpr h)
      have : ind D (c v) * ind D (c s) = 0 := by
        by_cases hv : c v ∈ D
        · rw [ind_not_mem (fun hs => hvs ⟨hv, hs⟩)]; ring
        · rw [ind_not_mem hv]; ring
      rw [this]
      split_ifs <;> simp [ind_not_mem, hu, hms]

lemma bm_down_term {D : Set α} (hD : IsLowerSet D) (c : Config n α)
    (ω : Fin n × Fin n × Fin n × Bool) :
    ind D (c ω.1) * (1 - ind D (bmNew c ω)) =
      ind D (c ω.1) * ((1 - ind D (c ω.2.1)) * (1 - ind D (c ω.2.2.1))) := by
  obtain ⟨u, v, s, b⟩ := ω
  simp only [bmNew]
  by_cases hu : c u ∈ D
  · have hm : med3 (c u) (c v) (c s) ∈ D ↔ c v ∈ D ∨ c s ∈ D := by
      rw [med3_mem_iff hD]; tauto
    by_cases hms : med3 (c u) (c v) (c s) ∈ D
    · have : (1 - ind D (c v)) * (1 - ind D (c s)) = 0 := by
        rcases hm.mp hms with h | h <;> simp [ind_mem h]
      rw [this]
      split_ifs <;> simp [ind_mem, hu, hms]
    · have hlt : c u < med3 (c u) (c v) (c s) := lt_of_not_ge fun h => hms (hD h hu)
      have hv : c v ∉ D := fun h => hms (hm.mpr (Or.inl h))
      have hs : c s ∉ D := fun h => hms (hm.mpr (Or.inr h))
      simp [hlt, ind_mem hu, ind_not_mem hms, ind_not_mem hv, ind_not_mem hs]
  · simp [ind_not_mem hu]

/-- `∑_u ∑_v ∑_s f u * (g v * h s) = (∑ f) (∑ g) (∑ h)`. -/
lemma sum_triple (f g h : Fin n → ℝ) :
    ∑ u, ∑ v, ∑ s, f u * (g v * h s) = (∑ u, f u) * ((∑ v, g v) * (∑ s, h s)) := by
  simp_rw [Finset.sum_mul, Finset.mul_sum]

lemma sum_one_sub_ind (D : Set α) (c : Config n α) :
    ∑ u, (1 - ind D (c u)) = (n : ℝ) - cnt D c := by
  rw [Finset.sum_sub_distrib, cnt_eq_sum]; simp

/-- Up/down probabilities of the Biased-Median dynamics for a lower set `D`. -/
lemma bm_upMass {D : Set α} (hD : IsLowerSet D) (c : Config n α) :
    upMass (bmμ n p) (fun ω _ => ω.1) (fun ω c => bmNew c ω) D c =
      1 / (n : ℝ) ^ 3 * (p / (1 - p)) * (((n : ℝ) - cnt D c) * ((cnt D c : ℝ) * cnt D c)) := by
  unfold upMass
  simp_rw [bm_up_term hD c]
  unfold bmμ
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  rw [← sum_one_sub_ind, cnt_eq_sum, ← sum_triple, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- Up/down probabilities of the Biased-Median dynamics for a lower set `D`. -/
lemma bm_downMass {D : Set α} (hD : IsLowerSet D) (c : Config n α) :
    downMass (bmμ n p) (fun ω _ => ω.1) (fun ω c => bmNew c ω) D c =
      1 / (n : ℝ) ^ 3 * ((cnt D c : ℝ) * (((n : ℝ) - cnt D c) * ((n : ℝ) - cnt D c))) := by
  unfold downMass
  simp_rw [bm_down_term hD c]
  unfold bmμ
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  rw [← sum_one_sub_ind, cnt_eq_sum, ← sum_triple, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

lemma biasedMedian_harmonic (hn : 0 < n) (hp1 : p < 1) (D : Set α) (hD : IsLowerSet D) :
    biasedMedian n α p *ᵥ (fun c : Config n α => cumul (binomLaw n p) (cnt D c)) =
      fun c => cumul (binomLaw n p) (cnt D c) := by
  refine harmonic_of_balance (bmμ n p) (bmμ_sum hn) (fun ω _ => ω.1)
    (fun ω c => bmNew c ω) _ D ?_
  intro c
  rw [bm_upMass hD, bm_downMass hD]
  set m := cnt D c with hm
  have hmn : m ≤ n := cnt_le D c
  by_cases h0 : m = 0
  · rw [h0]; simp
  by_cases hn' : m = n
  · rw [hn']; simp
  have hb := binomLaw_balance (n := n) hp1 (m := m) (by omega) (by omega)
  rw [Nat.cast_sub hmn] at hb
  linear_combination (1 / (n : ℝ) ^ 3 * ((m : ℝ) * ((n : ℝ) - m))) * hb

/-- **Theorem 2** (general initial configurations, ties summed): the Biased-Median dynamics with
`p ∈ (0, 1/2]` fixes on `x` with probability `∑ C(n-1, k-1) p^(n-k) (1-p)^(k-1)` over the ranks
`k` of `x`. -/
theorem biasedMedian_fixation (hn : 0 < n) (hp0 : 0 < p) (hp : p ≤ 1 / 2) (c : Config n α)
    (x : α) :
    Tendsto (fun t => (biasedMedian n α p ^ t) c (const x)) atTop
      (𝓝 (∑ k ∈ Ioc (cnt (Set.Iio x) c) (cnt (Set.Iic x) c), binomLaw n p k)) :=
  fixation_of_harmonic (biasedMedian_mem hn hp0 hp) hn _ (cumul_binomLaw p hn)
    biasedMedian_absorbing (biasedMedian_reach hn hp0 hp)
    (fun D hD => biasedMedian_harmonic hn (by linarith) D hD) c x

/-- **Theorem 2.** The Biased-Median dynamics of parameter `p ∈ (0, 1/2]` on the clique converges
to the `k`-th smallest initial value with probability `C(n-1, k-1) p^(n-k) (1-p)^(k-1)`
(distinct initial values). For `p = 1/2` (Median dynamics): `C(n-1, k-1) 2^-(n-1)`. -/
theorem biasedMedian_fixation_injective (hn : 0 < n) (hp0 : 0 < p) (hp : p ≤ 1 / 2)
    (c : Config n α) (hc : Function.Injective c) (u : Fin n) :
    Tendsto (fun t => (biasedMedian n α p ^ t) c (const (c u))) atTop
      (𝓝 ((Nat.choose (n - 1) (rank c (c u) - 1) : ℝ) * p ^ (n - rank c (c u)) *
        (1 - p) ^ (rank c (c u) - 1))) :=
  fixation_of_harmonic_injective (biasedMedian_mem hn hp0 hp) hn _ (cumul_binomLaw p hn)
    biasedMedian_absorbing (biasedMedian_reach hn hp0 hp)
    (fun D hD => biasedMedian_harmonic hn (by linarith) D hD) c hc u

/-! ### Corollary 3: 2-Choices -/

/-- **2-Choices** on binary opinions (`Bool`, `false < true`): an agent `u` drawn u.a.r. samples
two agents `v, s` u.a.r. (independently, with replacement) and adopts their opinion if they agree. -/
noncomputable def twoChoices (n : ℕ) : Matrix (Config n Bool) (Config n Bool) ℝ :=
  randomMap (fun _ : Fin n × Fin n × Fin n => 1 / (n : ℝ) ^ 3)
    (fun ω c => Function.update c ω.1 (if c ω.2.1 = c ω.2.2 then c ω.2.1 else c ω.1))

lemma med3_bool (a b c : Bool) : med3 a b c = if b = c then b else a := by
  cases a <;> cases b <;> cases c <;> rfl

/-- On binary opinions, 2-Choices *is* the Median dynamics (Biased-Median with `p = 1/2`). -/
theorem twoChoices_eq_median : twoChoices n = biasedMedian n Bool (1 / 2) := by
  ext c c'
  unfold twoChoices biasedMedian randomMap bmμ
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, ite_true, Bool.false_eq_true, ite_false]
  norm_num
  refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun v _ =>
    Finset.sum_congr rfl fun s _ => ?_
  simp [bmNew, med3_bool]

/-- **Corollary 3.** Binary 2-Choices on the clique with `n₁` agents initially holding `1`
(`true`) converges to `1` with probability `P[X < n₁]`, `X ~ Bin(n-1, 1/2)`. -/
theorem twoChoices_fixation (hn : 0 < n) (c : Config n Bool) :
    Tendsto (fun t => (twoChoices n ^ t) c (const true)) atTop
      (𝓝 (∑ x ∈ range (univ.filter fun u => c u = true).card,
        (Nat.choose (n - 1) x : ℝ) * (1 / 2) ^ (n - 1))) := by
  rw [twoChoices_eq_median]
  have h := biasedMedian_fixation (α := Bool) hn (by norm_num) le_rfl c true
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
    unfold binomLaw
    rw [show n - (n - x) = x by omega, show n - x - 1 = n - 1 - x by omega,
      Nat.choose_symm (by omega), show 1 - (1 / 2 : ℝ) = 1 / 2 by norm_num, mul_assoc, ← pow_add,
      show x + (n - 1 - x) = n - 1 by omega]

end OrderStatisticsPP
