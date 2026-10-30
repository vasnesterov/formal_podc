import Papers.PODC2026.MultiKrumRobustness.Defs

/-!
# Upper bounds on the robustness coefficient of MultiKrum (Sections 3.1 and 4)

* `sum_norm_sub_sq` — parallel-axis identity `∑_A ‖x_i - y‖² = |A| Σ_A + |A| ‖x̄_A - y‖²`.
* `lemma_1`, `lemma_1_self` — **Lemma 1** (mean-variance relation).
* `young` — **Lemma A.1**; `norm_sum_sq_le` — **Lemma A.2** (Jensen, uniform weights).
* `lemma_2` — **Lemma 2**, `lemma_3` — **Lemma 3**.
* `theorem_5`, `theorem_6` — **Theorems 5 and 6**, and `theorem_1` — **Theorem 1**
  (`m`-MultiKrum is robust with `κ⋆_m ≤ (n-f)/(n-2f) · min((√2+1)², κ^>_2(m))`).
* `theorem_1_as_written_false` — the displayed inequality (1) of Theorem 1 has `≥` instead of `≤`;
  as written it fails (e.g. `f = 0`, `m = n = 2`).
-/

open Finset

namespace Podc.MultiKrumRobustness

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}

/-! ### Elementary relations (Section 4.1 and Appendix A) -/

lemma card_smul_mean (x : Fin n → E) {A : Finset (Fin n)} (hA : A.Nonempty) :
    (A.card : ℝ) • mean x A = ∑ i ∈ A, x i := by
  unfold mean
  rw [smul_smul, mul_inv_cancel₀ (by exact_mod_cast hA.card_pos.ne'), one_smul]

lemma sum_sub_mean (x : Fin n → E) (A : Finset (Fin n)) :
    ∑ i ∈ A, (x i - mean x A) = 0 := by
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  rw [sum_sub_distrib, sum_const, ← card_smul_mean x hA, ← Nat.cast_smul_eq_nsmul ℝ, sub_self]

-- CSLib candidate (general inner-product-space identity/inequality)
/-- Parallel-axis identity: `∑_{i ∈ A} ‖x_i - y‖² = |A| Σ_A + |A| ‖x̄_A - y‖²`. -/
lemma sum_norm_sub_sq (x : Fin n → E) (A : Finset (Fin n)) (y : E) :
    ∑ i ∈ A, ‖x i - y‖ ^ 2 = A.card * variance x A + A.card * ‖mean x A - y‖ ^ 2 := by
  have h1 : ∀ i, ‖x i - y‖ ^ 2 = ‖x i - mean x A‖ ^ 2 + 2 * inner ℝ (x i - mean x A)
      (mean x A - y) + ‖mean x A - y‖ ^ 2 := fun i => by
    rw [← norm_add_sq_real]; congr 1; abel_nf
  simp_rw [h1, sum_add_distrib, ← mul_sum, ← sum_inner, sum_sub_mean, inner_zero_left, mul_zero,
    add_zero, sum_const, nsmul_eq_mul]
  congr 1
  unfold variance
  rcases A.eq_empty_or_nonempty with rfl | hA
  · simp
  rw [← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast hA.card_pos.ne'), one_mul]

lemma card_mul_variance (x : Fin n → E) (A : Finset (Fin n)) :
    A.card * variance x A = ∑ i ∈ A, ‖x i - mean x A‖ ^ 2 := by
  have := sum_norm_sub_sq x A (mean x A)
  simpa using this.symm

-- CSLib candidate (general inner-product-space identity/inequality)
/-- **Lemma 1** (mean-variance relation): for nonempty `A, B`,
`(ab)⁻¹ ∑_{i∈A} ∑_{j∈B} ‖x_i - x_j‖² = ‖x̄_A - x̄_B‖² + Σ_A + Σ_B`. -/
theorem lemma_1 (x : Fin n → E) {A B : Finset (Fin n)} (hA : A.Nonempty) (hB : B.Nonempty) :
    (∑ i ∈ A, ∑ j ∈ B, ‖x i - x j‖ ^ 2) / (A.card * B.card) =
      ‖mean x A - mean x B‖ ^ 2 + variance x A + variance x B := by
  have ha : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hb : (0 : ℝ) < B.card := by exact_mod_cast hB.card_pos
  rw [sum_comm]
  simp_rw [sum_norm_sub_sq x A, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
  have : ∑ j ∈ B, ‖mean x A - x j‖ ^ 2 = ∑ j ∈ B, ‖x j - mean x A‖ ^ 2 := by
    simp_rw [norm_sub_rev (mean x A)]
  rw [this, sum_norm_sub_sq x B, norm_sub_rev (mean x B)]
  field_simp
  ring

/-- **Lemma 1** for `A = B`: `∑_{i,j ∈ A} ‖x_i - x_j‖² = 2 |A|² Σ_A`. -/
theorem lemma_1_self (x : Fin n → E) (A : Finset (Fin n)) :
    ∑ i ∈ A, ∑ j ∈ A, ‖x i - x j‖ ^ 2 = 2 * (A.card : ℝ) ^ 2 * variance x A := by
  rw [sum_comm]
  simp_rw [sum_norm_sub_sq x A, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum]
  have : ∑ j ∈ A, ‖mean x A - x j‖ ^ 2 = ∑ j ∈ A, ‖x j - mean x A‖ ^ 2 := by
    simp_rw [norm_sub_rev (mean x A)]
  rw [this, sum_norm_sub_sq x A, sub_self, norm_zero]
  ring

-- CSLib candidate (general inner-product-space identity/inequality)
/-- **Lemma A.1** (Young): `‖a + b‖² ≤ (1 + α) ‖a‖² + (1 + 1/α) ‖b‖²` for `α > 0`. -/
theorem young (a b : E) {α : ℝ} (hα : 0 < α) :
    ‖a + b‖ ^ 2 ≤ (1 + α) * ‖a‖ ^ 2 + (1 + 1 / α) * ‖b‖ ^ 2 := by
  rw [norm_add_sq_real]
  have h1 := real_inner_le_norm a b
  have h2 : 2 * (‖a‖ * ‖b‖) ≤ α * ‖a‖ ^ 2 + 1 / α * ‖b‖ ^ 2 := by
    rw [← sub_nonneg]
    have : α * ‖a‖ ^ 2 + 1 / α * ‖b‖ ^ 2 - 2 * (‖a‖ * ‖b‖) = (α * ‖a‖ - ‖b‖) ^ 2 / α := by
      field_simp; ring
    rw [this]; positivity
  nlinarith

-- CSLib candidate (general inner-product-space identity/inequality)
omit [InnerProductSpace ℝ E] in
/-- **Lemma A.2** (Jensen, uniform weights): `‖∑_T v_i‖² ≤ |T| ∑_T ‖v_i‖²`. -/
theorem norm_sum_sq_le {ι : Type*} (T : Finset ι) (v : ι → E) :
    ‖∑ i ∈ T, v i‖ ^ 2 ≤ T.card * ∑ i ∈ T, ‖v i‖ ^ 2 := by
  calc ‖∑ i ∈ T, v i‖ ^ 2 ≤ (∑ i ∈ T, ‖v i‖) ^ 2 := by
        gcongr; exact norm_sum_le _ _
    _ ≤ T.card * ∑ i ∈ T, ‖v i‖ ^ 2 := sq_sum_le_card_mul_sum_sq

/-- Jensen for means: `‖x̄_T - y‖² ≤ |T|⁻¹ ∑_T ‖x_i - y‖²`. -/
lemma norm_mean_sub_sq_le (x : Fin n → E) {T : Finset (Fin n)} (hT : T.Nonempty) (y : E) :
    ‖mean x T - y‖ ^ 2 ≤ (T.card : ℝ)⁻¹ * ∑ i ∈ T, ‖x i - y‖ ^ 2 := by
  have hc : (0 : ℝ) < T.card := by exact_mod_cast hT.card_pos
  rw [sum_norm_sub_sq, le_inv_mul_iff₀ hc]
  nlinarith [variance_nonneg x T]

/-! ### The two key lemmas (Section 4.2) -/

section keyLemmas

variable {f m : ℕ} (x : Fin n → E)

omit [InnerProductSpace ℝ E] in
/-- The average over the `m` smallest scores is at most the average over any set of `≥ m`
indices. -/
lemma card_mul_sum_selection_le {S Sm : Finset (Fin n)} (hsel : IsSelection f m x Sm)
    (hmS : m ≤ S.card) :
    (S.card : ℝ) * ∑ i ∈ Sm, score f x (x i) ≤ m * ∑ i ∈ S, score f x (x i) := by
  set s : Fin n → ℝ := fun i => score f x (x i)
  rcases Sm.eq_empty_or_nonempty with hE | hne
  · have : m = 0 := by rw [← hsel.1, hE, card_empty]
    subst this; simp [hE]
  set M := Sm.sup' hne s
  have hle : ∀ i ∈ Sm, s i ≤ M := fun i hi => le_sup' s hi
  have hge : ∀ j ∉ Sm, M ≤ s j := fun j hj => by
    rw [sup'_le_iff]; exact fun i hi => hsel.2 i hi j hj
  set k := (S ∩ Sm).card
  have s1 := sum_inter_add_sum_sdiff Sm S s
  have s2 := sum_inter_add_sum_sdiff S Sm s
  rw [inter_comm] at s1
  have c1 := card_inter_add_card_sdiff Sm S
  have c2 := card_inter_add_card_sdiff S Sm
  rw [inter_comm] at c1
  rw [hsel.1] at c1
  have hP : ∑ i ∈ S ∩ Sm, s i ≤ k * M := by
    rw [← nsmul_eq_mul]; exact sum_le_card_nsmul _ _ _ fun i hi => hle i (mem_inter.1 hi).2
  have hA : ∑ i ∈ Sm \ S, s i ≤ (Sm \ S).card * M := by
    rw [← nsmul_eq_mul]; exact sum_le_card_nsmul _ _ _ fun i hi => hle i (mem_sdiff.1 hi).1
  have hB : ((S \ Sm).card : ℝ) * M ≤ ∑ i ∈ S \ Sm, s i := by
    rw [← nsmul_eq_mul]; exact card_nsmul_le_sum _ _ _ fun i hi => hge i (mem_sdiff.1 hi).2
  have e1 : ((Sm \ S).card : ℝ) = m - k := by
    have : (Sm \ S).card = m - k := by omega
    rw [this, Nat.cast_sub (by omega)]
  have e2 : ((S \ Sm).card : ℝ) = S.card - k := by
    have : (S \ Sm).card = S.card - k := by omega
    rw [this, Nat.cast_sub (by omega)]
  rw [e1] at hA
  rw [e2] at hB
  have hkm : (k : ℝ) ≤ m := by exact_mod_cast (show k ≤ m by omega)
  have hmS' : (m : ℝ) ≤ S.card := by exact_mod_cast hmS
  rw [← s1, ← s2]
  nlinarith [mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg (α := ℝ) S.card),
    mul_le_mul_of_nonneg_left hB (Nat.cast_nonneg (α := ℝ) m),
    mul_le_mul_of_nonneg_left hP (sub_nonneg.2 hmS')]

/-- Sum of the scores over a set `S` of `n - f` indices: `∑_{i ∈ S} s(x_i) ≤ 2 |S| Σ_S`
(Eq. (5)). -/
lemma sum_score_le {S : Finset (Fin n)} (hS : S.card = n - f) :
    ∑ i ∈ S, score f x (x i) ≤ 2 * S.card * variance x S := by
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  have hc : (0 : ℝ) < S.card := by exact_mod_cast hne.card_pos
  have h1 : ∀ i ∈ S, score f x (x i) ≤ (S.card : ℝ)⁻¹ * ∑ j ∈ S, ‖x i - x j‖ ^ 2 := by
    intro i _
    unfold score
    rw [← hS]
    exact mul_le_mul_of_nonneg_left (nearestSum_le x _ rfl) (by positivity)
  calc ∑ i ∈ S, score f x (x i) ≤ ∑ i ∈ S, (S.card : ℝ)⁻¹ * ∑ j ∈ S, ‖x i - x j‖ ^ 2 :=
        sum_le_sum h1
    _ = (S.card : ℝ)⁻¹ * (2 * (S.card : ℝ) ^ 2 * variance x S) := by
        rw [← mul_sum, lemma_1_self]
    _ = 2 * S.card * variance x S := by field_simp

/-- **Lemma 2**: `∑_{i ∈ S⋆_m} s(x_i) ≤ 2 m Σ_S` for every `S` with `|S| = n - f`
(i.e. `m⁻¹ ∑_{S⋆_m} s(x_i) ≤ 2 Σ_S`). -/
theorem lemma_2 (hf : f < n) (hm : m ≤ n - f) {S Sm : Finset (Fin n)} (hS : S.card = n - f)
    (hsel : IsSelection f m x Sm) :
    ∑ i ∈ Sm, score f x (x i) ≤ 2 * m * variance x S := by
  have h1 := card_mul_sum_selection_le x hsel (hS ▸ hm)
  have h2 := sum_score_le x hS
  have hc : (0 : ℝ) < S.card := by rw [hS]; exact_mod_cast Nat.sub_pos_of_lt hf
  have h3 : (S.card : ℝ) * ∑ i ∈ Sm, score f x (x i) ≤ S.card * (2 * m * variance x S) := by
    calc _ ≤ _ := h1
      _ ≤ (m : ℝ) * (2 * S.card * variance x S) := mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = _ := by ring
  exact le_of_mul_le_mul_left h3 hc

/-- **Lemma 3**: for every `y` and `α > 0`,
`‖y - x̄_S‖² ≤ (n-f)/(n-2f) ((1+α) s(y) + (1 + 1/α) Σ_S)`. -/
theorem lemma_3 (hf : 2 * f < n) {S : Finset (Fin n)} (hS : S.card = n - f) (y : E) {α : ℝ}
    (hα : 0 < α) :
    ‖y - mean x S‖ ^ 2 ≤ ((n : ℝ) - f) / ((n : ℝ) - 2 * f) *
      ((1 + α) * score f x y + (1 + 1 / α) * variance x S) := by
  obtain ⟨N, hN, hNsum⟩ := exists_nearestSum_eq x (Nat.sub_le n f) y
  set U := S ∩ N
  have hU : n - 2 * f ≤ U.card := by
    have e1 := card_union_add_card_inter S N
    have e2 : (S ∪ N).card ≤ n := by simpa using card_le_univ (S ∪ N)
    have e3 : U.card = (S ∩ N).card := rfl
    omega
  have hnf : ((n - f : ℕ) : ℝ) = (n : ℝ) - f := by rw [Nat.cast_sub (by omega)]
  have hn2f : ((n - 2 * f : ℕ) : ℝ) = (n : ℝ) - 2 * f := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hUpos : (0 : ℝ) < (n : ℝ) - 2 * f := by
    rw [← hn2f]; exact_mod_cast (show 0 < n - 2 * f by omega)
  have hUc : (n : ℝ) - 2 * f ≤ U.card := by rw [← hn2f]; exact_mod_cast hU
  have hnfpos : (0 : ℝ) < (n : ℝ) - f := by linarith
  -- `|U| ‖y - x̄_S‖² ≤ (1+α) ∑_N ‖y - x_j‖² + (1 + 1/α) ∑_S ‖x_j - x̄_S‖²`
  have key : (U.card : ℝ) * ‖y - mean x S‖ ^ 2 ≤
      (1 + α) * ∑ j ∈ N, ‖y - x j‖ ^ 2 + (1 + 1 / α) * ∑ j ∈ S, ‖x j - mean x S‖ ^ 2 := by
    have : (U.card : ℝ) * ‖y - mean x S‖ ^ 2 = ∑ j ∈ U, ‖(y - x j) + (x j - mean x S)‖ ^ 2 := by
      simp
    rw [this]
    calc ∑ j ∈ U, ‖(y - x j) + (x j - mean x S)‖ ^ 2
        ≤ ∑ j ∈ U, ((1 + α) * ‖y - x j‖ ^ 2 + (1 + 1 / α) * ‖x j - mean x S‖ ^ 2) :=
          sum_le_sum fun j _ => young _ _ hα
      _ = (1 + α) * ∑ j ∈ U, ‖y - x j‖ ^ 2 + (1 + 1 / α) * ∑ j ∈ U, ‖x j - mean x S‖ ^ 2 := by
          rw [sum_add_distrib, mul_sum, mul_sum]
      _ ≤ _ := by
          gcongr
          · exact inter_subset_right
          · exact inter_subset_left
  have hsc : ∑ j ∈ N, ‖y - x j‖ ^ 2 = ((n : ℝ) - f) * score f x y := by
    unfold score; rw [← hNsum, hnf]; field_simp
  have hvar : ∑ j ∈ S, ‖x j - mean x S‖ ^ 2 = ((n : ℝ) - f) * variance x S := by
    rw [← card_mul_variance, hS, hnf]
  rw [hsc, hvar] at key
  have hQ : 0 ≤ (1 + α) * score f x y + (1 + 1 / α) * variance x S := by
    have := score_nonneg f x y; have := variance_nonneg x S; positivity
  rw [div_mul_eq_mul_div, le_div_iff₀ hUpos]
  have : ‖y - mean x S‖ ^ 2 * ((n : ℝ) - 2 * f) ≤ (U.card : ℝ) * ‖y - mean x S‖ ^ 2 := by
    rw [mul_comm]; exact mul_le_mul_of_nonneg_right hUc (by positivity)
  nlinarith

end keyLemmas

/-! ### Theorems 5, 6 and 1 (Section 4.3) -/

section bounds

variable {f m : ℕ} (x : Fin n → E)

lemma mean_sub_mean_eq {S Sm : Finset (Fin n)} (hm : Sm.card = m) (hm0 : 0 < m) :
    mean x Sm - mean x S = (m : ℝ)⁻¹ • ∑ i ∈ Sm, (x i - mean x S) := by
  have hne : Sm.Nonempty := card_pos.1 (hm ▸ hm0)
  rw [sum_sub_distrib, sum_const, smul_sub, ← card_smul_mean x hne, hm, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hm0.ne'), one_smul, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    inv_mul_cancel₀ (by exact_mod_cast hm0.ne'), one_smul]

/-- Pointwise form of **Theorem 5**: `‖x̄_{S⋆_m} - x̄_S‖² ≤ (√2+1)² (n-f)/(n-2f) Σ_S`. -/
theorem bias_le_theorem_5 (hf : 2 * f < n) (hm0 : 0 < m) (hm : m ≤ n - f)
    {S Sm : Finset (Fin n)} (hS : S.card = n - f) (hsel : IsSelection f m x Sm) :
    ‖mean x Sm - mean x S‖ ^ 2 ≤ cKrum * (((n : ℝ) - f) / ((n : ℝ) - 2 * f)) * variance x S := by
  have hne : Sm.Nonempty := card_pos.1 (hsel.1 ▸ hm0)
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  set α : ℝ := 1 / Real.sqrt 2
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs2p : 0 < Real.sqrt 2 := by positivity
  have hα : 0 < α := by positivity
  set K := ((n : ℝ) - f) / ((n : ℝ) - 2 * f)
  have hK : 0 ≤ K := by
    have : (2 * f : ℝ) < n := by exact_mod_cast hf
    apply div_nonneg <;> linarith
  have h1 := norm_mean_sub_sq_le x hne (mean x S)
  rw [hsel.1] at h1
  have h2 : ∑ i ∈ Sm, ‖x i - mean x S‖ ^ 2 ≤
      ∑ i ∈ Sm, K * ((1 + α) * score f x (x i) + (1 + 1 / α) * variance x S) :=
    sum_le_sum fun i _ => lemma_3 x hf hS (x i) hα
  rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_const, hsel.1, nsmul_eq_mul] at h2
  have h3 := lemma_2 x (by omega) hm hS hsel
  have hv := variance_nonneg x S
  have hcK : cKrum = 3 + 2 * α + 1 / α := by
    simp only [cKrum, α]; field_simp; nlinarith
  rw [hcK]
  -- combine
  have h4 : (m : ℝ)⁻¹ * ∑ i ∈ Sm, ‖x i - mean x S‖ ^ 2 ≤
      K * ((1 + α) * 2 * variance x S + (1 + 1 / α) * variance x S) := by
    rw [inv_mul_le_iff₀ hmR]
    calc ∑ i ∈ Sm, ‖x i - mean x S‖ ^ 2 ≤ _ := h2
      _ ≤ K * ((1 + α) * (2 * m * variance x S) + m * ((1 + 1 / α) * variance x S)) := by
          gcongr
      _ = _ := by ring
  calc ‖mean x Sm - mean x S‖ ^ 2 ≤ _ := h1
    _ ≤ _ := h4
    _ = _ := by ring

/-- **Theorem 5**: `κ⋆_m ≤ κ₁ = (√2+1)² (n-f)/(n-2f)` for `n - 2f > 0`, `0 < m ≤ n - f`. -/
theorem theorem_5 (hf : 2 * f < n) (hm0 : 0 < m) (hm : m ≤ n - f) {F : (Fin n → E) → E}
    (hF : IsMultiKrum f m F) :
    kappaStar f F ≤ ((cKrum * (((n : ℝ) - f) / ((n : ℝ) - 2 * f)) : ℝ) : EReal) := by
  rw [kappaStar_le_iff]
  intro x S hS
  obtain ⟨Sm, hsel, hFx⟩ := hF x
  rw [hFx]
  exact bias_le_theorem_5 x hf hm0 hm hS hsel

/-- The minimised bracket in the proof of Theorem 6:
`(1+α) 2m + (1+1/α) u = (√(2m) + √u)²` for `α = √u/√(2m)`. -/
private lemma bracket_eq {p q : ℝ} (hp : 0 < p) (hq : 0 < q) :
    (1 + q / p) * p ^ 2 + (1 + 1 / (q / p)) * q ^ 2 = (p + q) ^ 2 := by
  field_simp; ring

/-- Pointwise form of **Theorem 6**, with `u_max = min(m, f)`:
`‖x̄_{S⋆_m} - x̄_S‖² ≤ (n-f)/(n-2f) (√(n-2f)/√m + √(2 u_max)/√m + u_max/m)² Σ_S`. -/
theorem bias_le_theorem_6 (hf : 2 * f < n) (hm0 : 0 < m) (hm : m ≤ n - f)
    {S Sm : Finset (Fin n)} (hS : S.card = n - f) (hsel : IsSelection f m x Sm) :
    ‖mean x Sm - mean x S‖ ^ 2 ≤ ((n : ℝ) - f) / ((n : ℝ) - 2 * f) *
      (Real.sqrt ((n : ℝ) - 2 * f) / Real.sqrt m + Real.sqrt (2 * (min m f : ℕ)) / Real.sqrt m +
        ((min m f : ℕ) : ℝ) / m) ^ 2 * variance x S := by
  set u : ℕ := min m f
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hfR : (2 * f : ℝ) < n := by exact_mod_cast hf
  have hn2f : (0 : ℝ) < (n : ℝ) - 2 * f := by linarith
  have hnf : (0 : ℝ) < (n : ℝ) - f := by linarith
  set K := ((n : ℝ) - f) / ((n : ℝ) - 2 * f)
  have hK : 0 ≤ K := by positivity
  set V := variance x S
  have hv : 0 ≤ V := variance_nonneg x S
  set d : Fin n → E := fun i => x i - mean x S
  set u' := (Sm \ S).card
  have hu'u : u' ≤ u := by
    refine le_min ?_ ?_
    · rw [← hsel.1]; exact card_le_card sdiff_subset
    · have : (Sm \ S).card ≤ (univ \ S).card := card_le_card (sdiff_subset_sdiff (subset_univ _)
          le_rfl)
      rw [card_univ_sdiff, Fintype.card_fin, hS] at this
      omega
  -- the honest part
  have hA : ‖∑ i ∈ Sm ∩ S, d i‖ ≤ Real.sqrt (m * ((n : ℝ) - f)) * Real.sqrt V := by
    rw [← Real.sqrt_mul (by positivity)]
    apply Real.le_sqrt_of_sq_le
    have hv' : (Sm ∩ S).card ≤ m := hsel.1 ▸ card_le_card inter_subset_left
    calc ‖∑ i ∈ Sm ∩ S, d i‖ ^ 2 ≤ (Sm ∩ S).card * ∑ i ∈ Sm ∩ S, ‖d i‖ ^ 2 := norm_sum_sq_le _ _
      _ ≤ m * ∑ i ∈ S, ‖d i‖ ^ 2 := by
          gcongr
          exact inter_subset_right
      _ = m * ((n : ℝ) - f) * V := by
          simp only [d]
          rw [← card_mul_variance, hS, Nat.cast_sub (by omega)]; ring
  -- the Byzantine part
  have hB : ‖∑ i ∈ Sm \ S, d i‖ ≤
      Real.sqrt (u * K) * (Real.sqrt (2 * m) + Real.sqrt u) * Real.sqrt V := by
    rcases Nat.eq_zero_or_pos u' with h0 | hpos
    · rw [card_eq_zero.1 h0, sum_empty, norm_zero]; positivity
    set p := Real.sqrt (2 * m)
    set q := Real.sqrt u'
    have hp : 0 < p := by positivity
    have hq : 0 < q := Real.sqrt_pos.2 (by exact_mod_cast hpos)
    have hp2 : p ^ 2 = 2 * m := Real.sq_sqrt (by positivity)
    have hq2 : q ^ 2 = u' := Real.sq_sqrt (by positivity)
    have hα : 0 < q / p := by positivity
    have hsc : ∑ i ∈ Sm \ S, score f x (x i) ≤ 2 * m * V :=
      le_trans (sum_le_sum_of_subset_of_nonneg sdiff_subset fun _ _ _ => score_nonneg _ _ _)
        (lemma_2 x (by omega) hm hS hsel)
    have h1 : ‖∑ i ∈ Sm \ S, d i‖ ^ 2 ≤ u' * K * (p + q) ^ 2 * V := by
      calc ‖∑ i ∈ Sm \ S, d i‖ ^ 2 ≤ u' * ∑ i ∈ Sm \ S, ‖d i‖ ^ 2 := norm_sum_sq_le _ _
        _ ≤ u' * ∑ i ∈ Sm \ S,
              K * ((1 + q / p) * score f x (x i) + (1 + 1 / (q / p)) * V) := by
            gcongr with i
            exact lemma_3 x hf hS (x i) hα
        _ = u' * K * ((1 + q / p) * ∑ i ∈ Sm \ S, score f x (x i) + (1 + 1 / (q / p)) * u' * V)
            := by
            rw [← mul_sum, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]; ring
        _ ≤ u' * K * ((1 + q / p) * (2 * m * V) + (1 + 1 / (q / p)) * u' * V) := by
            gcongr
        _ = u' * K * ((1 + q / p) * p ^ 2 + (1 + 1 / (q / p)) * q ^ 2) * V := by
            rw [hp2, hq2]; ring
        _ = u' * K * (p + q) ^ 2 * V := by rw [bracket_eq hp hq]
    have hu'R : (u' : ℝ) ≤ u := by exact_mod_cast hu'u
    have hq' : q ≤ Real.sqrt u := Real.sqrt_le_sqrt hu'R
    have h2 : u' * K * (p + q) ^ 2 * V ≤
        (Real.sqrt (u * K) * (p + Real.sqrt u) * Real.sqrt V) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt hv]
      gcongr
    apply le_of_sq_le_sq _ (by positivity)
    exact h1.trans h2
  -- combine
  have hsum : (m : ℝ) • (mean x Sm - mean x S) = ∑ i ∈ Sm ∩ S, d i + ∑ i ∈ Sm \ S, d i := by
    rw [mean_sub_mean_eq x hsel.1 hm0, smul_smul, mul_inv_cancel₀ hmR.ne', one_smul,
      sum_inter_add_sum_sdiff]
  have hnorm : (m : ℝ) * ‖mean x Sm - mean x S‖ ≤
      (Real.sqrt (m * ((n : ℝ) - f)) + Real.sqrt (u * K) * (Real.sqrt (2 * m) + Real.sqrt u)) *
        Real.sqrt V := by
    have := congrArg norm hsum
    rw [norm_smul, Real.norm_of_nonneg hmR.le] at this
    rw [this]
    calc _ ≤ ‖∑ i ∈ Sm ∩ S, d i‖ + ‖∑ i ∈ Sm \ S, d i‖ := norm_add_le _ _
      _ ≤ _ := by linarith
  -- algebra
  set a := Real.sqrt m
  set b := Real.sqrt ((n : ℝ) - 2 * f)
  set c := Real.sqrt ((n : ℝ) - f)
  set r := Real.sqrt (u : ℝ)
  have ha : 0 < a := Real.sqrt_pos.2 hmR
  have hb : 0 < b := Real.sqrt_pos.2 hn2f
  have hc : 0 < c := Real.sqrt_pos.2 hnf
  have ha2 : a ^ 2 = m := Real.sq_sqrt hmR.le
  have hb2 : b ^ 2 = (n : ℝ) - 2 * f := Real.sq_sqrt hn2f.le
  have hc2 : c ^ 2 = (n : ℝ) - f := Real.sq_sqrt hnf.le
  have hr2 : r ^ 2 = u := Real.sq_sqrt (by positivity)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have e1 : Real.sqrt (m * ((n : ℝ) - f)) = a * c := Real.sqrt_mul hmR.le _
  have e2 : Real.sqrt (u * K) = r * c / b := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_div' _ hn2f.le]; ring
  have e3 : Real.sqrt (2 * m) = Real.sqrt 2 * a := Real.sqrt_mul (by norm_num) _
  have e4 : Real.sqrt (2 * (u : ℝ)) = Real.sqrt 2 * r := Real.sqrt_mul (by norm_num) _
  have hK' : K = c ^ 2 / b ^ 2 := by rw [hc2, hb2]
  rw [e1, e2, e3] at hnorm
  rw [e4, hK', ← ha2]
  set W := a * c + r * c / b * (Real.sqrt 2 * a + r)
  have hW : 0 ≤ W := by positivity
  have hz : ‖mean x Sm - mean x S‖ ≤ W * Real.sqrt V / a ^ 2 := by
    rw [le_div_iff₀ (by positivity), mul_comm, ha2]; exact hnorm
  have hz2 : ‖mean x Sm - mean x S‖ ^ 2 ≤ (W * Real.sqrt V / a ^ 2) ^ 2 := by
    gcongr
  calc _ ≤ _ := hz2
    _ = W ^ 2 / a ^ 4 * V := by
        rw [div_pow, mul_pow, Real.sq_sqrt hv]; ring
    _ = _ := by
        congr 1
        simp only [W]
        rw [← hr2]
        field_simp
        ring

/-- **Theorem 6**: `κ⋆_m ≤ κ₂(m) = (n-f)/(n-2f) κ^<_2(m)` if `m ≤ f`, `(n-f)/(n-2f) κ^>_2(m)`
otherwise. -/
theorem theorem_6 (hf : 2 * f < n) (hm0 : 0 < m) (hm : m ≤ n - f) {F : (Fin n → E) → E}
    (hF : IsMultiKrum f m F) :
    kappaStar f F ≤ (((n : ℝ) - f) / ((n : ℝ) - 2 * f) *
      (if m ≤ f then kappaLt n f m else kappaGt n f m) : ℝ) := by
  rw [kappaStar_le_iff]
  intro x S hS
  obtain ⟨Sm, hsel, hFx⟩ := hF x
  rw [hFx]
  have h := bias_le_theorem_6 x hf hm0 hm hS hsel
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  split_ifs with hmf
  · rw [min_eq_left hmf] at h
    convert h using 3
    unfold kappaLt
    congr 1
    rw [Real.sqrt_mul (by norm_num), mul_div_assoc, div_self (Real.sqrt_pos.2 hmR).ne',
      div_self hmR.ne']
    ring
  · rw [min_eq_right (by omega)] at h
    exact h

/-- `κ^>_2(m) ≥ (√2+1)²` for `0 < m ≤ f`. -/
lemma cKrum_le_kappaGt (hm0 : 0 < m) (hmf : m ≤ f) :
    cKrum ≤ kappaGt n f m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hmfR : (m : ℝ) ≤ f := by exact_mod_cast hmf
  unfold cKrum kappaGt
  have h1 : Real.sqrt 2 ≤ Real.sqrt (2 * f) / Real.sqrt m := by
    rw [le_div_iff₀ (Real.sqrt_pos.2 hmR), ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have h2 : 1 ≤ (f : ℝ) / m := by rw [le_div_iff₀ hmR]; linarith
  have h3 : 0 ≤ Real.sqrt ((n : ℝ) - 2 * f) / Real.sqrt m := by positivity
  gcongr
  linarith

/-- **Theorem 1**: for `n - 2f > 0` and `0 < m ≤ n - f`, `m`-MultiKrum is robust and
`κ⋆_m ≤ (n-f)/(n-2f) · min((√2+1)², κ^>_2(m))`. (The paper prints `≥` in display (1); the text and
the proof make clear that an upper bound is meant, see `theorem_1_as_written_false`.) -/
theorem theorem_1 (hf : 2 * f < n) (hm0 : 0 < m) (hm : m ≤ n - f) {F : (Fin n → E) → E}
    (hF : IsMultiKrum f m F) :
    IsRobust f F ∧
      kappaStar f F ≤ (((n : ℝ) - f) / ((n : ℝ) - 2 * f) * min cKrum (kappaGt n f m) : ℝ) := by
  have hbound : kappaStar f F ≤ (((n : ℝ) - f) / ((n : ℝ) - 2 * f) * min cKrum (kappaGt n f m) :
      ℝ) := by
    rcases le_or_gt m f with hmf | hmf
    · rw [min_eq_left (cKrum_le_kappaGt (n := n) hm0 hmf), mul_comm]
      exact theorem_5 hf hm0 hm hF
    · rcases le_total cKrum (kappaGt n f m) with h | h
      · rw [min_eq_left h, mul_comm]; exact theorem_5 hf hm0 hm hF
      · rw [min_eq_right h]
        have := theorem_6 hf hm0 hm hF
        simpa only [show ¬ m ≤ f by omega, ↓reduceIte] using this
  exact ⟨lt_of_le_of_lt hbound (EReal.coe_lt_top _), hbound⟩

/-- Display (1) of Theorem 1 is printed with `≥`. Read literally it is false: for `f = 0` and
`m = n ≥ 1`, `n`-MultiKrum is the plain mean, `κ⋆ ≤ 0`, while the right-hand side equals
`min((√2+1)², 1) = 1`. (A typo: the surrounding text and the proof give an upper bound,
`theorem_1`.) -/
theorem theorem_1_as_written_false (hn : 0 < n) {F : (Fin n → E) → E} (hF : IsMultiKrum 0 n F) :
    ¬ ((((n : ℝ) - (0 : ℕ)) / ((n : ℝ) - 2 * (0 : ℕ)) * min cKrum (kappaGt n (0 : ℕ) n) : ℝ) :
        EReal) ≤ kappaStar 0 F := by
  have hle : kappaStar 0 F ≤ ((0 : ℝ) : EReal) := by
    rw [kappaStar_le_iff]
    intro x S hS
    obtain ⟨Sm, hsel, hFx⟩ := hF x
    have h1 : Sm = univ := eq_univ_of_card _ (by rw [hsel.1, Fintype.card_fin])
    have h2 : S = univ := eq_univ_of_card _ (by rw [hS, Fintype.card_fin, Nat.sub_zero])
    rw [hFx, h1, h2]; simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : kappaGt n (0 : ℕ) n = 1 := by
    unfold kappaGt
    simp [div_self (Real.sqrt_pos.2 hnR).ne']
  have hC : 1 ≤ cKrum := by unfold cKrum; nlinarith [Real.sqrt_nonneg 2]
  rw [hk, min_eq_right hC]
  intro h
  have := h.trans hle
  simp [div_self hnR.ne'] at this
  exact absurd this (by norm_num)

end bounds

end Podc.MultiKrumRobustness
