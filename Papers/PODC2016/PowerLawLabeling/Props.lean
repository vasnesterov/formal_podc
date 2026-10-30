import Papers.PODC2016.PowerLawLabeling.Zeta

/-!
# Propositions 1–3: properties of `α`-proper power-law graphs
-/

namespace Podc.PowerLawLabeling

open Finset

variable {α : ℝ}

section Helpers

variable {n : ℕ} (G : SimpleGraph (Fin n))

theorem deg_eq_degree [DecidableRel G.Adj] (v : Fin n) : deg G v = G.degree v := by
  unfold deg
  rw [← G.card_neighborSet_eq_degree, Set.ncard_eq_toFinset_card', Set.toFinset_card]

theorem deg_lt (v : Fin n) : deg G v < n := by
  classical
  rw [deg_eq_degree]
  simpa using G.degree_lt_card_verts v

theorem numDeg_eq_zero {i : ℕ} (hi : n ≤ i) : numDeg G i = 0 := by
  unfold numDeg
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro v _
  have := deg_lt G v
  omega

theorem sum_numDeg (s : Finset ℕ) : ∑ i ∈ s, numDeg G i = #{v | deg G v ∈ s} := by
  unfold numDeg
  rw [Finset.card_eq_sum_card_fiberwise (f := deg G) (t := s) (fun x hx => by simpa using hx)]
  refine Finset.sum_congr rfl fun i hi => ?_
  congr 1
  ext v
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h; exact ⟨h ▸ hi, h⟩
  · exact fun h => h.2

theorem exists_of_numDeg_ne_zero {i : ℕ} (h : numDeg G i ≠ 0) : ∃ v, deg G v = i := by
  unfold numDeg at h
  obtain ⟨v, hv⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  exact ⟨v, (Finset.mem_filter.mp hv).2⟩

theorem one_le_numDeg_deg (v : Fin n) : 1 ≤ numDeg G (deg G v) := by
  unfold numDeg
  exact Finset.card_pos.mpr ⟨v, by simp⟩

variable {G}

/-- Monotonicity of `|V_i|` from `anti`, for `2 ≤ i ≤ j ≤ n`. -/
theorem numDeg_anti (hG : IsProperPowerLaw α G) {i j : ℕ} (hi : 2 ≤ i) (hij : i ≤ j)
    (hj : j ≤ n) : numDeg G j ≤ numDeg G i := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih =>
    have := hG.anti j (by omega) (by simp only [Fintype.card_fin]; omega)
    exact this.trans (ih (by omega))

/-- Upper bound `|V_i| ≤ C n / i^α + 1` (`+ 2` for `i = 2`). -/
theorem numDeg_le (hα : 1 < α) (hG : IsProperPowerLaw α G) {i : ℕ} (hi : 1 ≤ i) :
    (numDeg G i : ℝ) ≤ C α * n / (i : ℝ) ^ α + (if i = 2 then 2 else 1) := by
  have hC := (C_pos hα).le
  have hx : 0 ≤ C α * n / (i : ℝ) ^ α := by positivity
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · have h := hG.one_upper
    simp only [Fintype.card_fin] at h
    have h' : (numDeg G 1 : ℝ) ≤ ⌈C α * n⌉₊ := by exact_mod_cast h
    have := Nat.ceil_lt_add_one (show 0 ≤ C α * n by positivity)
    simp only [Nat.cast_one, Real.one_rpow, div_one, show (1:ℕ) ≠ 2 by norm_num, ↓reduceIte]
    linarith
  · have h := hG.two_upper
    simp only [Fintype.card_fin] at h
    have h' : (numDeg G 2 : ℝ) ≤ ⌈C α * n / (2:ℝ) ^ α⌉₊ + 1 := by exact_mod_cast h
    have := Nat.ceil_lt_add_one (show 0 ≤ C α * n / (2:ℝ) ^ α by positivity)
    simp only [Nat.cast_ofNat, ↓reduceIte]
    linarith
  · simp only [show i ≠ 2 by omega, ↓reduceIte]
    by_cases hin : i ≤ n
    · have h := hG.mid i h3 (by simpa using hin)
      simp only [Fintype.card_fin] at h
      have h1 := Nat.floor_le hx
      have h2 := Nat.ceil_lt_add_one hx
      rcases h with h | h <;> rw [h] <;> linarith
    · rw [numDeg_eq_zero G (by omega)]
      simp only [Nat.cast_zero]
      linarith

/-- Lower bound `|V_i| ≥ C n / i^α - 1` (`- i₁ - 2` for `i = 1`), for `1 ≤ i ≤ n`. -/
theorem numDeg_ge (hG : IsProperPowerLaw α G) {i : ℕ} (hi : 1 ≤ i) (hin : i ≤ n) :
    C α * n * (i : ℝ) ^ (-α) - 1 - (if i = 1 then (i₁ α n : ℝ) + 1 else 0) ≤ numDeg G i := by
  have hi0 : (0:ℝ) ≤ i := Nat.cast_nonneg i
  rw [Real.rpow_neg hi0, ← div_eq_mul_inv]
  rcases (show i = 1 ∨ i = 2 ∨ 3 ≤ i by omega) with rfl | rfl | h3
  · have h := hG.one_lower
    simp only [Fintype.card_fin] at h
    have h' : ((⌊C α * n⌋₊ : ℤ) : ℝ) - (i₁ α n : ℤ) - 1 ≤ ((numDeg G 1 : ℤ) : ℝ) := by
      exact_mod_cast h
    push_cast at h'
    have := Nat.lt_floor_add_one (C α * n)
    simp only [Nat.cast_one, Real.one_rpow, div_one, ↓reduceIte]
    linarith
  · have h := hG.two_lower
    simp only [Fintype.card_fin] at h
    have h' : (⌊C α * n / (2:ℝ) ^ α⌋₊ : ℝ) ≤ numDeg G 2 := by exact_mod_cast h
    have := Nat.lt_floor_add_one (C α * n / (2:ℝ) ^ α)
    simp only [Nat.cast_ofNat, show (2:ℕ) ≠ 1 by norm_num, ↓reduceIte]
    linarith
  · simp only [show i ≠ 1 by omega, ↓reduceIte]
    have h := hG.mid i h3 (by simpa using hin)
    simp only [Fintype.card_fin] at h
    have h1 := Nat.lt_floor_add_one (C α * n / (i:ℝ) ^ α)
    have h2 : (⌊C α * n / (i:ℝ) ^ α⌋₊ : ℝ) ≤ ⌈C α * n / (i:ℝ) ^ α⌉₊ := by
      exact_mod_cast Nat.floor_le_ceil _
    rcases h with h | h <;> rw [h] <;> linarith

end Helpers

/-- **Proposition 1.** The maximum degree of an `n`-vertex graph in `P'_α` is at most
`(C/(α-1) + 2) n^{1/α} + i₁ + 3`. -/
theorem prop1 (hα : 1 < α) {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (hG : IsProperPowerLaw α G) (v : Fin n) :
    (deg G v : ℝ) ≤ (C α / (α - 1) + 2) * (n : ℝ) ^ (1 / α) + i₁ α n + 3 := by
  classical
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hα0 : 0 < α := by linarith
  have hC := C_pos hα
  set r := (n:ℝ) ^ (1 / α) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hn' (by positivity)
  have hrn : r ≤ n := by
    calc r ≤ (n:ℝ) ^ (1:ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hn' (by rw [div_le_one hα0]; linarith)
      _ = n := Real.rpow_one _
  set k := ⌈r⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr (by
    rw [hk, ne_eq, Nat.ceil_eq_zero, not_le]; linarith)
  have hkn : k ≤ n := Nat.ceil_le.mpr (by simpa using hrn)
  have hkr : r ≤ k := Nat.le_ceil r
  have hkr' : (k:ℝ) < r + 1 := Nat.ceil_lt_add_one (by linarith)
  -- `n k^{1-α} ≤ n^{1/α}`
  have htail : (n:ℝ) * (k:ℝ) ^ (1 - α) ≤ r := by
    have h1 : (k:ℝ) ^ (1 - α) ≤ r ^ (1 - α) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hkr (by linarith)
    have h2 : (n:ℝ) * r ^ (1 - α) = r := by
      rw [hr, ← Real.rpow_mul (by positivity)]
      conv_lhs => arg 1; rw [← Real.rpow_one (n:ℝ)]
      rw [← Real.rpow_add (by linarith)]
      congr 1
      field_simp
      ring
    calc _ ≤ (n:ℝ) * r ^ (1 - α) := by gcongr
      _ = r := h2
  -- `S = ∑_{i ≤ k} |V_i| ≥ n - C/(α-1) n^{1/α} - k - i₁ - 1`
  have hS : (n:ℝ) - C α / (α - 1) * r - k - i₁ α n - 1 ≤ ∑ i ∈ Icc 1 k, (numDeg G i : ℝ) := by
    have h1 := Finset.sum_le_sum (s := Icc 1 k) (fun i hi =>
      numDeg_ge hG (G := G) (Finset.mem_Icc.mp hi).1 ((Finset.mem_Icc.mp hi).2.trans hkn))
    rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_ite_eq'] at h1
    simp only [Finset.mem_Icc, le_refl, true_and, hk1, ↓reduceIte, Finset.sum_const,
      Nat.card_Icc, nsmul_eq_mul, mul_one] at h1
    have h3 := one_sub_C_mul_sum_Icc_le hα hk1
    have h4 : (n:ℝ) - C α * n * ∑ i ∈ Icc 1 k, (i : ℝ) ^ (-α) ≤ C α / (α - 1) * r := by
      have := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ n)
      have h5 : C α / (α - 1) * ((n:ℝ) * (k:ℝ) ^ (1 - α)) ≤ C α / (α - 1) * r := by
        apply mul_le_mul_of_nonneg_left htail
        exact div_nonneg hC.le (by linarith)
      calc _ = (n:ℝ) * (1 - C α * ∑ i ∈ Icc 1 k, (i : ℝ) ^ (-α)) := by ring
        _ ≤ _ := this
        _ = C α / (α - 1) * ((n:ℝ) * (k:ℝ) ^ (1 - α)) := by ring
        _ ≤ _ := h5
    have : ((k + 1 - 1 : ℕ) : ℝ) = k := by simp
    rw [this] at h1
    linarith
  -- vertices of degree `> k`
  have hcount : (#{w | k < deg G w} : ℝ) ≤ C α / (α - 1) * r + k + i₁ α n + 1 := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (fun w => deg G w ∈ Icc 1 k)
    have h2 : #{w | k < deg G w} ≤ #{w | ¬ deg G w ∈ Icc 1 k} := by
      apply Finset.card_le_card
      intro w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Icc]
      omega
    have h3 : (∑ i ∈ Icc 1 k, (numDeg G i : ℝ)) = #{w | deg G w ∈ Icc 1 k} := by
      rw [← sum_numDeg]; push_cast; rfl
    simp only [Finset.card_univ, Fintype.card_fin] at h1
    have h1' : (#{w | deg G w ∈ Icc 1 k} : ℝ) + #{w | ¬ deg G w ∈ Icc 1 k} = n := by
      exact_mod_cast h1
    have h2' : (#{w | k < deg G w} : ℝ) ≤ #{w | ¬ deg G w ∈ Icc 1 k} := by exact_mod_cast h2
    linarith
  have hi₁ : (0:ℝ) ≤ i₁ α n := Nat.cast_nonneg _
  have hCa : 0 ≤ C α / (α - 1) := div_nonneg hC.le (by linarith)
  by_cases hD : deg G v ≤ k
  · have : (deg G v : ℝ) ≤ k := by exact_mod_cast hD
    nlinarith
  · replace hD := not_le.mp hD
    -- every class `V_i`, `k < i ≤ deg v`, is nonempty
    have h1 : deg G v - k ≤ #{w | k < deg G w} := by
      have h2 : ∑ i ∈ Ioc k (deg G v), numDeg G i ≤ #{w | k < deg G w} := by
        rw [sum_numDeg]
        apply Finset.card_le_card
        intro w
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ioc]
        exact fun h => h.1
      refine le_trans ?_ h2
      have h3 : ∀ i ∈ Ioc k (deg G v), 1 ≤ numDeg G i := fun i hi => by
        rw [Finset.mem_Ioc] at hi
        exact (one_le_numDeg_deg G v).trans
          (numDeg_anti hG (by omega) hi.2 (deg_lt G v).le)
      have := Finset.card_nsmul_le_sum _ _ _ h3
      simpa using this
    have h1' : (deg G v : ℝ) - k ≤ #{w | k < deg G w} := by
      have : ((deg G v - k : ℕ) : ℝ) = deg G v - k := by
        rw [Nat.cast_sub hD.le]
      rw [← this]; exact_mod_cast h1
    nlinarith

/-- Corollary of Proposition 1: `deg v + 1 ≤ (C/(α-1) + 8) n^{1/α}`. -/
theorem deg_add_one_le (hα : 1 < α) {n : ℕ} (hn : 1 ≤ n) (G : SimpleGraph (Fin n))
    (hG : IsProperPowerLaw α G) (v : Fin n) :
    (deg G v : ℝ) + 1 ≤ (C α / (α - 1) + 8) * (n : ℝ) ^ (1 / α) := by
  have h1 := prop1 hα hn G hG v
  have h2 := i₁_le_rpow_add_one hα n
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hr1 : 1 ≤ (n : ℝ) ^ (1 / α) := Real.one_le_rpow hn' (by
    have : 0 < α := by linarith
    positivity)
  nlinarith

/-- **Proposition 2.** For `α > 2`, the graphs of `P'_α` are sparse: `|E| ≤ c n` for a constant
`c` depending only on `α`. -/
theorem prop2 (hα : 2 < α) : ∃ c : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    IsProperPowerLaw α G → Sparse c G := by
  have hα1 : 1 < α := by linarith
  set K := C α / (α - 1) + 8 with hK
  have hC := C_pos hα1
  have hz : 1 ≤ zeta (α - 1) := one_le_zeta (by linarith)
  refine ⟨C α * zeta (α - 1) + K ^ 2, fun n G hG => ?_⟩
  classical
  unfold Sparse
  rw [Fintype.card_fin]
  -- `2|E| = ∑_v deg v`
  have hE : 2 * (G.edgeSet.ncard : ℝ) = ∑ v, (deg G v : ℝ) := by
    have := G.sum_degrees_eq_twice_card_edges
    simp only [deg_eq_degree]
    rw [Set.ncard_eq_toFinset_card', ← SimpleGraph.edgeFinset]
    exact_mod_cast this.symm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Finset.univ_eq_empty, Finset.sum_empty] at hE
    simp only [CharP.cast_eq_zero, mul_zero]
    linarith
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hα0 : 0 < α := by linarith
  set r := (n:ℝ) ^ (1 / α) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hn' (by positivity)
  have hK0 : 0 ≤ K := by
    have : 0 ≤ C α / (α - 1) := div_nonneg hC.le (by linarith)
    linarith
  set M := ⌊K * r⌋₊ with hM
  have hMr : (M : ℝ) ≤ K * r := Nat.floor_le (by positivity)
  have hdeg : ∀ v, deg G v ∈ range (M + 1) := fun v => by
    rw [Finset.mem_range, Nat.lt_succ_iff, hM]
    apply Nat.le_floor
    have := deg_add_one_le hα1 hn G hG v
    linarith
  -- fiberwise sum
  have hsum : ∑ v, (deg G v : ℝ) = ∑ i ∈ range (M + 1), (i : ℝ) * numDeg G i := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := deg G) (t := range (M + 1))
      (fun v _ => hdeg v)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => (i : ℝ)) (fun v hv => by
      rw [(Finset.mem_filter.mp hv).2])]
    rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    rfl
  rw [hsum, Finset.sum_range_succ'] at hE
  simp only [CharP.cast_eq_zero, zero_mul, add_zero] at hE
  -- termwise bound
  have hterm : ∀ i ∈ range M, ((i + 1 : ℕ) : ℝ) * numDeg G (i + 1) ≤
      C α * n * (1 / ((i : ℝ) + 1) ^ (α - 1)) + 2 * M := by
    intro i hi
    rw [Finset.mem_range] at hi
    have h1 := numDeg_le hα1 hG (G := G) (i := i + 1) (by omega)
    have hi0 : (0:ℝ) < (i : ℝ) + 1 := by positivity
    have hiM : ((i + 1 : ℕ) : ℝ) ≤ M := by exact_mod_cast hi
    push_cast at h1 hiM ⊢
    have h3 : ((i : ℝ) + 1) * (C α * n / ((i : ℝ) + 1) ^ α) =
        C α * n * (1 / ((i : ℝ) + 1) ^ (α - 1)) := by
      rw [Real.rpow_sub_one hi0.ne']
      field_simp
    have h4 : 0 ≤ (numDeg G (i + 1) : ℝ) := Nat.cast_nonneg _
    calc ((i : ℝ) + 1) * numDeg G (i + 1)
        ≤ ((i : ℝ) + 1) * (C α * n / ((i : ℝ) + 1) ^ α + 2) := by
          apply mul_le_mul_of_nonneg_left _ hi0.le; split_ifs at h1 <;> linarith
      _ = C α * n * (1 / ((i : ℝ) + 1) ^ (α - 1)) + 2 * ((i : ℝ) + 1) := by rw [mul_add, h3]; ring
      _ ≤ _ := by linarith
  have h1 := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at h1
  have h2 : ∑ i ∈ range M, 1 / ((i : ℝ) + 1) ^ (α - 1) ≤ zeta (α - 1) :=
    Summable.sum_le_tsum _ (fun i _ => by positivity) (summable_zeta (by linarith))
  have h3 : C α * n * ∑ i ∈ range M, 1 / ((i : ℝ) + 1) ^ (α - 1) ≤ C α * n * zeta (α - 1) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  -- `M² ≤ K² n`
  have hr2 : r * r ≤ n := by
    have h5 : r ≤ (n : ℝ) ^ (1 / 2 : ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le hn'
      rw [div_le_div_iff₀ hα0 (by norm_num)]; linarith
    calc r * r ≤ (n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (1 / 2 : ℝ) := by
          apply mul_le_mul h5 h5 (by positivity) (by positivity)
      _ = n := by rw [← Real.rpow_add (by positivity)]; norm_num
  have hM2 : (M : ℝ) * M ≤ K ^ 2 * n := by
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg _
    calc (M : ℝ) * M ≤ (K * r) * (K * r) := mul_le_mul hMr hMr hM0 (by positivity)
      _ = K ^ 2 * (r * r) := by ring
      _ ≤ K ^ 2 * n := by gcongr
  have hCz : 0 ≤ C α * n * zeta (α - 1) := by
    have : 0 ≤ zeta (α - 1) := by linarith
    positivity
  nlinarith

/-- The constant for which we prove `P'_α ⊆ P_α` (the paper's constant plus `C`, see
`differencies.md`). -/
noncomputable def C'₀ (α : ℝ) : ℝ := (C α / (α - 1) + 8) ^ α + C α * α / (α - 1)

/-- **Proposition 3.** `P'_α ⊆ P_α` (for every constant `C' ≥ C'₀ α`). -/
theorem prop3 (hα : 1 < α) {C' : ℝ} (hC' : C'₀ α ≤ C') {n : ℕ} (G : SimpleGraph (Fin n))
    (hG : IsProperPowerLaw α G) : IsPowerLaw α C' G := by
  intro k hk1 _ hkn
  simp only [Fintype.card_fin] at hkn ⊢
  have hn : 1 ≤ n := by omega
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hα0 : 0 < α := by linarith
  have hC := C_pos hα
  set K := C α / (α - 1) + 8 with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ C α / (α - 1) := div_nonneg hC.le (by linarith)
    linarith
  set r := (n:ℝ) ^ (1 / α) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow hn' (by positivity)
  have hk1' : (1:ℝ) ≤ k := by exact_mod_cast hk1
  have hkα : 0 < (k : ℝ) ^ (α - 1) := Real.rpow_pos_of_pos (by linarith) _
  set Y := (n : ℝ) / (k : ℝ) ^ (α - 1) with hY
  have hY0 : 0 ≤ Y := by positivity
  have hC'₀ : 0 ≤ C'₀ α := by
    unfold C'₀
    have : 0 ≤ C α * α / (α - 1) := div_nonneg (by positivity) (by linarith)
    have : 0 ≤ (C α / (α - 1) + 8) ^ α := Real.rpow_nonneg hK0 _
    linarith
  suffices h : ((∑ i ∈ Icc k (n - 1), numDeg G i : ℕ) : ℝ) ≤ C'₀ α * Y from
    h.trans (mul_le_mul_of_nonneg_right hC' hY0)
  set s := Icc k (n - 1) with hs
  set t := s.filter (fun i => numDeg G i ≠ 0) with ht
  rw [← Finset.sum_filter_ne_zero, ← ht]
  rcases t.eq_empty_or_nonempty with he | ⟨i₀, hi₀⟩
  · rw [he, Finset.sum_empty, Nat.cast_zero]; positivity
  -- some vertex has degree `≥ k`, so `k + 1 ≤ K r`
  have hmemt : ∀ i ∈ t, k ≤ i ∧ (i : ℝ) + 1 ≤ K * r := by
    intro i hi
    rw [ht, Finset.mem_filter, hs, Finset.mem_Icc] at hi
    obtain ⟨v, hv⟩ := exists_of_numDeg_ne_zero G hi.2
    refine ⟨hi.1.1, ?_⟩
    rw [← hv]
    exact deg_add_one_le hα hn G hG v
  have hkK : (k : ℝ) ≤ K * r := by
    have := hmemt i₀ hi₀
    have : (k : ℝ) ≤ i₀ := by exact_mod_cast this.1
    linarith
  -- `#t + 1 ≤ K r`
  have hcard : (#t : ℝ) + 1 ≤ K * r := by
    set F := ⌊K * r⌋₊
    have hsub : t ⊆ Ico 1 F := fun i hi => by
      have h := hmemt i hi
      rw [Finset.mem_Ico]
      refine ⟨by omega, ?_⟩
      have : i + 1 ≤ F := Nat.le_floor (by push_cast; exact h.2)
      omega
    have h1 := Finset.card_le_card hsub
    rw [Nat.card_Ico] at h1
    have hF : 1 ≤ F := by
      have := hmemt i₀ hi₀
      have : i₀ + 1 ≤ F := Nat.le_floor (by push_cast; exact this.2)
      omega
    have h2 : #t + 1 ≤ F := by omega
    have h3 : ((#t + 1 : ℕ) : ℝ) ≤ F := by exact_mod_cast h2
    push_cast at h3
    exact h3.trans (Nat.floor_le (by positivity))
  -- `K r ≤ K^α Y`
  have hKr : K * r ≤ K ^ α * Y := by
    have hKr0 : 0 < K * r := by positivity
    have h1 : (k : ℝ) ^ (α - 1) ≤ (K * r) ^ (α - 1) :=
      Real.rpow_le_rpow (by positivity) hkK (by linarith)
    have h2 : (K * r) ^ α = K ^ α * n := by
      rw [Real.mul_rpow hK0 (by positivity), hr, ← Real.rpow_mul (by positivity),
        one_div_mul_cancel hα0.ne', Real.rpow_one]
    have h3 : (K * r) ^ (α - 1) * (K * r) = (K * r) ^ α := by
      rw [Real.rpow_sub_one hKr0.ne', div_mul_cancel₀ _ hKr0.ne']
    rw [hY, mul_div_assoc', le_div_iff₀ hkα, ← h2, ← h3, mul_comm]
    exact mul_le_mul_of_nonneg_right h1 hKr0.le
  -- termwise bound
  have hterm : ∀ i ∈ t, (numDeg G i : ℝ) ≤
      C α * n * (i : ℝ) ^ (-α) + 1 + (if i = 2 then 1 else 0) := by
    intro i hi
    have hi1 : 1 ≤ i := by have := (hmemt i hi).1; omega
    have h := numDeg_le hα hG (G := G) hi1
    rw [Real.rpow_neg (Nat.cast_nonneg _), ← div_eq_mul_inv]
    split_ifs at h ⊢ <;> linarith
  have h1 := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one,
    Finset.sum_ite_eq'] at h1
  have h2 : (if 2 ∈ t then (1:ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
  -- the power-law part
  have hsum : ∑ i ∈ t, C α * n * (i : ℝ) ^ (-α) ≤ C α * α / (α - 1) * Y := by
    have hts : t ⊆ insert k (Ioc k (n - 1)) := fun i hi => by
      have := (hmemt i hi).1
      have hi' := (Finset.mem_filter.mp hi).1
      rw [hs, Finset.mem_Icc] at hi'
      rw [Finset.mem_insert, Finset.mem_Ioc]
      omega
    have e1 := Finset.sum_le_sum_of_subset_of_nonneg hts
      (f := fun i : ℕ => C α * n * (i : ℝ) ^ (-α)) (fun i _ _ => by positivity)
    rw [Finset.sum_insert (by simp)] at e1
    have e2 := sum_Ioc_rpow_neg_le hα hk1 (n - 1)
    have e3 : (k : ℝ) ^ (-α) ≤ (k : ℝ) ^ (1 - α) :=
      Real.rpow_le_rpow_of_exponent_le hk1' (by linarith)
    have e4 : (n : ℝ) * (k : ℝ) ^ (1 - α) = Y := by
      rw [hY, show 1 - α = -(α - 1) by ring, Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
    have hCn : 0 ≤ C α * n := by positivity
    have hα1 : α - 1 ≠ 0 := by linarith
    calc _ ≤ _ := e1
      _ = C α * n * (k : ℝ) ^ (-α) + C α * n * ∑ i ∈ Ioc k (n - 1), (i : ℝ) ^ (-α) := by
          rw [Finset.mul_sum]
      _ ≤ C α * n * (k : ℝ) ^ (1 - α) + C α * n * ((k : ℝ) ^ (1 - α) / (α - 1)) := by
          gcongr
      _ = C α * α / (α - 1) * ((n : ℝ) * (k : ℝ) ^ (1 - α)) := by
          field_simp
          ring
      _ = _ := by rw [e4]
  push_cast
  unfold C'₀
  rw [← hK]
  nlinarith

end Podc.PowerLawLabeling
