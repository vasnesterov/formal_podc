import Papers.PODC2010.TruncatedGaleShapley.Theorem3Det
import Papers.PODC2010.TruncatedGaleShapley.Locality
import Podc.Probability.Finite.MultiplicativeChernoff

/-!
# Theorem 3: estimating the size of a stable matching with a constant number of queries (§6.3)

The randomised algorithm of §6.3, with the paper's parameters `γ = ε/(8Δ)`,
`j = ⌈1 + (2Δ-2)/ε⌉`, `N = ⌈6(Δ+1)/γ² · ln(6/δ)⌉`, `K = 2(Δ+1)N`:

1. sample `N` nodes uniformly (with replacement); `X` = number of red ones;
2. sample `K` nodes uniformly; if fewer than `N` are red, fail; otherwise let `Y` be the number of
   the first `N` red samples that are matched in `M_j`;
3. output `m̂ = n · (X/N) · (Y/N)`.

The random choices are uniform on `(Fin N → V) × (Fin K → V)` (probability by counting, `uprob`).

* `theorem_3_prob`: with probability `≥ 1 - δ` the algorithm does not fail and
  `|m̂ - |M_∞|| ≤ ε |M_∞|`, where `M_∞` is the stable matching found by Gale–Shapley.
* `theorem_3_queries`: deciding whether a red node is matched in `M_j` only needs the local data of
  the nodes within distance `2j` (`Bicoloured.run_congr_of_agree`); there are fewer than
  `3(Δ-1)^{2j}` of them; and `N + K + N · 3(Δ-1)^{2j} ≤ 25000 ε⁻² (Δ-1)^{3+4Δ/ε} ln δ⁻¹`.
-/

namespace Podc.TruncatedGaleShapley

open Finset Cslib.Probability

set_option linter.unusedSectionVars false

/-- `γ = ε / (8Δ)`. -/
noncomputable def gam3 (Δ : ℕ) (ε : ℝ) : ℝ := ε / (8 * Δ)

/-- The number of Gale–Shapley rounds, `j = ⌈1 + (2Δ - 2)/ε⌉`. -/
noncomputable def j3 (Δ : ℕ) (ε : ℝ) : ℕ := ⌈1 + (2 * Δ - 2 : ℝ) / ε⌉₊

/-- The sample size `N = ⌈N₀⌉`, `N₀ = 6(Δ+1)/γ² · ln(6/δ)`. -/
noncomputable def N3 (Δ : ℕ) (ε δ : ℝ) : ℕ := ⌈6 * (Δ + 1) / gam3 Δ ε ^ 2 * Real.log (6 / δ)⌉₊

/-- `K = 2(Δ+1)N` samples to find `N` red nodes. -/
def K3 (Δ N : ℕ) : ℕ := 2 * (Δ + 1) * N

variable {V : Type*} [Fintype V] [DecidableEq V]

namespace Bicoloured

variable (I : Bicoloured V)

/-- The red nodes matched in `M_j`. -/
noncomputable def matchedReds (j : ℕ) : Finset V := I.reds.filter fun r => (I.run j).p r ≠ none

/-- The estimator of §6.3 on the random choices `ω = (a, b)`: `none` = failure. -/
noncomputable def estimate (j N K : ℕ) (ω : (Fin N → V) × (Fin K → V)) : Option ℝ :=
  if #(univ.filter fun i => ω.2 i ∈ I.reds) < N then none
  else some ((Fintype.card V : ℝ) * ((#(univ.filter fun i => ω.1 i ∈ I.reds) : ℝ) / N) *
    ((#(univ.filter fun i => ω.2 i ∈ I.matchedReds j ∧
      #(univ.filter fun k => k < i ∧ ω.2 k ∈ I.reds) < N) : ℝ) / N))

end Bicoloured

/-! ### Arithmetic of the parameters -/

section Params

variable {Δ : ℕ} {ε δ : ℝ}

lemma gam3_pos (hΔ3 : 3 ≤ Δ) (hε0 : 0 < ε) : 0 < gam3 Δ ε := by
  unfold gam3; have : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
  positivity

lemma gam3_le_one (hΔ3 : 3 ≤ Δ) (_hε0 : 0 < ε) (hε1 : ε ≤ 1) : gam3 Δ ε ≤ 1 := by
  unfold gam3; have : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
  rw [div_le_one (by positivity)]; linarith

lemma four_mul_gam3 (hΔ3 : 3 ≤ Δ) : 4 * (Δ : ℝ) * gam3 Δ ε = ε / 2 := by
  unfold gam3; have : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
  field_simp; ring

lemma j3_spec (hΔ3 : 3 ≤ Δ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    2 ≤ j3 Δ ε ∧ 1 + ((Δ - 1 : ℕ) : ℝ) / (ε / 2) ≤ j3 Δ ε ∧ (j3 Δ ε : ℝ) ≤ 2 * Δ / ε := by
  have hD : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
  have hcast : ((Δ - 1 : ℕ) : ℝ) = (Δ : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have hx : ((Δ - 1 : ℕ) : ℝ) / (ε / 2) = (2 * Δ - 2 : ℝ) / ε := by
    rw [hcast]; field_simp
  have h4 : (4 : ℝ) ≤ (2 * Δ - 2 : ℝ) / ε := by
    rw [le_div_iff₀ hε0]; nlinarith
  have hle := Nat.le_ceil (1 + (2 * Δ - 2 : ℝ) / ε)
  refine ⟨?_, by rw [hx]; exact hle, ?_⟩
  · have : (2 : ℝ) ≤ j3 Δ ε := by unfold j3; linarith
    exact_mod_cast this
  · have hlt := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 1 + (2 * Δ - 2 : ℝ) / ε)
    have h2 : (2 : ℝ) ≤ 2 / ε := by rw [le_div_iff₀ hε0]; linarith
    have : (2 * Δ - 2 : ℝ) / ε + 2 / ε = 2 * Δ / ε := by field_simp; ring
    unfold j3; linarith

lemma log_six_div_pos (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) : 0 < Real.log (6 / δ) :=
  Real.log_pos (by rw [lt_div_iff₀ hδ0]; linarith)

lemma le_N3 (Δ : ℕ) (ε δ : ℝ) : 6 * (Δ + 1) / gam3 Δ ε ^ 2 * Real.log (6 / δ) ≤ N3 Δ ε δ :=
  Nat.le_ceil _

/-- `ln 6 ≤ 2.6 ln 2` (from `6⁵ ≤ 2¹³`). -/
lemma log_six_le : Real.log 6 ≤ 2.6 * Real.log 2 := by
  have h : Real.log ((6 : ℝ) ^ 5) ≤ Real.log ((2 : ℝ) ^ 13) :=
    Real.log_le_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h; linarith

/-- `N ≤ 6250 (Δ-1)³ ε⁻² ln δ⁻¹` (§6.3). -/
lemma N3_le (hΔ3 : 3 ≤ Δ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    (N3 Δ ε δ : ℝ) ≤ 6250 * ((Δ : ℝ) - 1) ^ 3 / ε ^ 2 * Real.log δ⁻¹ := by
  have hD : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
  set L := Real.log δ⁻¹
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by
    rw [le_inv_comm₀ (by norm_num) hδ0]; linarith)
  have hl2 := Real.log_two_gt_d9
  have h6 : Real.log (6 / δ) = Real.log 6 + L := by
    rw [div_eq_mul_inv, Real.log_mul (by norm_num) (by positivity)]
  have hlog6 := log_six_le
  have hN0 : 6 * (Δ + 1) / gam3 Δ ε ^ 2 * Real.log (6 / δ) =
      384 * (Δ : ℝ) ^ 2 * (Δ + 1) / ε ^ 2 * (Real.log 6 + L) := by
    rw [h6]; unfold gam3; field_simp; ring
  have hε2 : 0 < ε ^ 2 := by positivity
  have hl6 : 0 < Real.log 6 := Real.log_pos (by norm_num)
  have h0 : (0 : ℝ) ≤ 6 * (Δ + 1) / gam3 Δ ε ^ 2 * Real.log (6 / δ) := by
    rw [hN0]; exact mul_nonneg (div_nonneg (by positivity) hε2.le) (by linarith)
  have hlt : (N3 Δ ε δ : ℝ) < 6 * (Δ + 1) / gam3 Δ ε ^ 2 * Real.log (6 / δ) + 1 :=
    Nat.ceil_lt_add_one h0
  rw [hN0] at hlt
  have hpoly : (Δ : ℝ) ^ 2 * (Δ + 1) ≤ 4.5 * ((Δ : ℝ) - 1) ^ 3 := by
    nlinarith [sq_nonneg ((Δ : ℝ) - 3)]
  have hε21 : ε ^ 2 ≤ 1 := by nlinarith
  have hcube : (8 : ℝ) ≤ ((Δ : ℝ) - 1) ^ 3 := by nlinarith
  -- `384 Δ²(Δ+1)(ln 6 + L) ≤ 6220.8 (Δ-1)³ L`
  have key : 384 * (Δ : ℝ) ^ 2 * (Δ + 1) * (Real.log 6 + L) ≤ 6220.8 * ((Δ : ℝ) - 1) ^ 3 * L := by
    have h1 : Real.log 6 + L ≤ 3.6 * L := by linarith
    have h2 : 0 ≤ Real.log 6 + L := by linarith
    calc 384 * (Δ : ℝ) ^ 2 * (Δ + 1) * (Real.log 6 + L)
        ≤ 384 * (4.5 * ((Δ : ℝ) - 1) ^ 3) * (Real.log 6 + L) :=
          mul_le_mul_of_nonneg_right (by nlinarith) h2
      _ ≤ 384 * (4.5 * ((Δ : ℝ) - 1) ^ 3) * (3.6 * L) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 6220.8 * ((Δ : ℝ) - 1) ^ 3 * L := by ring
  have hgoal : 384 * (Δ : ℝ) ^ 2 * (Δ + 1) / ε ^ 2 * (Real.log 6 + L) + 1 ≤
      6250 * ((Δ : ℝ) - 1) ^ 3 / ε ^ 2 * L := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_add_one hε2.ne', div_le_div_iff_of_pos_right hε2]
    nlinarith
  linarith

/-- The query count of §6.3: `N + 2(Δ+1)N + 3(Δ-1)^{2j} N ≤ 25000 ε⁻² (Δ-1)^{3+4Δ/ε} ln δ⁻¹`. -/
theorem queries_le (hΔ3 : 3 ≤ Δ) (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    (N3 Δ ε δ : ℝ) + K3 Δ (N3 Δ ε δ) + N3 Δ ε δ * (3 * ((Δ : ℝ) - 1) ^ (2 * j3 Δ ε)) ≤
      25000 / ε ^ 2 * ((Δ : ℝ) - 1) ^ (3 + 4 * (Δ : ℝ) / ε) * Real.log δ⁻¹ := by
  have hD : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
  obtain ⟨hj2, -, hjle⟩ := j3_spec hΔ3 hε0 hε1
  set j := j3 Δ ε
  set N := N3 Δ ε δ
  set a : ℝ := (Δ : ℝ) - 1 with ha
  have ha2 : 2 ≤ a := by linarith
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hNle := N3_le hΔ3 hε0 hε1 hδ0 hδ1
  have hL : 0 ≤ Real.log δ⁻¹ := Real.log_nonneg (by rw [le_inv_comm₀ (by norm_num) hδ0]; linarith)
  set P : ℝ := a ^ (2 * j)
  have hP4 : a ^ 4 ≤ P := pow_le_pow_right₀ (by linarith) (by omega)
  have hP : 1 + 2 * ((Δ : ℝ) + 1) ≤ P := by
    have : 1 + 2 * ((Δ : ℝ) + 1) = 2 * a + 5 := by rw [ha]; ring
    rw [this]; nlinarith [sq_nonneg a, sq_nonneg (a - 2)]
  have hK : (K3 Δ N : ℝ) = 2 * ((Δ : ℝ) + 1) * N := by simp [K3]
  have step1 : (N : ℝ) + K3 Δ N + N * (3 * P) ≤ 4 * P * N := by rw [hK]; nlinarith
  have hPr : P ≤ a ^ (4 * (Δ : ℝ) / ε) := by
    rw [show P = a ^ ((2 * j : ℕ) : ℝ) from (Real.rpow_natCast a (2 * j)).symm]
    apply Real.rpow_le_rpow_of_exponent_le (by linarith)
    have : 4 * (Δ : ℝ) / ε = 2 * (2 * Δ / ε) := by ring
    push_cast; linarith
  have hapos : 0 < a := by linarith
  have hsplit : a ^ (3 + 4 * (Δ : ℝ) / ε) = a ^ 3 * a ^ (4 * (Δ : ℝ) / ε) := by
    rw [Real.rpow_add hapos, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  have hP0 : 0 ≤ P := by positivity
  calc (N : ℝ) + K3 Δ N + N * (3 * P) ≤ 4 * P * N := step1
    _ ≤ 4 * a ^ (4 * (Δ : ℝ) / ε) * (6250 * a ^ 3 / ε ^ 2 * Real.log δ⁻¹) := by
        apply mul_le_mul (by linarith) hNle hN0 (by positivity)
    _ = 25000 / ε ^ 2 * a ^ (3 + 4 * (Δ : ℝ) / ε) * Real.log δ⁻¹ := by
        rw [hsplit]; ring

end Params

/-! ### The probability bound -/

lemma two_exp_neg_le {δ t : ℝ} (hδ0 : 0 < δ) (ht : Real.log (6 / δ) ≤ t) :
    2 * Real.exp (-t) ≤ δ / 3 := by
  have h : Real.exp (-t) ≤ Real.exp (-Real.log (6 / δ)) := Real.exp_le_exp.2 (by linarith)
  rw [Real.exp_neg (Real.log (6 / δ)), Real.exp_log (by positivity)] at h
  have : (6 / δ)⁻¹ = δ / 6 := by rw [inv_div]
  rw [this] at h; linarith

lemma card_filter_fst {α β : Type*} [Fintype α] [Fintype β] (P : α → Prop) [DecidablePred P]
    [DecidablePred fun ω : α × β => P ω.1] :
    #(univ.filter fun ω : α × β => P ω.1) = #(univ.filter P) * Fintype.card β := by
  rw [show (univ.filter fun ω : α × β => P ω.1) = (univ.filter P) ×ˢ (univ : Finset β) by
    ext; simp, card_product, card_univ]

lemma card_filter_snd {α β : Type*} [Fintype α] [Fintype β] (P : β → Prop) [DecidablePred P]
    [DecidablePred fun ω : α × β => P ω.2] :
    #(univ.filter fun ω : α × β => P ω.2) = Fintype.card α * #(univ.filter P) := by
  rw [show (univ.filter fun ω : α × β => P ω.2) = (univ : Finset α) ×ˢ (univ.filter P) by
    ext; simp, card_product, card_univ]

namespace Bicoloured

variable {I : Bicoloured V}

lemma reds_nonempty [Nonempty V] (hiso : ∀ v, (I.N v).Nonempty) : I.reds.Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨u, hu⟩ := hiso v
  cases hv : I.red v
  · exact ⟨u, I.mem_reds.2 (red_of_mem_blue hu hv)⟩
  · exact ⟨v, I.mem_reds.2 hv⟩

/-- The size facts of §6.3 used in the proof of Theorem 3: (3)–(7). -/
lemma t3_sizes [Nonempty V] {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hΔ : ∀ v, (I.N v).card ≤ Δ)
    (hiso : ∀ v, (I.N v).Nonempty) {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) :
    0 < (#I.reds : ℝ) ∧ (#I.reds : ℝ) ≤ Fintype.card V ∧
    (Fintype.card V : ℝ) ≤ (Δ + 1) * #I.reds ∧
    (Fintype.card V : ℝ) ≤ 2 * Δ * I.size (Minf I) ∧
    (#I.reds : ℝ) ≤ 2 * Δ * I.size (I.run (j3 Δ ε)) ∧
    0 ≤ I.size (I.run (j3 Δ ε)) ∧
    I.size (I.run (j3 Δ ε)) ≤ #I.reds ∧
    I.size (I.run (j3 Δ ε)) ≤ I.size (Minf I) ∧
    I.size (Minf I) ≤ I.size (I.run (j3 Δ ε)) + ε / 2 * I.size (Minf I) := by
  obtain ⟨hj2, hj, -⟩ := j3_spec hΔ3 hε0 hε1
  have hD : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
  have F1 : (#I.reds : ℝ) ≤ Δ * I.size (Minf I) := by
    have := card_reds_le isMatching_Minf isStable_Minf hiso hΔ
    rw [size_eq_card_matched_blues]; exact_mod_cast this
  have F2 : (#I.blues : ℝ) ≤ Δ * I.size (Minf I) := by
    have := card_blues_le isMatching_Minf isStable_Minf hiso hΔ
    rw [size_eq_card_matched_reds isMatching_Minf]; exact_mod_cast this
  have F3 : (#I.reds : ℝ) + #I.blues = Fintype.card V := by
    exact_mod_cast card_reds_add_blues (I := I)
  have hMiR : I.size (Minf I) ≤ #I.reds := by
    rw [size_eq_card_matched_reds isMatching_Minf]; exact_mod_cast card_filter_le _ _
  have hMjR : I.size (I.run (j3 Δ ε)) ≤ #I.reds := by
    rw [size_eq_card_matched_reds (isMatching_run _)]; exact_mod_cast card_filter_le _ _
  have hMj0 : 0 ≤ I.size (I.run (j3 Δ ε)) := blueW_nonneg I.respectsPrefs_one _
  have hMjMi : I.size (I.run (j3 Δ ε)) ≤ I.size (Minf I) := size_run_le_Minf (by omega)
  have hMiMj := size_Minf_le (I := I) hΔ hε0 hj2 hj
  have hRpos : (0 : ℝ) < #I.reds := by exact_mod_cast (reds_nonempty hiso).card_pos
  have hBn0 : (0 : ℝ) ≤ #I.blues := Nat.cast_nonneg _
  refine ⟨hRpos, by linarith, by nlinarith, by nlinarith, by nlinarith, hMj0, hMjR, hMjMi,
    by nlinarith⟩

/-- Bound on the first bad event (the frequency of red nodes among `N` samples is off). -/
lemma t3_boundX [Nonempty V] {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hΔ : ∀ v, (I.N v).card ≤ Δ)
    (hiso : ∀ v, (I.N v).Nonempty) {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) :
    (#(univ.filter fun a : Fin (N3 Δ ε δ) → V => gam3 Δ ε * ((#I.reds : ℝ) / Fintype.card V *
      Fintype.card (Fin (N3 Δ ε δ))) ≤ |(#(univ.filter fun i => a i ∈ I.reds) : ℝ) -
        (#I.reds : ℝ) / Fintype.card V * Fintype.card (Fin (N3 Δ ε δ))|) : ℝ) ≤
      δ / 3 * (Fintype.card V : ℝ) ^ (N3 Δ ε δ) := by
  obtain ⟨hRpos, hRn, hnR, -⟩ := t3_sizes hΔ3 hΔ hiso hε0 hε1
  have h := card_filter_abs_card_filter_mem_sub_ge_le (ι := Fin (N3 Δ ε δ)) I.reds rfl
    (gam3_pos hΔ3 hε0).le (gam3_le_one hΔ3 hε0 hε1)
  rw [Fintype.card_fin] at h ⊢
  refine h.trans (mul_le_mul_of_nonneg_right (two_exp_neg_le hδ0 ?_) (by positivity))
  have hN0 := le_N3 Δ ε δ
  have hγ0 := gam3_pos hΔ3 hε0
  have hL0 := log_six_div_pos hδ0 hδ1
  have hn : (0 : ℝ) < Fintype.card V := hRpos.trans_le hRn
  -- `μ ≥ N/(Δ+1)`
  have hμ : (N3 Δ ε δ : ℝ) / (Δ + 1) ≤ (#I.reds : ℝ) / Fintype.card V * N3 Δ ε δ := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) hn]
    have := Nat.cast_nonneg (α := ℝ) (N3 Δ ε δ); nlinarith
  have e : gam3 Δ ε ^ 2 * (6 * (Δ + 1) / gam3 Δ ε ^ 2 * Real.log (6 / δ)) =
      6 * (Δ + 1) * Real.log (6 / δ) := by field_simp
  have h1 : gam3 Δ ε ^ 2 * (6 * (Δ + 1) / gam3 Δ ε ^ 2 * Real.log (6 / δ)) ≤
      gam3 Δ ε ^ 2 * N3 Δ ε δ := mul_le_mul_of_nonneg_left hN0 (sq_nonneg _)
  have h2 : Real.log (6 / δ) ≤ gam3 Δ ε ^ 2 * ((N3 Δ ε δ : ℝ) / (Δ + 1)) / 3 := by
    rw [le_div_iff₀ (by norm_num), mul_div_assoc', le_div_iff₀ (by positivity)]
    nlinarith
  calc Real.log (6 / δ) ≤ gam3 Δ ε ^ 2 * ((N3 Δ ε δ : ℝ) / (Δ + 1)) / 3 := h2
    _ ≤ gam3 Δ ε ^ 2 * ((#I.reds : ℝ) / Fintype.card V * N3 Δ ε δ) / 3 := by gcongr

/-- Bound on the failure event (fewer than `N` red nodes among the `K` samples). -/
lemma t3_boundF [Nonempty V] {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hΔ : ∀ v, (I.N v).card ≤ Δ)
    (hiso : ∀ v, (I.N v).Nonempty) {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) :
    (#(univ.filter fun b : Fin (K3 Δ (N3 Δ ε δ)) → V =>
      #(univ.filter fun i => b i ∈ I.reds) < N3 Δ ε δ) : ℝ) ≤
      δ / 3 * (Fintype.card V : ℝ) ^ (K3 Δ (N3 Δ ε δ)) := by
  obtain ⟨hRpos, hRn, hnR, -⟩ := t3_sizes hΔ3 hΔ hiso hε0 hε1
  set N := N3 Δ ε δ
  set K := K3 Δ N
  have hD : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
  have hN0 := le_N3 Δ ε δ
  have hγ0 := gam3_pos hΔ3 hε0
  have hγ1 := gam3_le_one hΔ3 hε0 hε1
  have hL0 := log_six_div_pos hδ0 hδ1
  have hn : (0 : ℝ) < Fintype.card V := hRpos.trans_le hRn
  have hN6 : 6 * (Δ + 1) * Real.log (6 / δ) ≤ N := by
    refine le_trans ?_ hN0
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    have : gam3 Δ ε ^ 2 ≤ 1 := by nlinarith
    have : 0 ≤ 6 * ((Δ : ℝ) + 1) * Real.log (6 / δ) := by positivity
    nlinarith
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN6
  have hK : (Fintype.card (Fin K) : ℝ) = 2 * (Δ + 1) * N := by simp [K, K3]
  set μ : ℝ := (#I.reds : ℝ) / Fintype.card V * Fintype.card (Fin K) with hμ
  have hμ2 : 2 * N ≤ μ := by
    rw [hμ, hK, div_mul_eq_mul_div, le_div_iff₀ hn]; nlinarith
  have hμK : μ ≤ 2 * (Δ + 1) * N := by
    rw [hμ, hK, div_mul_eq_mul_div, div_le_iff₀ hn]
    have : 0 ≤ 2 * ((Δ : ℝ) + 1) * N := by positivity
    nlinarith
  have hμpos : 0 < μ := by linarith
  have hβ1 : N / μ ≤ 1 := by rw [div_le_one hμpos]; linarith
  have h := card_filter_abs_card_filter_mem_sub_ge_le (ι := Fin K) I.reds hμ
    (div_nonneg hNpos.le hμpos.le) hβ1
  have hsub : (univ.filter fun b : Fin K → V => #(univ.filter fun i => b i ∈ I.reds) < N) ⊆
      univ.filter fun b : Fin K → V =>
        N / μ * μ ≤ |(#(univ.filter fun i => b i ∈ I.reds) : ℝ) - μ| := by
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    rw [div_mul_cancel₀ _ hμpos.ne']
    have : ((#(univ.filter fun i => b i ∈ I.reds) : ℕ) : ℝ) < N := by exact_mod_cast hb
    rw [abs_sub_comm, abs_of_pos (by linarith)]; linarith
  refine (Nat.cast_le.2 (card_le_card hsub)).trans (h.trans ?_)
  rw [Fintype.card_fin]
  refine mul_le_mul_of_nonneg_right (two_exp_neg_le hδ0 ?_) (by positivity)
  rw [div_pow, div_mul_eq_mul_div, div_div, le_div_iff₀ (by positivity)]
  have h1 : 3 * μ * Real.log (6 / δ) ≤ (N : ℝ) * N := by
    have := mul_le_mul_of_nonneg_right hμK hL0.le
    have := mul_le_mul_of_nonneg_left hN6 hNpos.le
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hμpos.le]

/-- Bound on the third bad event (the frequency of matched nodes among the first `N` red samples
is off). -/
lemma t3_boundY [Nonempty V] {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hΔ : ∀ v, (I.N v).card ≤ Δ)
    (hiso : ∀ v, (I.N v).Nonempty) {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) :
    (#(univ.filter fun b : Fin (K3 Δ (N3 Δ ε δ)) → V =>
      N3 Δ ε δ ≤ #(univ.filter fun i => b i ∈ I.reds) ∧
      gam3 Δ ε * ((#(I.matchedReds (j3 Δ ε)) / #I.reds : ℝ) * N3 Δ ε δ) ≤
        |(#(univ.filter fun i => b i ∈ I.matchedReds (j3 Δ ε) ∧
          #(univ.filter fun k => k < i ∧ b k ∈ I.reds) < N3 Δ ε δ) : ℝ) -
          (#(I.matchedReds (j3 Δ ε)) / #I.reds : ℝ) * N3 Δ ε δ|) : ℝ) ≤
      δ / 3 * (Fintype.card V : ℝ) ^ (K3 Δ (N3 Δ ε δ)) := by
  obtain ⟨hRpos, -, -, -, hRMj, -⟩ := t3_sizes hΔ3 hΔ hiso hε0 hε1
  have hD : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
  have hN0 := le_N3 Δ ε δ
  have hγ0 := gam3_pos hΔ3 hε0
  have hL0 := log_six_div_pos hδ0 hδ1
  have h := card_firstHits_abs_sub_ge_le (X := V) (A := I.reds) (B := I.matchedReds (j3 Δ ε))
    (filter_subset _ _) (reds_nonempty hiso) (N3 Δ ε δ) (K3 Δ (N3 Δ ε δ)) hγ0.le
    (gam3_le_one hΔ3 hε0 hε1)
  refine h.trans (mul_le_mul_of_nonneg_right (two_exp_neg_le hδ0 ?_) (by positivity))
  have hBm : (#(I.matchedReds (j3 Δ ε)) : ℝ) = I.size (I.run (j3 Δ ε)) :=
    (size_eq_card_matched_reds (isMatching_run _)).symm
  rw [hBm]
  set Mj := I.size (I.run (j3 Δ ε))
  set Rn := (#I.reds : ℝ)
  set N := (N3 Δ ε δ : ℝ)
  set γ := gam3 Δ ε
  have hq : 1 / (2 * Δ) ≤ Mj / Rn := by
    rw [div_le_div_iff₀ (by positivity) hRpos]; linarith
  have e : γ ^ 2 * (6 * (Δ + 1) / γ ^ 2 * Real.log (6 / δ)) = 6 * (Δ + 1) * Real.log (6 / δ) := by
    field_simp
  have h1 : γ ^ 2 * (6 * (Δ + 1) / γ ^ 2 * Real.log (6 / δ)) ≤ γ ^ 2 * N :=
    mul_le_mul_of_nonneg_left hN0 (sq_nonneg _)
  have hγN : 6 * (Δ + 1) * Real.log (6 / δ) ≤ γ ^ 2 * N := by linarith
  have hqN : γ ^ 2 * N / (2 * Δ) ≤ γ ^ 2 * (Mj / Rn * N) := by
    have := mul_le_mul_of_nonneg_left hq (by positivity : 0 ≤ γ ^ 2 * N)
    calc γ ^ 2 * N / (2 * Δ) = γ ^ 2 * N * (1 / (2 * Δ)) := by ring
      _ ≤ γ ^ 2 * N * (Mj / Rn) := this
      _ = _ := by ring
  have h3 : 3 * Real.log (6 / δ) ≤ γ ^ 2 * N / (2 * Δ) := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  linarith

/-- Outside the three bad events the estimate is `ε`-accurate. -/
lemma t3_good [Nonempty V] {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hΔ : ∀ v, (I.N v).card ≤ Δ)
    (hiso : ∀ v, (I.N v).Nonempty) {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) (a : Fin (N3 Δ ε δ) → V) (b : Fin (K3 Δ (N3 Δ ε δ)) → V)
    (hX : |(#(univ.filter fun i => a i ∈ I.reds) : ℝ) -
        (#I.reds : ℝ) / Fintype.card V * Fintype.card (Fin (N3 Δ ε δ))| <
      gam3 Δ ε * ((#I.reds : ℝ) / Fintype.card V * Fintype.card (Fin (N3 Δ ε δ))))
    (hF : N3 Δ ε δ ≤ #(univ.filter fun i => b i ∈ I.reds))
    (hY : |(#(univ.filter fun i => b i ∈ I.matchedReds (j3 Δ ε) ∧
          #(univ.filter fun k => k < i ∧ b k ∈ I.reds) < N3 Δ ε δ) : ℝ) -
          (#(I.matchedReds (j3 Δ ε)) / #I.reds : ℝ) * N3 Δ ε δ| <
      gam3 Δ ε * ((#(I.matchedReds (j3 Δ ε)) / #I.reds : ℝ) * N3 Δ ε δ)) :
    ∃ m, I.estimate (j3 Δ ε) (N3 Δ ε δ) (K3 Δ (N3 Δ ε δ)) (a, b) = some m ∧
      |m - (matchingEdges (Minf I).p).card| ≤ ε * (matchingEdges (Minf I).p).card := by
  obtain ⟨hRpos, hRn, -, hnMi, -, hMj0, hMjR, hMjMi, hMi2⟩ := t3_sizes hΔ3 hΔ hiso hε0 hε1
  have hγ0 := gam3_pos hΔ3 hε0
  have hN0 := le_N3 Δ ε δ
  have hNpos : (0 : ℝ) < N3 Δ ε δ := lt_of_lt_of_le (by
    have := log_six_div_pos hδ0 hδ1
    have : (3 : ℝ) ≤ Δ := by exact_mod_cast hΔ3
    positivity) hN0
  have hBm : (#(I.matchedReds (j3 Δ ε)) : ℝ) = I.size (I.run (j3 Δ ε)) :=
    (size_eq_card_matched_reds (isMatching_run _)).symm
  rw [Fintype.card_fin] at hX
  rw [hBm] at hY
  refine ⟨_, by rw [estimate, ite_eq_right (not_lt.2 hF)], ?_⟩
  rw [card_matchingEdges isMatching_Minf]
  have hXN : ((#(univ.filter fun i => a i ∈ I.reds) : ℕ) : ℝ) ≤ N3 Δ ε δ := by
    have := card_filter_le (univ : Finset (Fin (N3 Δ ε δ))) fun i => a i ∈ I.reds
    rw [card_univ, Fintype.card_fin] at this; exact_mod_cast this
  apply estimate_error hRpos hRn hMj0 hMjR (div_nonneg (Nat.cast_nonneg _) hNpos.le)
    ((div_le_one hNpos).2 hXN) hγ0.le _ _ hnMi (four_mul_gam3 hΔ3) hMjMi hMi2
  · rw [show ∀ x : ℝ, x / N3 Δ ε δ - (#I.reds : ℝ) / Fintype.card V =
        (x - (#I.reds : ℝ) / Fintype.card V * N3 Δ ε δ) / N3 Δ ε δ from fun x => by field_simp,
      abs_div, abs_of_pos hNpos, div_lt_iff₀ hNpos]
    linarith
  · rw [show ∀ x : ℝ, x / N3 Δ ε δ - I.size (I.run (j3 Δ ε)) / #I.reds =
        (x - I.size (I.run (j3 Δ ε)) / #I.reds * N3 Δ ε δ) / N3 Δ ε δ from fun x => by field_simp,
      abs_div, abs_of_pos hNpos, div_lt_iff₀ hNpos]
    linarith

/-- **Theorem 3** (probability bound). Let `Δ ≥ 3`, `0 < δ ≤ 1/2`, `0 < ε ≤ 1`, and let the
bicoloured graph be nonempty, without isolated nodes, of maximum degree `≤ Δ`. With the
parameters `j = j3 Δ ε`, `N = N3 Δ ε δ`, `K = 2(Δ+1)N` of §6.3 and uniform random choices, the
estimator does not fail and outputs `m̂` with `|m̂ - |M_∞|| ≤ ε |M_∞|` with probability at least
`1 - δ`, where `M_∞` is the stable matching found by the Gale–Shapley algorithm. -/
theorem theorem_3_prob [Nonempty V] {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hΔ : ∀ v, (I.N v).card ≤ Δ)
    (hiso : ∀ v, (I.N v).Nonempty) {ε δ : ℝ} (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ)
    (hδ1 : δ ≤ 1 / 2) :
    1 - δ ≤ uprob (fun ω : (Fin (N3 Δ ε δ) → V) × (Fin (K3 Δ (N3 Δ ε δ)) → V) =>
      ∃ m, I.estimate (j3 Δ ε) (N3 Δ ε δ) (K3 Δ (N3 Δ ε δ)) ω = some m ∧
        |m - (matchingEdges (Minf I).p).card| ≤ ε * (matchingEdges (Minf I).p).card) := by
  classical
  set good := fun ω : (Fin (N3 Δ ε δ) → V) × (Fin (K3 Δ (N3 Δ ε δ)) → V) =>
      ∃ m, I.estimate (j3 Δ ε) (N3 Δ ε δ) (K3 Δ (N3 Δ ε δ)) ω = some m ∧
        |m - (matchingEdges (Minf I).p).card| ≤ ε * (matchingEdges (Minf I).p).card
  have hX := t3_boundX hΔ3 hΔ hiso hε0 hε1 hδ0 hδ1 (I := I)
  have hF := t3_boundF hΔ3 hΔ hiso hε0 hε1 hδ0 hδ1 (I := I)
  have hY := t3_boundY hΔ3 hΔ hiso hε0 hε1 hδ0 hδ1 (I := I)
  set XB := fun a : Fin (N3 Δ ε δ) → V => gam3 Δ ε * ((#I.reds : ℝ) / Fintype.card V *
      Fintype.card (Fin (N3 Δ ε δ))) ≤ |(#(univ.filter fun i => a i ∈ I.reds) : ℝ) -
        (#I.reds : ℝ) / Fintype.card V * Fintype.card (Fin (N3 Δ ε δ))|
  set FB := fun b : Fin (K3 Δ (N3 Δ ε δ)) → V =>
      #(univ.filter fun i => b i ∈ I.reds) < N3 Δ ε δ
  set YB := fun b : Fin (K3 Δ (N3 Δ ε δ)) → V =>
      N3 Δ ε δ ≤ #(univ.filter fun i => b i ∈ I.reds) ∧
      gam3 Δ ε * ((#(I.matchedReds (j3 Δ ε)) / #I.reds : ℝ) * N3 Δ ε δ) ≤
        |(#(univ.filter fun i => b i ∈ I.matchedReds (j3 Δ ε) ∧
          #(univ.filter fun k => k < i ∧ b k ∈ I.reds) < N3 Δ ε δ) : ℝ) -
          (#(I.matchedReds (j3 Δ ε)) / #I.reds : ℝ) * N3 Δ ε δ|
  have hsub : (univ.filter fun ω => ¬ good ω) ⊆
      ((univ.filter fun ω : (Fin (N3 Δ ε δ) → V) × (Fin (K3 Δ (N3 Δ ε δ)) → V) => XB ω.1) ∪
        univ.filter fun ω => FB ω.2) ∪ univ.filter fun ω => YB ω.2 := by
    rintro ⟨a, b⟩ hω
    simp only [mem_filter, mem_univ, true_and, mem_union] at hω ⊢
    by_contra hcon
    push Not at hcon
    exact hω (t3_good hΔ3 hΔ hiso hε0 hε1 hδ0 hδ1 a b (lt_of_not_ge hcon.1.1)
      (not_lt.1 hcon.1.2) (lt_of_not_ge fun h => hcon.2 ⟨not_lt.1 hcon.1.2, h⟩))
  have hcard : (#(univ.filter fun ω => ¬ good ω) : ℝ) ≤
      δ * (Fintype.card V : ℝ) ^ (N3 Δ ε δ) * (Fintype.card V : ℝ) ^ (K3 Δ (N3 Δ ε δ)) := by
    have h1 := card_le_card hsub
    have h2 := h1.trans ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    rw [card_filter_fst, card_filter_snd, card_filter_snd, Fintype.card_fun, Fintype.card_fun]
      at h2
    simp only [Fintype.card_fin] at h2
    have h3 : (#(univ.filter fun ω => ¬ good ω) : ℝ) ≤
        #(univ.filter XB) * (Fintype.card V : ℝ) ^ (K3 Δ (N3 Δ ε δ)) +
        (Fintype.card V : ℝ) ^ (N3 Δ ε δ) * #(univ.filter FB) +
        (Fintype.card V : ℝ) ^ (N3 Δ ε δ) * #(univ.filter YB) := by exact_mod_cast h2
    have hp1 : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ (N3 Δ ε δ) := by positivity
    have hp2 : (0 : ℝ) ≤ (Fintype.card V : ℝ) ^ (K3 Δ (N3 Δ ε δ)) := by positivity
    have := mul_le_mul_of_nonneg_right hX hp2
    have := mul_le_mul_of_nonneg_left hF hp1
    have := mul_le_mul_of_nonneg_left hY hp1
    nlinarith
  have hΩ : (Fintype.card ((Fin (N3 Δ ε δ) → V) × (Fin (K3 Δ (N3 Δ ε δ)) → V)) : ℝ) =
      (Fintype.card V : ℝ) ^ (N3 Δ ε δ) * (Fintype.card V : ℝ) ^ (K3 Δ (N3 Δ ε δ)) := by
    simp [Fintype.card_prod]
  have hΩpos : (0 : ℝ) < (Fintype.card V : ℝ) ^ (N3 Δ ε δ) *
      (Fintype.card V : ℝ) ^ (K3 Δ (N3 Δ ε δ)) := by
    have : (0 : ℝ) < Fintype.card V := by exact_mod_cast Fintype.card_pos
    positivity
  have hbad : uprob (fun ω => ¬ good ω) ≤ δ := by
    rw [uprob_eq_card_filter, hΩ, div_le_iff₀ hΩpos]; linarith
  have := uprob_not (fun ω => ¬ good ω)
  simp only [not_not] at this
  linarith

/-- **Theorem 3** (query bound). To decide whether a red node `r` is matched in `M_j`, it suffices
to know the local data (neighbours, preferences, colour; one oracle query each) of the nodes within
distance `2j` of `r`; there are fewer than `3(Δ-1)^{2j}` of them; and the total number of queries
`N + K + N · 3(Δ-1)^{2j}` is at most `25000 ε⁻² (Δ-1)^{3+4Δ/ε} ln δ⁻¹`. -/
theorem theorem_3_queries {Δ : ℕ} (hΔ3 : 3 ≤ Δ) (hΔ : ∀ v, (I.N v).card ≤ Δ) {ε δ : ℝ}
    (hε0 : 0 < ε) (hε1 : ε ≤ 1) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1 / 2) :
    (∀ (I' : Bicoloured V) (r : V),
      (∀ u ∈ I.graph.closedBall r (2 * j3 Δ ε : ℕ), AgreeAt I I' u) →
        (I.run (j3 Δ ε)).p r = (I'.run (j3 Δ ε)).p r) ∧
    (∀ r, (I.graph.closedBall r (2 * j3 Δ ε : ℕ)).ncard < 3 * (Δ - 1) ^ (2 * j3 Δ ε)) ∧
    (N3 Δ ε δ : ℝ) + K3 Δ (N3 Δ ε δ) + N3 Δ ε δ * (3 * ((Δ : ℝ) - 1) ^ (2 * j3 Δ ε)) ≤
      25000 / ε ^ 2 * ((Δ : ℝ) - 1) ^ (3 + 4 * (Δ : ℝ) / ε) * Real.log δ⁻¹ :=
  ⟨fun _ r h => run_congr_of_agree _ r h,
    fun r => I.graph.ncard_closedBall_lt hΔ3 (fun v => (graph_degree I v).trans_le (hΔ v)) r _,
    queries_le hΔ3 hε0 hε1 hδ0 hδ1⟩

end Bicoloured

end Podc.TruncatedGaleShapley
