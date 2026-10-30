import Papers.PODC2026.DemandAwareThroughput.Rounding
import Papers.PODC2026.DemandAwareThroughput.CycleDirection

/-!
# Dependent rounding (Theorem 3), proved

We prove `DependentRounding n` for every `n` (`dependentRounding`): an `n × n` matrix `α` with
entries in `[0, 1]` and integer row and column sums is the vector of marginals of a distribution on
`0/1` matrices that preserves all row and column sums surely and has negatively correlated zeros
within every row and every column. This is the special case of Theorem 2.3 of Gandhi, Khuller,
Parthasarathy and Srinivasan (JACM 2006) used in the paper.

## Proof

Strong induction on the number of fractional entries (`frac α`). If there is none, `α` is a `0/1`
matrix and the point mass at it works. Otherwise `exists_cycle_direction` gives a nonzero `Δ`
supported on the fractional entries, with zero line sums and at most two nonzero entries per line.
Move along `±Δ` until a new entry becomes integral (`exists_step`): `α⁺ = α + aΔ`,
`α⁻ = α - bΔ` with `a, b > 0`, both in `[0,1]^{n×n}`, with the same line sums and fewer fractional
entries. Mix the two distributions given by induction with weights `b/(a+b)` and `a/(a+b)`.
Marginals and line sums are preserved by linearity. Negative correlation follows from
`prod_mix_le`: on a fixed line, `Δ` restricted to `S` has `0`, `1`, or (if both nonzero entries
of the line lie in `S`) `2` nonzero entries `d, -d`, so `t ↦ ∏_{j∈S} (x_j + t Δ_j)` is constant,
affine, or a concave quadratic times a nonnegative constant, and its weighted mean over the two
endpoints (mean `0`) is at most its value at `0`.
-/

namespace Podc.DemandAwareThroughput

open Finset

namespace DepRound

section Dist

variable {Ω : Type} [Fintype Ω]

/-- The point mass at `ω₀`. -/
noncomputable def dirac [DecidableEq Ω] (ω₀ : Ω) : FinDist Ω where
  w ω := if ω = ω₀ then 1 else 0
  nonneg ω := by split_ifs <;> norm_num
  sum_eq_one := by simp

lemma prob_dirac_of [DecidableEq Ω] (ω₀ : Ω) {E : Ω → Prop} (h : E ω₀) :
    (dirac ω₀).prob E = 1 := by
  classical
  unfold FinDist.prob
  rw [sum_eq_single ω₀ (fun ω _ hω => by simp [dirac, hω]) (by simp)]
  simp [dirac, h]

lemma prob_dirac_of_not [DecidableEq Ω] (ω₀ : Ω) {E : Ω → Prop} (h : ¬ E ω₀) :
    (dirac ω₀).prob E = 0 := by
  classical
  unfold FinDist.prob
  refine sum_eq_zero fun ω _ => ?_
  by_cases hω : ω = ω₀
  · subst hω; simp [h]
  · simp [dirac, hω]

/-- The mixture `p μ + (1 - p) ν`. -/
noncomputable def mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (μ ν : FinDist Ω) : FinDist Ω where
  w ω := p * μ.w ω + (1 - p) * ν.w ω
  nonneg ω := add_nonneg (mul_nonneg hp0 (μ.nonneg ω)) (mul_nonneg (by linarith) (ν.nonneg ω))
  sum_eq_one := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, μ.sum_eq_one, ν.sum_eq_one]; ring

lemma prob_mix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (μ ν : FinDist Ω) (E : Ω → Prop) :
    (mix p hp0 hp1 μ ν).prob E = p * μ.prob E + (1 - p) * ν.prob E := by
  unfold FinDist.prob
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun ω _ => ?_
  simp only [mix]
  split_ifs <;> ring

end Dist

section Ineq

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- The key inequality for negative correlation: if `d` has at most two nonzero entries and zero
sum, `x ≥ 0`, and the weights `p, 1 - p` average `c₁, c₂` to `0`, then the weighted average of
`∏_{j∈S} (x_j + c d_j)` over `c ∈ {c₁, c₂}` is at most `∏_{j∈S} x_j`. -/
lemma prod_mix_le (x d : κ → ℝ) (S : Finset κ) (hx : ∀ j, 0 ≤ x j)
    (hd : (univ.filter fun j => d j ≠ 0).card ≤ 2) (hsum : ∑ j, d j = 0)
    {p c₁ c₂ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hpc : p * c₁ + (1 - p) * c₂ = 0) :
    p * ∏ j ∈ S, (x j + c₁ * d j) + (1 - p) * ∏ j ∈ S, (x j + c₂ * d j) ≤ ∏ j ∈ S, x j := by
  set N := S.filter fun j => d j ≠ 0 with hN
  set R := ∏ j ∈ S.filter (fun j => ¬ d j ≠ 0), x j with hRdef
  have hR : 0 ≤ R := prod_nonneg fun j _ => hx j
  have hsplit : ∀ c : ℝ, ∏ j ∈ S, (x j + c * d j) = (∏ j ∈ N, (x j + c * d j)) * R := by
    intro c
    rw [← prod_filter_mul_prod_filter_not S (fun j => d j ≠ 0)]
    congr 1
    refine prod_congr rfl fun j hj => ?_
    have : d j = 0 := by simpa using (mem_filter.1 hj).2
    simp [this]
  have hsplit0 : ∏ j ∈ S, x j = (∏ j ∈ N, x j) * R := by
    simpa using hsplit 0
  have hNsub : N ⊆ univ.filter fun j => d j ≠ 0 :=
    fun j hj => mem_filter.2 ⟨mem_univ _, (mem_filter.1 hj).2⟩
  have hNcard : N.card ≤ 2 := (card_le_card hNsub).trans hd
  rw [hsplit, hsplit, hsplit0]
  rcases (by omega : N.card = 0 ∨ N.card = 1 ∨ N.card = 2) with hc | hc | hc
  · rw [card_eq_zero.1 hc]; simp only [prod_empty]; linarith
  · obtain ⟨k, hk⟩ := card_eq_one.1 hc
    rw [hk]; simp only [prod_singleton]
    have : p * ((x k + c₁ * d k) * R) + (1 - p) * ((x k + c₂ * d k) * R) = x k * R := by
      linear_combination (d k * R) * hpc
    linarith
  · obtain ⟨k, l, hkl, hk⟩ := card_eq_two.1 hc
    have hall : (univ.filter fun j => d j ≠ 0) = N :=
      (eq_of_subset_of_card_le hNsub (by omega)).symm
    have hdl : d l = -d k := by
      have := hsum
      rw [← sum_filter_ne_zero, hall, hk, sum_pair hkl] at this
      linarith
    rw [hk, prod_pair hkl, prod_pair hkl, prod_pair hkl, hdl]
    have key : x k * x l * R - (p * ((x k + c₁ * d k) * (x l + c₁ * -d k) * R) +
        (1 - p) * ((x k + c₂ * d k) * (x l + c₂ * -d k) * R)) =
        R * (d k ^ 2 * (p * c₁ ^ 2 + (1 - p) * c₂ ^ 2)) := by
      linear_combination (-(R * d k * (x l - x k))) * hpc
    have hnn : 0 ≤ R * (d k ^ 2 * (p * c₁ ^ 2 + (1 - p) * c₂ ^ 2)) :=
      mul_nonneg hR (mul_nonneg (sq_nonneg _)
        (add_nonneg (mul_nonneg hp0 (sq_nonneg _)) (mul_nonneg (by linarith) (sq_nonneg _))))
    linarith

end Ineq

section Step

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Moving from `α ∈ [0,1]^{ι×κ}` along a direction `Δ ≠ 0` supported on the fractional entries
of `α`, there is a largest step `a > 0` keeping all entries in `[0,1]`; at it, some entry in the
support of `Δ` becomes `0` or `1`. -/
lemma exists_step (α Δ : ι → κ → ℝ) (h01 : ∀ i j, 0 ≤ α i j ∧ α i j ≤ 1)
    (hfr : ∀ i j, Δ i j ≠ 0 → 0 < α i j ∧ α i j < 1) (hne : ∃ i j, Δ i j ≠ 0) :
    ∃ a > 0, (∀ i j, 0 ≤ α i j + a * Δ i j ∧ α i j + a * Δ i j ≤ 1) ∧
      ∃ i j, Δ i j ≠ 0 ∧ (α i j + a * Δ i j = 0 ∨ α i j + a * Δ i j = 1) := by
  classical
  set s := univ.filter fun p : ι × κ => Δ p.1 p.2 ≠ 0
  let r : ι × κ → ℝ := fun p =>
    if 0 < Δ p.1 p.2 then (1 - α p.1 p.2) / Δ p.1 p.2 else α p.1 p.2 / (-Δ p.1 p.2)
  obtain ⟨i₀, j₀, h₀⟩ := hne
  obtain ⟨q, hq, hmin⟩ := s.exists_min_image r ⟨(i₀, j₀), by simp [s, h₀]⟩
  have hqΔ : Δ q.1 q.2 ≠ 0 := (mem_filter.1 hq).2
  have hqα := hfr _ _ hqΔ
  refine ⟨r q, ?_, fun i j => ?_, q.1, q.2, hqΔ, ?_⟩
  · simp only [r]
    split_ifs with hpos
    · exact div_pos (by linarith) hpos
    · exact div_pos hqα.1 (by push Not at hpos; exact neg_pos.2 (lt_of_le_of_ne hpos hqΔ))
  · by_cases hij : Δ i j = 0
    · simp [hij, h01 i j]
    have hle : r q ≤ r (i, j) := hmin _ (by simp [s, hij])
    have hrq : 0 < r q := by
      simp only [r]
      split_ifs with hpos
      · exact div_pos (by linarith) hpos
      · exact div_pos hqα.1 (by push Not at hpos; exact neg_pos.2 (lt_of_le_of_ne hpos hqΔ))
    have hα := hfr i j hij
    by_cases hpos : 0 < Δ i j
    · rw [show r (i, j) = (1 - α i j) / Δ i j by simp [r, hpos], le_div_iff₀ hpos] at hle
      have := mul_pos hrq hpos
      constructor <;> linarith
    · have hneg : 0 < -Δ i j := by push Not at hpos; exact neg_pos.2 (lt_of_le_of_ne hpos hij)
      rw [show r (i, j) = α i j / -Δ i j by simp [r, hpos], le_div_iff₀ hneg] at hle
      have := mul_pos hrq hneg
      have e : r q * -Δ i j = -(r q * Δ i j) := by ring
      constructor <;> linarith
  · simp only [r]
    split_ifs with hpos
    · right; field_simp; ring
    · left
      have : -Δ q.1 q.2 ≠ 0 := neg_ne_zero.2 hqΔ
      field_simp; ring

end Step

variable {n : ℕ}

/-- The fractional entries of `α`. -/
noncomputable def frac (α : Fin n → Fin n → ℝ) : Finset (Fin n × Fin n) :=
  by classical exact univ.filter fun p => 0 < α p.1 p.2 ∧ α p.1 p.2 < 1

lemma mem_frac {α : Fin n → Fin n → ℝ} {p : Fin n × Fin n} :
    p ∈ frac α ↔ 0 < α p.1 p.2 ∧ α p.1 p.2 < 1 := by
  classical
  unfold frac
  simp

/-- The conclusion of Theorem 3 for a fixed matrix `α` and distribution `μ`. -/
def IsRounding (α : Fin n → Fin n → ℝ) (μ : FinDist (Fin n → Fin n → Bool)) : Prop :=
  (∀ i j, μ.prob (fun β => β i j = true) = α i j) ∧
  (∀ β, μ.w β ≠ 0 →
    (∀ i, ∑ j, bval (β i j) = ∑ j, α i j) ∧ (∀ j, ∑ i, bval (β i j) = ∑ i, α i j)) ∧
  (∀ i (S : Finset (Fin n)),
    μ.prob (fun β => ∀ j ∈ S, β i j = false) ≤ ∏ j ∈ S, (1 - α i j)) ∧
  (∀ j (S : Finset (Fin n)),
    μ.prob (fun β => ∀ i ∈ S, β i j = false) ≤ ∏ i ∈ S, (1 - α i j))

/-- Base case: a `0/1` matrix is rounded by the point mass at itself. -/
lemma isRounding_of_integral (α : Fin n → Fin n → ℝ) (h : ∀ i j, α i j = 0 ∨ α i j = 1) :
    ∃ μ, IsRounding α μ := by
  classical
  let β₀ : Fin n → Fin n → Bool := fun i j => decide (α i j = 1)
  have hb : ∀ i j, bval (β₀ i j) = α i j := by
    intro i j
    rcases h i j with h0 | h1 <;> simp [β₀, bval, *]
  have hf : ∀ i j, β₀ i j = false ↔ α i j = 0 := by
    intro i j
    rcases h i j with h0 | h1 <;> simp [β₀, *]
  refine ⟨dirac β₀, ?_, ?_, ?_, ?_⟩
  · intro i j
    by_cases hij : β₀ i j = true
    · rw [prob_dirac_of (E := fun β => β i j = true) β₀ hij, ← hb, hij]; rfl
    · rw [prob_dirac_of_not (E := fun β => β i j = true) β₀ hij, ← hb]
      simp only [Bool.not_eq_true] at hij; simp [hij, bval]
  · intro β hβ
    have : β = β₀ := by
      by_contra hne; exact hβ (by simp [dirac, hne])
    subst this
    simp [hb]
  · intro i S
    by_cases hS : ∀ j ∈ S, β₀ i j = false
    · rw [prob_dirac_of _ hS]
      rw [prod_eq_one fun j hj => by rw [(hf i j).1 (hS j hj)]; ring]
    · rw [prob_dirac_of_not _ hS]
      exact prod_nonneg fun j _ => by rcases h i j with h0 | h1 <;> simp [*]
  · intro j S
    by_cases hS : ∀ i ∈ S, β₀ i j = false
    · rw [prob_dirac_of _ hS]
      rw [prod_eq_one fun i hi => by rw [(hf i j).1 (hS i hi)]; ring]
    · rw [prob_dirac_of_not _ hS]
      exact prod_nonneg fun i _ => by rcases h i j with h0 | h1 <;> simp [*]

/-- Main induction: matrices with `k` fractional entries can be rounded. -/
lemma exists_isRounding (k : ℕ) : ∀ α : Fin n → Fin n → ℝ, (frac α).card = k →
    (∀ i j, 0 ≤ α i j ∧ α i j ≤ 1) →
    (∀ i, ∃ s : ℤ, ∑ j, α i j = s) → (∀ j, ∃ t : ℤ, ∑ i, α i j = t) →
    ∃ μ, IsRounding α μ := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro α hk h01 hr hc
  by_cases hF : ∃ i j, 0 < α i j ∧ α i j < 1
  swap
  · refine isRounding_of_integral α fun i j => ?_
    push Not at hF
    rcases (h01 i j).1.lt_or_eq with h | h
    · exact Or.inr (le_antisymm (h01 i j).2 (hF i j h))
    · exact Or.inl h.symm
  -- a cycle direction
  have hnonint : ∀ i j, (¬ ∃ z : ℤ, α i j = z) ↔ 0 < α i j ∧ α i j < 1 := by
    intro i j
    constructor
    · intro h
      refine ⟨lt_of_le_of_ne (h01 i j).1 fun h0 => h ⟨0, by simp [h0]⟩,
        lt_of_le_of_ne (h01 i j).2 fun h1 => h ⟨1, by simp [h1]⟩⟩
    · rintro ⟨h0, h1⟩ ⟨z, hz⟩
      rw [hz] at h0 h1
      have h0' : (0 : ℤ) < z := by exact_mod_cast h0
      have h1' : z < (1 : ℤ) := by exact_mod_cast h1
      omega
  obtain ⟨i₀, j₀, hij₀⟩ := hF
  obtain ⟨Δ, hΔne, hΔfr, hΔr, hΔc, hΔr2, hΔc2⟩ :=
    exists_cycle_direction α hr hc ⟨i₀, j₀, (hnonint i₀ j₀).2 hij₀⟩
  have hfr : ∀ i j, Δ i j ≠ 0 → 0 < α i j ∧ α i j < 1 :=
    fun i j h => (hnonint i j).1 (hΔfr i j h)
  have hex : ∃ i j, Δ i j ≠ 0 := by
    by_contra h0; push Not at h0; exact hΔne (funext fun i => funext fun j => h0 i j)
  obtain ⟨a, ha, ha01, ia, ja, hΔa, hia⟩ := exists_step α Δ h01 hfr hex
  obtain ⟨b, hb, hb01, ib, jb, hΔb, hib⟩ := exists_step α (fun i j => -Δ i j) h01
    (fun i j h => hfr i j (neg_ne_zero.1 h)) (let ⟨i, j, h⟩ := hex; ⟨i, j, neg_ne_zero.2 h⟩)
  set αp : Fin n → Fin n → ℝ := fun i j => α i j + a * Δ i j with hαp
  set αm : Fin n → Fin n → ℝ := fun i j => α i j + b * -Δ i j with hαm
  -- fewer fractional entries
  have hfrac_lt : ∀ (c : ℝ) (D : Fin n → Fin n → ℝ) (i' j' : Fin n), D i' j' ≠ 0 →
      (∀ i j, D i j ≠ 0 → Δ i j ≠ 0) →
      (α i' j' + c * D i' j' = 0 ∨ α i' j' + c * D i' j' = 1) →
      (frac fun i j => α i j + c * D i j).card < k := by
    intro c D i' j' hD hDΔ hend
    rw [← hk]
    refine card_lt_card ((ssubset_iff_of_subset ?_).2 ⟨(i', j'), ?_, ?_⟩)
    · intro p hp
      rw [mem_frac] at hp ⊢
      by_cases hDp : D p.1 p.2 = 0
      · simpa [hDp] using hp
      · exact hfr _ _ (hDΔ _ _ hDp)
    · exact mem_frac.2 (hfr _ _ (hDΔ _ _ hD))
    · rw [mem_frac]; rcases hend with h | h <;> simp [h]
  have hsum_r : ∀ (c : ℝ) (D : Fin n → Fin n → ℝ), (∀ i, ∑ j, D i j = 0) →
      ∀ i, ∑ j, (α i j + c * D i j) = ∑ j, α i j := by
    intro c D hD i
    rw [sum_add_distrib, ← mul_sum, hD i, mul_zero, add_zero]
  have hsum_c : ∀ (c : ℝ) (D : Fin n → Fin n → ℝ), (∀ j, ∑ i, D i j = 0) →
      ∀ j, ∑ i, (α i j + c * D i j) = ∑ i, α i j := by
    intro c D hD j
    rw [sum_add_distrib, ← mul_sum, hD j, mul_zero, add_zero]
  have hΔr' : ∀ i, ∑ j, -Δ i j = 0 := fun i => by rw [sum_neg_distrib, hΔr i, neg_zero]
  have hΔc' : ∀ j, ∑ i, -Δ i j = 0 := fun j => by rw [sum_neg_distrib, hΔc j, neg_zero]
  obtain ⟨μp, hμp1, hμp2, hμp3, hμp4⟩ := ih _ (hfrac_lt a Δ ia ja hΔa (fun _ _ h => h) hia) αp
    rfl ha01 (fun i => by rw [hsum_r a Δ hΔr]; exact hr i)
    (fun j => by rw [hsum_c a Δ hΔc]; exact hc j)
  obtain ⟨μm, hμm1, hμm2, hμm3, hμm4⟩ := ih _ (hfrac_lt b (fun i j => -Δ i j) ib jb hΔb
    (fun _ _ h => neg_ne_zero.1 h) hib) αm rfl hb01
    (fun i => by rw [hsum_r b _ hΔr']; exact hr i)
    (fun j => by rw [hsum_c b _ hΔc']; exact hc j)
  -- the mixture
  have hab : 0 < a + b := by linarith
  set p := b / (a + b) with hp
  have hp0 : 0 ≤ p := div_nonneg hb.le hab.le
  have hp1 : p ≤ 1 := (div_le_one hab).2 (by linarith)
  have hq : 1 - p = a / (a + b) := by rw [hp]; field_simp; ring
  have hpc : p * -a + (1 - p) * b = 0 := by rw [hq, hp]; field_simp; ring
  refine ⟨mix p hp0 hp1 μp μm, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [prob_mix, hμp1, hμm1]
    simp only [αp, αm]
    linear_combination (-Δ i j) * hpc
  · intro β hβ
    have : μp.w β ≠ 0 ∨ μm.w β ≠ 0 := by
      by_contra h0; push Not at h0; exact hβ (by simp [mix, h0])
    rcases this with h | h
    · obtain ⟨h1, h2⟩ := hμp2 β h
      exact ⟨fun i => (h1 i).trans (hsum_r a Δ hΔr i),
        fun j => (h2 j).trans (hsum_c a Δ hΔc j)⟩
    · obtain ⟨h1, h2⟩ := hμm2 β h
      exact ⟨fun i => (h1 i).trans (hsum_r b _ hΔr' i),
        fun j => (h2 j).trans (hsum_c b _ hΔc' j)⟩
  · intro i S
    rw [prob_mix]
    calc p * μp.prob (fun β => ∀ j ∈ S, β i j = false) +
          (1 - p) * μm.prob (fun β => ∀ j ∈ S, β i j = false)
        ≤ p * ∏ j ∈ S, (1 - αp i j) + (1 - p) * ∏ j ∈ S, (1 - αm i j) :=
          add_le_add (mul_le_mul_of_nonneg_left (hμp3 i S) hp0)
            (mul_le_mul_of_nonneg_left (hμm3 i S) (by linarith))
      _ = p * ∏ j ∈ S, ((1 - α i j) + -a * Δ i j) +
          (1 - p) * ∏ j ∈ S, ((1 - α i j) + b * Δ i j) := by
          congr 2 <;> refine prod_congr rfl fun j _ => ?_ <;> simp only [αp, αm] <;> ring
      _ ≤ ∏ j ∈ S, (1 - α i j) :=
          prod_mix_le (fun j => 1 - α i j) (Δ i) S (fun j => by linarith [(h01 i j).2])
            (hΔr2 i) (hΔr i) hp0 hp1 hpc
  · intro j S
    rw [prob_mix]
    calc p * μp.prob (fun β => ∀ i ∈ S, β i j = false) +
          (1 - p) * μm.prob (fun β => ∀ i ∈ S, β i j = false)
        ≤ p * ∏ i ∈ S, (1 - αp i j) + (1 - p) * ∏ i ∈ S, (1 - αm i j) :=
          add_le_add (mul_le_mul_of_nonneg_left (hμp4 j S) hp0)
            (mul_le_mul_of_nonneg_left (hμm4 j S) (by linarith))
      _ = p * ∏ i ∈ S, ((1 - α i j) + -a * Δ i j) +
          (1 - p) * ∏ i ∈ S, ((1 - α i j) + b * Δ i j) := by
          congr 2 <;> refine prod_congr rfl fun i _ => ?_ <;> simp only [αp, αm] <;> ring
      _ ≤ ∏ i ∈ S, (1 - α i j) :=
          prod_mix_le (fun i => 1 - α i j) (fun i => Δ i j) S
            (fun i => by linarith [(h01 i j).2]) (hΔc2 j) (hΔc j) hp0 hp1 hpc

end DepRound

open DepRound in
-- CSLib candidate
/-- **Theorem 3** of the paper (dependent rounding, Gandhi et al., Thm 2.3, case of integer row
and column sums), proved. -/
theorem dependentRounding (n : ℕ) : DependentRounding n := by
  intro α h01 hr hc
  obtain ⟨μ, hμ⟩ := exists_isRounding _ α rfl h01 hr hc
  exact ⟨μ, hμ⟩

end Podc.DemandAwareThroughput
