import Papers.PODC2021.MISTreeLowerBounds.Lemmas

/-!
# Lemma 15: randomized 0-round failure probability

In the graph family of Lemmas 12 and 15 (port number = colour at both endpoints of every edge), all
nodes have the same 0-round view, so a randomized 0-round algorithm is given by a single
probability distribution `p` on node configurations `Fin Δ → L5`, sampled independently at every
node (private randomness). Along an edge of colour `c` the algorithm fails if one endpoint outputs a
non-configuration or the two labels on the edge are incompatible; the probability of this event is
`failProb (Pi Δ a x) p c`.

* `lemma_15`: for `Δ ≥ 2`, `x < Δ` and `a ≥ 1`, some edge fails with probability at least
  `1/Δ^8` (in fact `1/(36Δ²)`).
* `lemma_15_false_delta_one`: the statement of the paper ("for all `x ≤ Δ - 1` and `a ≥ 1`") is false
  for `Δ = 1`: on `K₂` (the 1-regular tree) the distribution "`M` or `A`, each with probability
  `1/2`" fails with probability `1/2 < 1 = 1/Δ^8`. The paper's last step `1/(3Δ)² ≥ 1/Δ⁸` needs
  `Δ ≥ 2`.
-/

namespace Podc.MISTreeLowerBounds

open Finset

variable {Δ : ℕ}

/-- The probability that the edge of colour `c` between two nodes running the randomized 0-round
algorithm `p` (independently) is not correctly labelled for `P`. -/
noncomputable def failProb (P : Problem Δ L5) (p : (Fin Δ → L5) → ℝ) (c : Fin Δ) : ℝ := by
  classical
  exact ∑ σ, ∑ τ, if σ ∈ P.node ∧ τ ∈ P.node ∧ P.edge (σ c) (τ c) then 0 else p σ * p τ

section

variable (P : Problem Δ L5) (p : (Fin Δ → L5) → ℝ) (hp0 : ∀ σ, 0 ≤ p σ) (hp1 : ∑ σ, p σ = 1)
include hp0

open Classical in
theorem failProb_ge_invalid (hp1 : ∑ σ, p σ = 1) (c : Fin Δ) :
    (∑ σ, if σ ∈ P.node then 0 else p σ) ≤ failProb P p c := by
  unfold failProb
  refine sum_le_sum fun σ _ => ?_
  by_cases hσ : σ ∈ P.node
  · simp only [hσ, ite_true]
    exact sum_nonneg fun τ _ => by split_ifs <;> [exact le_rfl; exact mul_nonneg (hp0 _) (hp0 _)]
  · simp only [hσ, ite_false, false_and]
    rw [← mul_sum, hp1, mul_one]

open Classical in
theorem failProb_ge_sq (c : Fin Δ) {ℓ : L5} (hℓ : ¬ P.edge ℓ ℓ) :
    (∑ σ, if σ ∈ P.node ∧ σ c = ℓ then p σ else 0) ^ 2 ≤ failProb P p c := by
  unfold failProb
  rw [sq, sum_mul_sum]
  refine sum_le_sum fun σ _ => sum_le_sum fun τ _ => ?_
  by_cases hσ : σ ∈ P.node ∧ σ c = ℓ
  · by_cases hτ : τ ∈ P.node ∧ τ c = ℓ
    · simp only [hσ, hτ, and_self, ite_true, hσ.1, true_and, hℓ, ite_false]
      exact le_rfl
    · simp only [hτ, ite_false, mul_zero]
      split_ifs <;> [exact le_rfl; exact mul_nonneg (hp0 _) (hp0 _)]
  · simp only [hσ, ite_false, zero_mul]
    split_ifs <;> [exact le_rfl; exact mul_nonneg (hp0 _) (hp0 _)]

end

/-- The self-incompatible labels `M, A, P`. -/
def badLabels : Finset L5 := {.M, .A, .P}

theorem not_E5_self : ∀ ℓ ∈ badLabels, ¬ E5 ℓ ℓ := by decide

/-- Every node configuration of `Π_Δ(a, x)` (`x < Δ`, `a ≥ 1`) contains `M`, `A` or `P`
(the observation of Lemma 12). -/
theorem exists_bad {a x : ℕ} (hx : x < Δ) (ha : 1 ≤ a) {σ : Fin Δ → L5} (hσ : σ ∈ (Pi Δ a x).node) :
    ∃ c, σ c ∈ badLabels := by
  rcases hσ with hM | hA | hP
  · obtain ⟨i, hi⟩ := exists_eq_of_cnt_pos (σ := σ) (ℓ := .M) (by omega)
    exact ⟨i, by simp [hi, badLabels]⟩
  · obtain ⟨i, hi⟩ := exists_eq_of_cnt_pos (σ := σ) (ℓ := .A) (by omega)
    exact ⟨i, by simp [hi, badLabels]⟩
  · obtain ⟨i, hi⟩ := exists_eq_of_cnt_pos (σ := σ) (ℓ := .P) (by omega)
    exact ⟨i, by simp [hi, badLabels]⟩

open Classical in
/-- Lemma 15 of [paper] (for `Δ ≥ 2`): `Π_Δ(a, x)` is not 0-round solvable with failure
probability less than `1/Δ^8` in the randomized port-numbering model, for all `x ≤ Δ - 1` and
`a ≥ 1`, even with a `Δ`-edge colouring: for every output distribution `p` some edge fails with
probability at least `1/Δ^8`. -/
theorem lemma_15 {a x : ℕ} (hΔ : 2 ≤ Δ) (hx : x < Δ) (ha : 1 ≤ a)
    (p : (Fin Δ → L5) → ℝ) (hp0 : ∀ σ, 0 ≤ p σ) (hp1 : ∑ σ, p σ = 1) :
    ∃ c, 1 / (Δ : ℝ) ^ 8 ≤ failProb (Pi Δ a x) p c := by
  set P := Pi Δ a x
  set q : ℝ := ∑ σ, if σ ∈ P.node then 0 else p σ
  set r : Fin Δ → L5 → ℝ := fun c ℓ => ∑ σ, if σ ∈ P.node ∧ σ c = ℓ then p σ else 0
  have hvalid : (∑ σ, if σ ∈ P.node then p σ else 0) = 1 - q := by
    rw [← hp1, eq_sub_iff_add_eq, ← sum_add_distrib]
    exact sum_congr rfl fun σ _ => by split_ifs <;> simp
  -- the probability mass of valid configurations is covered by the events `σ c = ℓ ∈ {M, A, P}`
  have hcover : 1 - q ≤ ∑ cℓ ∈ (univ : Finset (Fin Δ)) ×ˢ badLabels, r cℓ.1 cℓ.2 := by
    rw [← hvalid, sum_product]
    simp only [r]
    have heq : (∑ c, ∑ ℓ ∈ badLabels, ∑ σ, if σ ∈ P.node ∧ σ c = ℓ then p σ else 0) =
        ∑ σ, ∑ c, ∑ ℓ ∈ badLabels, if σ ∈ P.node ∧ σ c = ℓ then p σ else 0 := by
      calc _ = ∑ c, ∑ σ, ∑ ℓ ∈ badLabels, if σ ∈ P.node ∧ σ c = ℓ then p σ else 0 :=
            sum_congr rfl fun c _ => sum_comm
        _ = _ := sum_comm
    rw [heq]
    refine sum_le_sum fun σ _ => ?_
    split_ifs with hσ
    · obtain ⟨c₀, hc₀⟩ := exists_bad hx ha hσ
      have h1 : p σ ≤ ∑ ℓ ∈ badLabels, (if σ ∈ P.node ∧ σ c₀ = ℓ then p σ else 0) := by
        refine le_trans ?_ (single_le_sum (f := fun ℓ => if σ ∈ P.node ∧ σ c₀ = ℓ then p σ else 0)
          (fun ℓ _ => by split_ifs <;> [exact hp0 σ; exact le_rfl]) hc₀)
        simp [hσ]
      refine h1.trans ?_
      exact single_le_sum (f := fun c => ∑ ℓ ∈ badLabels,
          (if σ ∈ P.node ∧ σ c = ℓ then p σ else 0))
        (fun c _ => sum_nonneg fun ℓ _ => by split_ifs <;> [exact hp0 σ; exact le_rfl])
        (mem_univ c₀)
    · exact sum_nonneg fun c _ => sum_nonneg fun ℓ _ => by
        split_ifs <;> [exact hp0 σ; exact le_rfl]
  have hΔpos : (0 : ℝ) < Δ := by exact_mod_cast (show 0 < Δ by omega)
  have hcard : ((univ : Finset (Fin Δ)) ×ˢ badLabels).card = 3 * Δ := by
    rw [card_product, card_univ, Fintype.card_fin]; simp [badLabels]; ring
  obtain ⟨⟨c, ℓ⟩, hcℓ, hr⟩ : ∃ cℓ ∈ (univ : Finset (Fin Δ)) ×ˢ badLabels,
      (1 - q) / (3 * Δ) ≤ r cℓ.1 cℓ.2 := by
    refine exists_le_of_sum_le ⟨⟨⟨0, by omega⟩, .M⟩, by simp [badLabels]⟩ ?_
    rw [sum_const, hcard, nsmul_eq_mul]
    convert hcover using 1
    push_cast; field_simp
  have hℓ : ¬ E5 ℓ ℓ := not_E5_self ℓ (mem_product.1 hcℓ).2
  refine ⟨c, ?_⟩
  have hq := failProb_ge_invalid P p hp0 hp1 c
  have hsq := failProb_ge_sq P p hp0 c hℓ
  have hq0 : 0 ≤ q := sum_nonneg fun σ _ => by split_ifs <;> [exact le_rfl; exact hp0 σ]
  -- `1/Δ^8 ≤ 1/(36 Δ²)`
  have h8 : 1 / (Δ : ℝ) ^ 8 ≤ 1 / (36 * (Δ : ℝ) ^ 2) := by
    have h2 : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
    apply one_div_le_one_div_of_le (by positivity)
    have : (64 : ℝ) ≤ (Δ : ℝ) ^ 6 := by
      calc (64 : ℝ) = 2 ^ 6 := by norm_num
        _ ≤ (Δ : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) h2 6
    nlinarith [sq_nonneg ((Δ : ℝ)), pow_pos hΔpos 2]
  refine h8.trans ?_
  by_cases hqbig : 1 / (36 * (Δ : ℝ) ^ 2) ≤ q
  · exact hqbig.trans hq
  · push Not at hqbig
    have hq2 : q ≤ 1 / 2 := by
      have : 1 / (36 * (Δ : ℝ) ^ 2) ≤ 1 / 2 := by
        apply one_div_le_one_div_of_le (by norm_num)
        have h2 : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
        nlinarith
      linarith
    have hr' : 1 / (6 * (Δ : ℝ)) ≤ r c ℓ := by
      refine le_trans ?_ hr
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    calc 1 / (36 * (Δ : ℝ) ^ 2) = (1 / (6 * (Δ : ℝ))) ^ 2 := by field_simp; ring
      _ ≤ (r c ℓ) ^ 2 := pow_le_pow_left₀ (by positivity) hr' 2
      _ ≤ failProb P p c := hsq

/-- Lemma 15 is false for `Δ = 1` (with `x = 0 ≤ Δ - 1`, `a = 1`): on the 1-regular tree `K₂`, the
randomized 0-round algorithm that outputs `M` or `A` with probability `1/2` each fails with
probability only `1/2 < 1/Δ^8 = 1`. -/
theorem lemma_15_false_delta_one :
    ∃ p : (Fin 1 → L5) → ℝ, (∀ σ, 0 ≤ p σ) ∧ ∑ σ, p σ = 1 ∧
      ∀ c, failProb (Pi 1 1 0) p c < 1 / (1 : ℝ) ^ 8 := by
  classical
  let p : (Fin 1 → L5) → ℝ := fun σ => if σ 0 = .M ∨ σ 0 = .A then 1 / 2 else 0
  have hsum : ∀ f : (Fin 1 → L5) → ℝ, ∑ σ, f σ = ∑ ℓ : L5, f (fun _ => ℓ) := fun f =>
    (Fintype.sum_equiv (Equiv.funUnique (Fin 1) L5) _ _ fun σ => by
      congr 1; funext i; rw [Subsingleton.elim i default]; rfl)
  have huniv : (univ : Finset L5) = {.M, .P, .O, .A, .X} := rfl
  refine ⟨p, fun σ => by simp only [p]; split_ifs <;> norm_num, ?_, fun c => ?_⟩
  · rw [hsum, huniv]; simp [p]; norm_num
  · have hc : c = 0 := Subsingleton.elim _ _
    subst hc
    unfold failProb
    rw [hsum]
    simp only [hsum, huniv]
    simp [p, Pi, cnt, E5]
    norm_num

end Podc.MISTreeLowerBounds
