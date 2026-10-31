import Papers.PODC2021.WakeUpMatching.Lemma52
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Lemma 5.6: a "lost opportunity" has probability at most `1 − r/(6e)`

Dani, Gupta, Hayes, Pettie, PODC 2021 (arXiv:2104.09096v2), Lemma 5.6 (one-round form).

`Z(v, t) = 1` iff round `t` is good (`Δ(t−1) r(t) < 1/2`), `v` is still unmatched after round
`t`, and `d(v, t) ≥ 1/(3 r(t))`. Conditioned on `M(t−1)` (fixed partner variables), goodness is
determined; when `t` is not good `Z ≡ 0`. For a good round we prove
`P(v unmatched after the round ∧ 3 r d(v, t) ≥ 1) ≤ 1 − r/(6e)`, following the paper: the events
"`v` is matched to `w`" (`w ∈ N(v, t−1)`) are disjoint and each has probability
`≥ r²/2 (1 − r)^(Δ−1) ≥ r²/(2e)` (Lemma 5.2 and `1 − x ≥ e^{−2x}` on `[0, 1/2]`).
-/

set_option linter.unusedSectionVars false

namespace Podc.WakeUpMatching

open Finset Fintype

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem roleLaw_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (a : Role) : 0 ≤ roleLaw r a := by
  cases a <;> simp [roleLaw] <;> linarith

/-- The role law is a probability distribution, hence so is the product law. -/
theorem prob_true (r : ℝ) : prob (V := V) r (fun _ => True) = 1 := by
  unfold prob
  rw [filter_true_of_mem (fun _ _ => trivial), ← piFinset_univ,
    ← prod_univ_sum (κ := fun _ => Role) _ (fun _ a => roleLaw r a)]
  have : ∑ a : Role, roleLaw r a = 1 := by simp [Finset.univ, Fintype.elems, roleLaw]; ring
  simp [this]

theorem prob_mono {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {E F : (V → Role) → Prop}
    [DecidablePred E] [DecidablePred F] (h : ∀ ρ, E ρ → F ρ) : prob r E ≤ prob r F :=
  sum_le_sum_of_subset_of_nonneg (fun ρ hρ => by simp at hρ ⊢; exact h ρ hρ)
    (fun ρ _ _ => prod_nonneg fun u _ => roleLaw_nonneg hr0 hr1 _)

theorem prob_not (r : ℝ) (E : (V → Role) → Prop) [DecidablePred E] :
    prob r (fun ρ => ¬ E ρ) = 1 - prob r E := by
  rw [← prob_true (V := V) r]
  unfold prob
  rw [filter_true_of_mem (fun _ _ => trivial), ← sum_filter_add_sum_filter_not univ E]
  ring

theorem prob_false {r : ℝ} {E : (V → Role) → Prop} [DecidablePred E] (h : ∀ ρ, ¬ E ρ) :
    prob r E = 0 := by
  unfold prob; rw [filter_false_of_mem (fun ρ _ => h ρ)]; simp

/-- `1 − x ≥ e^{−2x}` for `0 ≤ x ≤ 1/2`. -/
theorem exp_neg_two_mul_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2) :
    Real.exp (-(2 * x)) ≤ 1 - x := by
  have h1 : 1 + 2 * x ≤ Real.exp (2 * x) := by linarith [Real.add_one_le_exp (2 * x)]
  have hpos : 0 < Real.exp (2 * x) := Real.exp_pos _
  rw [Real.exp_neg, inv_le_iff_one_le_mul₀ hpos]
  nlinarith

/-- Residual degrees do not increase. -/
theorem resN_round_subset (partner : V → Option V) (ρ : V → Role) (v : V) :
    resN G (round G partner ρ) v ⊆ resN G partner v := by
  intro u hu
  simp only [resN, mem_filter, mem_univ, true_and] at hu ⊢
  refine ⟨hu.1, ?_⟩
  by_contra h
  obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 h
  have := round_mono (G := G) (ρ := ρ) hw
  rw [hu.2] at this; cases this

/-- **Lemma 5.6** (one round, `t` good). If every unmatched vertex has residual degree at most
`Δ` and `Δ r < 1/2` (round `t` is good), `0 < r ≤ 1/2`, then the probability that `v` stays
unmatched and still has residual degree `≥ 1/(3r)` after the round is at most `1 − r/(6e)`. -/
theorem lemma_5_6 (partner : V → Option V) {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1 / 2) {Δ : ℕ}
    (hΔ : ∀ u, partner u = none → #(resN G partner u) ≤ Δ) (hgood : (Δ : ℝ) * r < 1 / 2)
    (v : V) :
    prob r (fun ρ => round G partner ρ v = none ∧
      1 ≤ 3 * r * (#(resN G (round G partner ρ) v) : ℝ)) ≤ 1 - r / (6 * Real.exp 1) := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hbound : 0 ≤ 1 - r / (6 * Real.exp 1) := by
    have : r / (6 * Real.exp 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      have := Real.add_one_le_exp 1
      linarith
    linarith
  -- trivial cases
  by_cases hv : partner v = none
  swap
  · rw [prob_false]; · exact hbound
    rintro ρ ⟨h, -⟩
    obtain ⟨w, hw⟩ := Option.ne_none_iff_exists'.1 hv
    rw [round_mono hw] at h; cases h
  by_cases hd : 1 ≤ 3 * r * (#(resN G partner v) : ℝ)
  swap
  · rw [prob_false]; · exact hbound
    rintro ρ ⟨-, h⟩
    apply hd
    refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
    exact_mod_cast card_le_card (resN_round_subset partner ρ v)
  -- main case
  set N := resN G partner v
  have hr1' : r ≤ 1 := by linarith
  -- each edge forms with probability `≥ r²/(2e)`
  have hexp : Real.exp (-1) ≤ (1 - r) ^ (Δ - 1) := by
    have h2 : 2 * r * ((Δ - 1 : ℕ) : ℝ) ≤ 1 := by
      have : ((Δ - 1 : ℕ) : ℝ) ≤ Δ := by exact_mod_cast Nat.sub_le Δ 1
      nlinarith
    calc Real.exp (-1) ≤ Real.exp (-(2 * r)) ^ (Δ - 1) := by
          rw [← Real.exp_nat_mul]; apply Real.exp_le_exp.2; nlinarith
      _ ≤ (1 - r) ^ (Δ - 1) :=
          pow_le_pow_left₀ (Real.exp_pos _).le (exp_neg_two_mul_le hr0.le hr1) _
  have hedge : ∀ w ∈ N, r ^ 2 / 2 * Real.exp (-1) ≤
      prob r (fun ρ => round G partner ρ v = some w) := by
    intro w hw
    simp only [N, resN, mem_filter, mem_univ, true_and] at hw
    refine le_trans ?_ (lemma_5_2 hw.1 hv hw.2 hr0.le hr1' (hΔ v hv) (hΔ w hw.2))
    exact mul_le_mul_of_nonneg_left hexp (by positivity)
  -- the events `round v = some w` are disjoint
  have hsum : ∑ w ∈ N, prob r (fun ρ => round G partner ρ v = some w) ≤
      prob r (fun ρ => round G partner ρ v ≠ none) := by
    unfold prob
    rw [← sum_biUnion]
    · refine sum_le_sum_of_subset_of_nonneg (fun ρ hρ => ?_)
        (fun ρ _ _ => prod_nonneg fun u _ => roleLaw_nonneg hr0.le hr1' _)
      simp only [mem_biUnion, mem_filter, mem_univ, true_and] at hρ ⊢
      obtain ⟨w, -, hw⟩ := hρ
      simp [hw]
    · intro w₁ _ w₂ _ hne
      simp only [Function.onFun]
      rw [disjoint_left]
      intro ρ h1 h2
      simp only [mem_filter] at h1 h2
      rw [h1.2] at h2
      exact hne (Option.some_injective _ h2.2)
  have hcard : (1 : ℝ) / (3 * r) ≤ #N := by
    rw [div_le_iff₀ (by positivity)]; linarith
  calc prob r (fun ρ => round G partner ρ v = none ∧
          1 ≤ 3 * r * (#(resN G (round G partner ρ) v) : ℝ))
      ≤ prob r (fun ρ => ¬ (round G partner ρ v ≠ none)) :=
        prob_mono hr0.le hr1' (fun ρ h => by simpa using h.1)
    _ = 1 - prob r (fun ρ => round G partner ρ v ≠ none) := prob_not r _
    _ ≤ 1 - ∑ w ∈ N, prob r (fun ρ => round G partner ρ v = some w) := by linarith
    _ ≤ 1 - #N * (r ^ 2 / 2 * Real.exp (-1)) := by
        have := sum_le_sum hedge
        simp only [sum_const, nsmul_eq_mul] at this
        linarith
    _ ≤ 1 - 1 / (3 * r) * (r ^ 2 / 2 * Real.exp (-1)) := by
        have : 0 ≤ r ^ 2 / 2 * Real.exp (-1) := by positivity
        nlinarith
    _ = 1 - r / (6 * Real.exp 1) := by
        rw [Real.exp_neg]; field_simp; ring

end Podc.WakeUpMatching
