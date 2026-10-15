import Papers.PODC2024.Swiper.Construction

/-!
# Swiper: Weight Separation (Theorem 2.4) — an error and a corrected bound

**Paper's claim (Theorem 2.4 + Appendix A.2).** For `0 < α < β < 1` there is a WS solution with
`T ≤ (α + β)(1 - α) / (β - α) · n`; the proof takes `γ = (α + β) / 2`, `t_i = ⌊w_i s + γ⌋` with
`s = 2γ(1 - γ) n / ((β - α) W)`, and Swiper (Section 3) is claimed to respect this bound.

**What goes wrong.** The second case of Appendix A.2 ("analogously, by substitution of `1 - γ` in
place of `γ` ...") is not analogous: the rounding offset stays `γ`, not `1 - γ`, and the substitution
is valid only for `γ = 1/2`. Concretely (`swiper_ws_counterexample`): for weights `(1, 1, 15)`,
`α = 1/20`, `β = 1/10`, the paper's `s` gives `t = (0, 0, 7)`, which violates WS; and every
WS-valid member of Swiper's family with offset `γ` has `T ≥ 14 > 8.55`, the claimed bound
(`swiper_ws_family_exceeds_bound`). So Swiper's WS mode does **not** respect the claimed bound.
On this instance the optimum is `T = 2` (`counterexample_optimum`), but the *existence* part of
Theorem 2.4 is false as well: `ws_upper_bound_false` gives an instance (`α = 1/20`, `β = 1/10`,
`n = 21`) where every WS solution needs `T ≥ 63 > 59.85`.

**What we prove instead** (`ws_upper_bound`): with offset `c = (1 - d) / 2`, `d = β - α`, every
member of the family with `T ≥ (1 - d²) / (2d) · n` is WS-valid, so a WS solution with
`T ≤ ⌈(1 - (β - α)²) / (2 (β - α)) · n⌉` exists. This bound only depends on the gap `β - α` and is
better than the paper's when `α + β` is close to `1` (e.g. `α = 0.3, β = 0.7`: `1.05 n` vs `1.75 n`),
worse when `α + β` is small. We also prove the symmetry `WS(α, β) = WS(1 - β, 1 - α)`
(`isWS_iff_compl`), which shows that the paper's (asymmetric) bound could at best be replaced by the
minimum of it and its mirror image.
-/

namespace Papers.PODC2024.Swiper

open Finset Cslib.Apportionment

variable {ι : Type*} [Fintype ι]

/-- **Symmetry of Weight Separation**: `WS(α, β)` and `WS(1 - β, 1 - α)` have the same solutions
(complement both sets). -/
theorem isWS_iff_compl {α β : ℝ} {w : ι → ℝ} {t : ι → ℕ} :
    IsWS α β w t ↔ IsWS (1 - β) (1 - α) w t := by
  classical
  have hw : ∀ S : Finset ι, ∑ i ∈ Sᶜ, w i = ∑ i, w i - ∑ i ∈ S, w i := fun S => by
    rw [← Finset.sum_compl_add_sum S]; ring
  have ht : ∀ S : Finset ι, ∑ i ∈ Sᶜ, (t i : ℝ) = ∑ i, (t i : ℝ) - ∑ i ∈ S, (t i : ℝ) :=
    fun S => by rw [← Finset.sum_compl_add_sum S]; ring
  constructor
  · intro h S₁ S₂ h₁ h₂
    have := h S₂ᶜ S₁ᶜ (by rw [hw]; linarith) (by rw [hw]; linarith)
    rw [ht, ht] at this
    linarith
  · intro h S₁ S₂ h₁ h₂
    have := h S₂ᶜ S₁ᶜ (by rw [hw]; linarith) (by rw [hw]; linarith)
    rw [ht, ht] at this
    linarith

/-- The corrected Weight Separation bound `(1 - d²) / (2d) · n` with `d = β - α`. -/
noncomputable def wsBound (α β : ℝ) (n : ℕ) : ℝ := (1 - (β - α) ^ 2) / (2 * (β - α)) * n

/-- **Key lemma for WS (corrected).** A rounding of `w * s` with offset `(1 - d) / 2`
(`d = β - α`) with `T ≥ (1 - d²) / (2d) · n` satisfies the Weight Separation constraint. -/
theorem isWS_of_rounds {α β s : ℝ} {w : ι → ℝ} {t : ι → ℕ} (hαβ : α < β) (hd : β - α < 1)
    (hs : 0 ≤ s) (ht : Rounds w ((1 - (β - α)) / 2) s t)
    (hT : wsBound α β (Fintype.card ι) ≤ ∑ i, (t i : ℝ)) : IsWS α β w t := by
  classical
  intro S₁ S₂ h₁ h₂
  by_contra hp
  push Not at hp
  set d := β - α with hd_def
  have hd0 : 0 < d := by linarith
  have hT' : (1 - d ^ 2) / 2 * (Fintype.card ι) ≤ d * ∑ i, (t i : ℝ) := by
    unfold wsBound at hT
    rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)] at hT
    nlinarith
  rcases hs.eq_or_lt with rfl | hs
  · have h0 : ∀ i, t i = 0 := fun i => ht.eq_zero_of_lt (by simp; linarith)
    simp only [h0, Nat.cast_zero, Finset.sum_const_zero, mul_zero] at hT'
    have hcard : (Fintype.card ι : ℝ) ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos (by nlinarith : (0 : ℝ) < (1 - d ^ 2) / 2) hc
      linarith
    have hcard0 : Fintype.card ι = 0 := by exact_mod_cast le_antisymm hcard (by positivity)
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard0
    simp [Finset.eq_empty_of_isEmpty S₂] at h₂
  · have key : ∀ i, (d + ((if i ∈ S₁ then 1 else 0) - (if i ∈ S₂ then 1 else 0))) *
        ((t i : ℝ) - w i * s) ≤ (1 - d ^ 2) / 2 := by
      intro i
      have h1 := (ht i).1
      have h2 := (ht i).2
      split_ifs <;> nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ univ) => key i)
    simp only [add_mul, sub_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_mul] at hsum
    have hgap : d * (s * ∑ i, w i) < s * ∑ i ∈ S₂, w i - s * ∑ i ∈ S₁, w i := by
      rw [hd_def]; nlinarith
    nlinarith

/-- **Weight Separation upper bound (corrected Theorem 2.4).** For `0 < α < β < 1` and
non-negative weights with `W ≠ 0`, there is a WS solution with
`T ≤ ⌈(1 - (β - α)²) / (2 (β - α)) · n⌉`. -/
theorem ws_upper_bound {α β : ℝ} (hα : 0 < α) (hαβ : α < β) (hβ : β < 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i ≠ 0) :
    ∃ t : ι → ℕ, IsWS α β w t ∧
      ∑ i, t i ≤ ⌈(1 - (β - α) ^ 2) / (2 * (β - α)) * Fintype.card ι⌉₊ := by
  obtain ⟨s, hs, t, ht, hsum⟩ := exists_rounds_sum_eq hw (exists_pos_of_sum_ne_zero hw hW)
    (c := (1 - (β - α)) / 2) (by linarith) (by linarith) ⌈wsBound α β (Fintype.card ι)⌉₊
  refine ⟨t, isWS_of_rounds hαβ (by linarith) hs ht ?_, hsum.le⟩
  rw [← Nat.cast_sum, hsum]
  exact Nat.le_ceil _

/-! ## The counterexample to the Weight Separation part of Swiper -/

/-- Paper's claimed WS bound `(α + β)(1 - α) / (β - α) · n`. -/
noncomputable def wsPaperBound (α β : ℝ) (n : ℕ) : ℝ := (α + β) * (1 - α) / (β - α) * n

/-- The multiplier `s = 2γ(1 - γ) n / ((β - α) W)` of Appendix A.2, `γ = (α + β) / 2`. -/
noncomputable def wsPaperS (α β : ℝ) (n : ℕ) (W : ℝ) : ℝ :=
  2 * ((α + β) / 2) * (1 - (α + β) / 2) * n / ((β - α) * W)

/-- The counterexample weights `(1, 1, 15)`. -/
def cw : Fin 3 → ℝ := ![1, 1, 15]

theorem sum_fin3 (S : Finset (Fin 3)) (f : Fin 3 → ℝ) :
    ∑ i ∈ S, f i = (if 0 ∈ S then f 0 else 0) + (if 1 ∈ S then f 1 else 0) +
      (if 2 ∈ S then f 2 else 0) := by
  rw [← Finset.univ_inter S, ← Finset.sum_ite_mem, Fin.sum_univ_three]
  simp

theorem cw_sum : ∑ i, cw i = 17 := by
  simp [cw, Fin.sum_univ_three]; norm_num

/-- **Counterexample, part 1.** Appendix A.2's assignment `⌊w_i s + γ⌋` at the paper's `s` is not
a WS solution for `w = (1, 1, 15)`, `α = 1/20`, `β = 1/10` (it is `(0, 0, 7)`). -/
theorem swiper_ws_counterexample :
    ts cw ((1 / 20 + 1 / 10) / 2) (wsPaperS (1 / 20) (1 / 10) 3 (∑ i, cw i)) = ![0, 0, 7] ∧
    ¬ IsWS (1 / 20) (1 / 10) cw
      (ts cw ((1 / 20 + 1 / 10) / 2) (wsPaperS (1 / 20) (1 / 10) 3 (∑ i, cw i))) := by
  have heq : ts cw ((1 / 20 + 1 / 10) / 2) (wsPaperS (1 / 20) (1 / 10) 3 (∑ i, cw i)) =
      ![0, 0, 7] := by
    funext i
    rw [cw_sum]
    fin_cases i <;> simp [ts, cw, wsPaperS] <;> norm_num
  refine ⟨heq, fun h => ?_⟩
  rw [heq] at h
  have := h ∅ {0, 1} (by rw [cw_sum]; simp) (by rw [cw_sum, sum_fin3]; simp [cw]; norm_num)
  simp at this

/-- **Counterexample, part 2.** On the same instance, every WS-valid member of Swiper's family with
offset `γ = (α + β)/2` (i.e. every `t` with `w_i s + γ - 1 ≤ t_i ≤ w_i s + γ`, which includes every
`t(s, k)` of Section 3.1 and hence Swiper's output) has `T ≥ 14`, while the paper's bound is
`(α + β)(1 - α)/(β - α) · n = 8.55`. -/
theorem swiper_ws_family_exceeds_bound :
    wsPaperBound (1 / 20) (1 / 10) 3 = 171 / 20 ∧
    ∀ s, 0 ≤ s → ∀ t : Fin 3 → ℕ, Rounds cw ((1 / 20 + 1 / 10) / 2) s t →
      IsWS (1 / 20) (1 / 10) cw t → 14 ≤ ∑ i, t i := by
  refine ⟨by unfold wsPaperBound; norm_num, fun s hs t ht hws => ?_⟩
  have h01 : 1 ≤ t 0 ∨ 1 ≤ t 1 := by
    by_contra hc
    push Not at hc
    have h0 : t 0 = 0 := by omega
    have h1 : t 1 = 0 := by omega
    have := hws ∅ {0, 1} (by rw [cw_sum]; simp) (by rw [cw_sum, sum_fin3]; simp [cw]; norm_num)
    simp [h0, h1] at this
  have hs' : 37 / 40 ≤ s := by
    rcases h01 with h | h
    · have := (ht 0).2
      have h' : (1 : ℝ) ≤ t 0 := by exact_mod_cast h
      simp [cw] at this; linarith
    · have := (ht 1).2
      have h' : (1 : ℝ) ≤ t 1 := by exact_mod_cast h
      simp [cw] at this; linarith
  have h2 : (12 : ℝ) < t 2 := by
    have := (ht 2).1
    simp [cw] at this; linarith
  have h2' : 13 ≤ t 2 := by exact_mod_cast h2
  rw [Fin.sum_univ_three]
  omega

/-- **Counterexample, part 3.** The optimum on that instance is tiny: `t = (1, 0, 1)` is a WS
solution with `T = 2`, so the instance does not refute the existence claim of Theorem 2.4. -/
theorem counterexample_optimum : IsWS (1 / 20) (1 / 10) cw ![1, 0, 1] := by
  intro S₁ S₂ h₁ h₂
  rw [cw_sum, sum_fin3] at h₁ h₂
  rw [sum_fin3, sum_fin3]
  simp only [cw] at h₁ h₂
  by_cases a0 : (0 : Fin 3) ∈ S₁ <;> by_cases a1 : (1 : Fin 3) ∈ S₁ <;>
    by_cases a2 : (2 : Fin 3) ∈ S₁ <;> by_cases b0 : (0 : Fin 3) ∈ S₂ <;>
    by_cases b2 : (2 : Fin 3) ∈ S₂ <;> by_cases b1 : (1 : Fin 3) ∈ S₂ <;>
    simp [a0, a1, a2, b0, b1, b2] at h₁ h₂ ⊢ <;> linarith

/-! ## Theorem 2.4 itself is false

Instance found by numerical search (helper subagent): `α = 1/20`, `β = 1/10`, `n = 21`; eight
"heavy" parties of weight `14` and thirteen parties of weight `1` (`W = 125`, `αW = 6.25`,
`βW = 12.5`). Every WS solution has `T ≥ 63`, while the paper's bound is
`(α + β)(1 - α)/(β - α) · 21 = 59.85`. The refutation uses overlapping sets (`S₁ ⊆ S₂`), which the
paper's definition of WS allows; under a disjoint-sets reading it would not be a counterexample.
(Numerically, the optimum is exactly `63`: `7` tickets per
heavy party, one ticket for seven of the light parties.)

Argument: let `P` be the light parties holding a ticket. If `|P| < 6`, then `S₁ = P` (weight `< 6`)
and `S₂ =` all light parties (weight `13`) have the same number of tickets — contradiction. Otherwise
(`|P| ≥ 6`) some `A ⊆ P` with `|A| = 6` has `t(A) ≥ 6`, so every heavy party (weight `14 > 12.5`) has `≥ 7`
tickets and the light parties together have `≥ 7`, giving `T ≥ 8 · 7 + 7 = 63`. -/

/-- Weights of the counterexample to Theorem 2.4: parties `0, …, 7` have weight `14`, parties
`8, …, 20` weight `1`. -/
def ws24w : Fin 21 → ℝ := fun i => if (i : ℕ) < 8 then 14 else 1

/-- The heavy parties. -/
def ws24heavy : Finset (Fin 21) := univ.filter fun i => (i : ℕ) < 8

/-- The light parties. -/
def ws24light : Finset (Fin 21) := univ.filter fun i => ¬ (i : ℕ) < 8

theorem ws24_sum_light {A : Finset (Fin 21)} (hA : A ⊆ ws24light) :
    ∑ i ∈ A, ws24w i = A.card := by
  rw [Finset.sum_congr rfl (g := fun _ => (1 : ℝ)), Finset.sum_const, nsmul_eq_mul, mul_one]
  intro i hi
  have := hA hi
  simp only [ws24light, mem_filter, mem_univ, true_and] at this
  simp [ws24w, this]

theorem ws24_total : ∑ i, ws24w i = 125 := by
  simp [ws24w, Fin.sum_univ_succ]
  norm_num

/-- **Theorem 2.4 is false.** For `α = 1/20`, `β = 1/10` and the weights `ws24w` (`n = 21`),
every Weight Separation solution has `T ≥ 63`, but the paper's bound is
`(α + β)(1 - α)/(β - α) · n = 59.85 < 63`. -/
theorem ws_upper_bound_false :
    wsPaperBound (1 / 20) (1 / 10) 21 = 1197 / 20 ∧
    (∀ t : Fin 21 → ℕ, IsWS (1 / 20) (1 / 10) ws24w t → 63 ≤ ∑ i, t i) ∧
    ¬ ∃ t : Fin 21 → ℕ, IsWS (1 / 20) (1 / 10) ws24w t ∧
      (∑ i, t i : ℝ) ≤ wsPaperBound (1 / 20) (1 / 10) 21 := by
  have hb : wsPaperBound (1 / 20) (1 / 10) 21 = 1197 / 20 := by
    unfold wsPaperBound; norm_num
  have main : ∀ t : Fin 21 → ℕ, IsWS (1 / 20) (1 / 10) ws24w t → 63 ≤ ∑ i, t i := by
    intro t ht
    classical
    have hlc : ws24light.card = 13 := by decide
    have hhc : ws24heavy.card = 8 := by decide
    have hW := ws24_total
    -- light parties with a ticket
    set P := ws24light.filter fun i => 1 ≤ t i with hP
    have hPsub : P ⊆ ws24light := Finset.filter_subset _ _
    -- the light parties together beat any light set of weight < 6.25
    have hall : ∀ A ⊆ ws24light, A.card ≤ 6 → ∑ i ∈ A, t i < ∑ i ∈ ws24light, t i := by
      intro A hA hcard
      have hc6 : (A.card : ℝ) ≤ 6 := by exact_mod_cast hcard
      have := ht A ws24light (by rw [ws24_sum_light hA, hW]; linarith)
        (by rw [ws24_sum_light le_rfl, hW, hlc]; norm_num)
      exact_mod_cast this
    have hsumP : ∑ i ∈ P, t i = ∑ i ∈ ws24light, t i := by
      rw [hP, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      split_ifs with h
      · rfl
      · omega
    have hPcard : 6 ≤ P.card := by
      by_contra hc
      push Not at hc
      have := hall P hPsub (by omega)
      omega
    obtain ⟨A, hAP, hAcard⟩ := Finset.exists_subset_card_eq hPcard
    have hA6 : 6 ≤ ∑ i ∈ A, t i := by
      have := Finset.card_nsmul_le_sum A t 1 (fun i hi => (mem_filter.1 (hAP hi)).2)
      simpa [hAcard] using this
    have hAlight : ∑ i ∈ A, ws24w i < 1 / 20 * ∑ i, ws24w i := by
      rw [ws24_sum_light (hAP.trans hPsub), hW, hAcard]; norm_num
    have hheavy : ∀ h ∈ ws24heavy, 7 ≤ t h := by
      intro h hh
      have hh' : (h : ℕ) < 8 := (mem_filter.1 hh).2
      have := ht A {h} hAlight (by rw [hW]; simp [ws24w, hh']; norm_num)
      simp only [Finset.sum_singleton] at this
      have : ∑ i ∈ A, t i < t h := by exact_mod_cast this
      omega
    have hlight : 7 ≤ ∑ i ∈ ws24light, t i := by
      have := hall A (hAP.trans hPsub) (by omega)
      omega
    have hH : 8 * 7 ≤ ∑ i ∈ ws24heavy, t i := by
      have := Finset.card_nsmul_le_sum ws24heavy t 7 hheavy
      simpa [hhc] using this
    have hsplit : ∑ i, t i = ∑ i ∈ ws24heavy, t i + ∑ i ∈ ws24light, t i :=
      (Finset.sum_filter_add_sum_filter_not univ (fun i : Fin 21 => (i : ℕ) < 8) t).symm
    omega
  refine ⟨hb, main, fun ⟨t, ht, hT⟩ => ?_⟩
  have h63 : (63 : ℝ) ≤ ∑ i, (t i : ℝ) := by exact_mod_cast main t ht
  rw [hb] at hT
  linarith

end Papers.PODC2024.Swiper
