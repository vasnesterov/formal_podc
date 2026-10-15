import Papers.PODC2024.Swiper.Defs

/-!
# Swiper: upper bounds for Weight Restriction and Weight Qualification

Theorem 2.1, Theorem 2.2 and Corollary 2.3 of Tonkikh–Freitas (PODC 2024), with the proof of
Appendix A.1 reorganised around one *key lemma*:

`isWR_of_rounds`: if `t` rounds `w * s` with offset `αw` (i.e. `w i s + αw - 1 ≤ t i ≤ w i s + αw`,
the family `t(s, k)` of Section 3.1) and `T ≥ αw (1 - αw) / (αn - αw) · n`, then `t` satisfies the
Weight Restriction constraint.

This is exactly the paper's computation (the paper states it in contrapositive form: "any invalid
ticket assignment of this form yields fewer tickets than the bound"). Together with the fact that
every total `T` is attained by such a rounding (`Cslib.Apportionment.exists_rounds_sum_eq`), it gives
Theorem 2.1 without the "locally minimal `s*`" machinery; the paper's own route through `s*` is
formalized in `Papers.PODC2024.Swiper.Construction`.
-/

namespace Papers.PODC2024.Swiper

open Finset Cslib.Apportionment

variable {ι : Type*} [Fintype ι]

/-- **Key lemma (Appendix A.1, contrapositive form).** A rounding of `w * s` with offset `αw` whose
total is at least `αw (1 - αw) / (αn - αw) · n` satisfies the Weight Restriction constraint. -/
theorem isWR_of_rounds {αw αn s : ℝ} {w : ι → ℝ} {t : ι → ℕ} (hαw : 0 < αw) (hαw1 : αw < 1)
    (hlt : αw < αn) (hs : 0 ≤ s) (ht : Rounds w αw s t)
    (hT : wrBound αw αn (Fintype.card ι) ≤ ∑ i, (t i : ℝ)) : IsWR αw αn w t := by
  classical
  intro S hS
  by_contra hp
  push Not at hp
  have hgap : 0 < αn - αw := by linarith
  have hT' : αw * (1 - αw) * (Fintype.card ι) ≤ (αn - αw) * ∑ i, (t i : ℝ) := by
    unfold wrBound at hT
    rw [div_mul_eq_mul_div, div_le_iff₀ hgap] at hT
    linarith
  rcases hs.eq_or_lt with rfl | hs
  · -- `s = 0`: no tickets at all, hence no parties, contradicting `w(S) < αw W`.
    have h0 : ∀ i, t i = 0 := fun i => ht.eq_zero_of_lt (by simpa using hαw1)
    simp only [h0, Nat.cast_zero, Finset.sum_const_zero, mul_zero] at hT'
    have hcard : (Fintype.card ι : ℝ) ≤ 0 := by
      by_contra hc
      push Not at hc
      have := mul_pos (mul_pos hαw (by linarith : (0 : ℝ) < 1 - αw)) hc
      linarith
    have hcard0 : Fintype.card ι = 0 := by exact_mod_cast le_antisymm hcard (by positivity)
    have : IsEmpty ι := Fintype.card_eq_zero_iff.mp hcard0
    simp [Finset.eq_empty_of_isEmpty S] at hS
  · -- `s > 0`: the computation of Appendix A.1.
    -- per-party bound
    have key : ∀ i, (if i ∈ S then (1 - αw) * ((t i : ℝ) - w i * s)
        else αw * (w i * s - t i)) ≤ αw * (1 - αw) := by
      intro i
      have h1 := (ht i).1
      have h2 := (ht i).2
      split_ifs
      · nlinarith
      · nlinarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ univ) => key i)
    rw [sum_ite_mem_compl, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    simp only [← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.sum_mul] at hsum
    have hSs : s * ∑ i ∈ S, w i < αw * (s * ∑ i, w i) := by nlinarith
    nlinarith

/-- **Theorem 2.1 (WR upper bound).** For `0 < αw < αn < 1` and non-negative weights with
`W ≠ 0`, there is a ticket assignment satisfying the Weight Restriction constraint, with `T ≠ 0`
(viable), and with `T ≤ ⌈αw (1 - αw) / (αn - αw) · n⌉`. -/
theorem wr_upper_bound {αw αn : ℝ} (hαw : 0 < αw) (hlt : αw < αn) (hαn : αn < 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i ≠ 0) :
    ∃ t : ι → ℕ, Viable αw αn w t ∧
      ∑ i, t i ≤ ⌈αw * (1 - αw) / (αn - αw) * Fintype.card ι⌉₊ := by
  obtain ⟨s, hs, t, ht, hsum⟩ := exists_rounds_sum_eq hw (exists_pos_of_sum_ne_zero hw hW)
    hαw.le (by linarith) ⌈wrBound αw αn (Fintype.card ι)⌉₊
  have hWR : IsWR αw αn w t := isWR_of_rounds hαw (by linarith) hlt hs ht (by
    rw [← Nat.cast_sum, hsum]; exact Nat.le_ceil _)
  exact ⟨t, ⟨hWR.sum_ne_zero (sum_pos_of_sum_ne_zero hw hW) hαw, hWR⟩, hsum.le⟩

/-- **Theorem 2.2.** Weight Qualification with parameters `(βw, βn)` and Weight Restriction with
parameters `(1 - βw, 1 - βn)` have exactly the same solutions. (No assumption on the parameters or
the weights is needed.) -/
theorem isWQ_iff_isWR {βw βn : ℝ} {w : ι → ℝ} {t : ι → ℕ} :
    IsWQ βw βn w t ↔ IsWR (1 - βw) (1 - βn) w t := by
  classical
  have hw : ∀ S : Finset ι, ∑ i ∈ Sᶜ, w i = ∑ i, w i - ∑ i ∈ S, w i := fun S => by
    rw [← Finset.sum_compl_add_sum S]; ring
  have ht : ∀ S : Finset ι, ∑ i ∈ Sᶜ, (t i : ℝ) = ∑ i, (t i : ℝ) - ∑ i ∈ S, (t i : ℝ) :=
    fun S => by rw [← Finset.sum_compl_add_sum S]; ring
  constructor
  · intro h S hS
    have := h Sᶜ (by rw [hw]; linarith)
    rw [ht] at this
    linarith
  · intro h S hS
    have := h Sᶜ (by rw [hw]; linarith)
    rw [ht] at this
    linarith

/-- **Corollary 2.3 (WQ upper bound).** For `0 < βn < βw < 1` and non-negative weights with
`W ≠ 0`, there is a solution of Weight Qualification with `T ≤ ⌈βw (1 - βw) / (βw - βn) · n⌉`
(and `T ≠ 0`). -/
theorem wq_upper_bound {βw βn : ℝ} (hβn : 0 < βn) (hlt : βn < βw) (hβw : βw < 1)
    (w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hW : ∑ i, w i ≠ 0) :
    ∃ t : ι → ℕ, IsWQ βw βn w t ∧ ∑ i, t i ≠ 0 ∧
      ∑ i, t i ≤ ⌈βw * (1 - βw) / (βw - βn) * Fintype.card ι⌉₊ := by
  obtain ⟨t, ht, hT⟩ := wr_upper_bound (αw := 1 - βw) (αn := 1 - βn) (by linarith) (by linarith)
    (by linarith) w hw hW
  refine ⟨t, isWQ_iff_isWR.2 ht.2, ht.1, ?_⟩
  convert hT using 3
  ring

end Papers.PODC2024.Swiper
