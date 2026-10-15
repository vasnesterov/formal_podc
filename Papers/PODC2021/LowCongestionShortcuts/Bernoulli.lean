-- CSLib candidate
import Mathlib

/-!
# Independent Bernoulli subsets, as finite sums

The probabilistic-method step of [GH21, Theorem 3.1] samples a random subset `S` of a finite set
`ι`, including every element independently with probability `p`. We do not use measure theory:
the probability of `S` is the explicit weight `p ^ |S| * (1 - p) ^ (|ι| - |S|)` and expectations
are finite weighted sums over `univ.powerset`.

* `bernWeight p S`: the weight of `S`.
* `sum_bernWeight_indicator`: `P[In ⊆ S ∧ S ∩ Out = ∅] = p ^ |In| * (1 - p) ^ |Out|` for disjoint
  `In`, `Out`.
* `exists_pos_of_sum_bernWeight_pos`: the probabilistic method — a positive expectation implies a
  positive outcome.
-/

namespace LowCongestionShortcuts

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The probability of the set `S` when each element of `ι` is included independently with
probability `p`. -/
def bernWeight (p : ℝ) (S : Finset ι) : ℝ := p ^ S.card * (1 - p) ^ (Fintype.card ι - S.card)

omit [DecidableEq ι] in
theorem bernWeight_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (S : Finset ι) :
    0 ≤ bernWeight p S :=
  mul_nonneg (pow_nonneg h0 _) (pow_nonneg (by linarith) _)

/-- `P[In ⊆ S ∧ S ∩ Out = ∅] = p ^ |In| * (1 - p) ^ |Out|` for disjoint `In`, `Out`. -/
theorem sum_bernWeight_indicator (p : ℝ) (In Out : Finset ι) (h : Disjoint In Out) :
    ∑ S ∈ univ.powerset, bernWeight p S * (if In ⊆ S ∧ Disjoint S Out then 1 else 0) =
      p ^ In.card * (1 - p) ^ Out.card := by
  classical
  set f : ι → ℝ := fun i => if i ∈ Out then 0 else p
  set g : ι → ℝ := fun i => if i ∈ In then 0 else 1 - p
  have key := Finset.prod_add f g (univ : Finset ι)
  have hl : ∏ i, (f i + g i) = p ^ In.card * (1 - p) ^ Out.card := by
    have : ∀ i, f i + g i = (if i ∈ In then p else 1) * (if i ∈ Out then 1 - p else 1) := by
      intro i
      by_cases hi : i ∈ In
      · have : i ∉ Out := Finset.disjoint_left.1 h hi
        simp [f, g, hi, this]
      · by_cases ho : i ∈ Out <;> simp [f, g, hi, ho]
    simp_rw [this, Finset.prod_mul_distrib, Finset.prod_ite_mem, univ_inter, prod_const]
  rw [hl] at key
  rw [key]
  refine Finset.sum_congr rfl fun t _ => ?_
  unfold bernWeight
  by_cases hIn : In ⊆ t
  · by_cases hOut : Disjoint t Out
    · rw [ite_eq_left ⟨hIn, hOut⟩, mul_one]
      have h1 : ∏ i ∈ t, f i = p ^ t.card := by
        rw [Finset.prod_congr rfl (g := fun _ => p), prod_const]
        intro i hi; simp [f, Finset.disjoint_left.1 hOut hi]
      have h2 : ∏ i ∈ univ \ t, g i = (1 - p) ^ (Fintype.card ι - t.card) := by
        rw [Finset.prod_congr rfl (g := fun _ => 1 - p), prod_const, card_sdiff_of_subset
          (subset_univ _), card_univ]
        intro i hi
        have : i ∉ In := fun h' => (mem_sdiff.1 hi).2 (hIn h')
        simp [g, this]
      rw [h1, h2]
    · rw [ite_eq_right (fun h' => hOut h'.2), mul_zero]
      obtain ⟨i, hit, hio⟩ := Finset.not_disjoint_iff.1 hOut
      have : ∏ i ∈ t, f i = 0 := Finset.prod_eq_zero hit (by simp [f, hio])
      rw [this, zero_mul]
  · rw [ite_eq_right (fun h' => hIn h'.1), mul_zero]
    obtain ⟨i, hii, hit⟩ := Finset.not_subset.1 hIn
    have : ∏ i ∈ univ \ t, g i = 0 :=
      Finset.prod_eq_zero (mem_sdiff.2 ⟨mem_univ _, hit⟩) (by simp [g, hii])
    rw [this, mul_zero]

theorem sum_bernWeight (p : ℝ) : ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S = 1 := by
  have := sum_bernWeight_indicator (ι := ι) p ∅ ∅ (disjoint_empty_left _)
  simpa using this

omit [DecidableEq ι] in
/-- The probabilistic method: if a weighted sum with nonnegative weights is positive, some
summand is positive. -/
theorem exists_pos_of_sum_bernWeight_pos {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) (X : Finset ι → ℝ)
    (h : 0 < ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * X S) : ∃ S, 0 < X S := by
  by_contra hc
  push Not at hc
  have : ∑ S ∈ (univ : Finset ι).powerset, bernWeight p S * X S ≤ 0 :=
    Finset.sum_nonpos fun S _ => mul_nonpos_of_nonneg_of_nonpos (bernWeight_nonneg h0 h1 S) (hc S)
  linarith

end LowCongestionShortcuts
