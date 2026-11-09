import Mathlib

/-!
# Searching for a token in `N` locked boxes in `D` rounds: the model

Bar-Noy, Cheilaris, Feng, Levin, *Finding mobile data under delay constraints with searching costs*,
PODC 2010, Section 2.

A token is in box `i` with probability `p i`; unlocking box `i` costs `w i`. A search strategy for
`D` rounds is an ordered partition `⟨A₁, …, A_D⟩` of the boxes; we represent it as the map
`A : Fin n → Fin D` sending each box to the round in which it is unlocked (empty rounds are
allowed, see `differencies.md`). If the token is in box `i`, the searcher pays for all boxes
unlocked in rounds `≤ A i`; `cost` is the expected payment.

Algorithm FRO ("follow ratio order") assumes the boxes are indexed in non-increasing order of
`p i / w i` (`RatioSorted`, stated without division) and returns a minimum-cost strategy among
those that *respect* this order, i.e. among monotone maps `Fin n → Fin D` (`IsFRO`). Ties in the
ratio order are resolved by the indexing, so a statement "for every `RatioSorted` instance and
every `IsFRO` strategy" covers every tie-breaking (an adversarial one in particular).
-/

namespace Podc.MobileDataSearch

open Finset

variable {n D : ℕ}

/-- A search strategy for `D` rounds: box `i` is unlocked in round `A i`. -/
abbrev Strategy (n D : ℕ) := Fin n → Fin D

/-- Expected cost of a strategy: with probability `p i` the token is in box `i`, and then the
searcher pays the costs of all boxes unlocked in rounds `≤ A i`. -/
def cost (p w : Fin n → ℝ) (A : Strategy n D) : ℝ :=
  ∑ i, p i * ∑ j ∈ univ.filter (fun j => A j ≤ A i), w j

/-- Round sums: `roundSum p A d = P_d` (round probability), `roundSum w A d = W_d` (round
cost). -/
def roundSum (f : Fin n → ℝ) (A : Strategy n D) (d : Fin D) : ℝ :=
  ∑ i ∈ univ.filter (fun i => A i = d), f i

/-- Regrouping a sum `∑ i, f i * F (A i)` by rounds. -/
lemma sum_mul_comp_eq (f : Fin n → ℝ) (A : Strategy n D) (F : Fin D → ℝ) :
    ∑ i, f i * F (A i) = ∑ d, roundSum f A d * F d := by
  rw [← Finset.sum_fiberwise univ A (fun i => f i * F (A i))]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [roundSum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.1 hi).2]

/-- The cost of the boxes unlocked up to round `d` is `∑_{e ≤ d} W_e`. -/
lemma sum_filter_le_eq (f : Fin n → ℝ) (A : Strategy n D) (d : Fin D) :
    ∑ j ∈ univ.filter (fun j => A j ≤ d), f j =
      ∑ e ∈ univ.filter (fun e => e ≤ d), roundSum f A e := by
  rw [Finset.sum_filter, Finset.sum_filter]
  have := sum_mul_comp_eq f A (fun e => if e ≤ d then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at this
  exact this

/-- The probability that the token is in rounds `≥ d` is `∑_{e ≥ d} P_e`. -/
lemma sum_filter_ge_eq (f : Fin n → ℝ) (A : Strategy n D) (d : Fin D) :
    ∑ j ∈ univ.filter (fun j => d ≤ A j), f j =
      ∑ e ∈ univ.filter (fun e => d ≤ e), roundSum f A e := by
  rw [Finset.sum_filter, Finset.sum_filter]
  have := sum_mul_comp_eq f A (fun e => if d ≤ e then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero] at this
  exact this

/-- Proposition 1, first formula: `cost(A) = ∑_d P_d ∑_{e ≤ d} W_e`. -/
theorem prop1_eq1 (p w : Fin n → ℝ) (A : Strategy n D) :
    cost p w A = ∑ d, roundSum p A d * ∑ e ∈ univ.filter (fun e => e ≤ d), roundSum w A e := by
  rw [cost]
  simp_rw [sum_filter_le_eq w A]
  exact sum_mul_comp_eq p A (fun d => ∑ e ∈ univ.filter (fun e => e ≤ d), roundSum w A e)

/-- Proposition 1, second formula: `cost(A) = ∑_d W_d ∑_{e ≥ d} P_e`. -/
theorem prop1_eq2 (p w : Fin n → ℝ) (A : Strategy n D) :
    cost p w A = ∑ d, roundSum w A d * ∑ e ∈ univ.filter (fun e => d ≤ e), roundSum p A e := by
  have h1 : cost p w A = ∑ j, w j * ∑ i ∈ univ.filter (fun i => A j ≤ A i), p i := by
    rw [cost]
    simp_rw [Finset.mul_sum, Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp [mul_comm]
  rw [h1]
  simp_rw [sum_filter_ge_eq p A]
  exact sum_mul_comp_eq w A (fun d => ∑ e ∈ univ.filter (fun e => d ≤ e), roundSum p A e)

/-- Pairwise form of the cost: `cost(A) = ∑_{i,j} [A j ≤ A i] p_i w_j`. -/
lemma cost_eq_pairs (p w : Fin n → ℝ) (A : Strategy n D) :
    cost p w A = ∑ i, ∑ j, if A j ≤ A i then p i * w j else 0 := by
  rw [cost]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, Finset.sum_filter]

/-- An optimal strategy: minimum cost among all strategies with `D` rounds. -/
def IsOptimal (p w : Fin n → ℝ) (A : Strategy n D) : Prop :=
  ∀ B : Strategy n D, cost p w A ≤ cost p w B

/-- The boxes are indexed in non-increasing order of the ratio `p i / w i`
(`p₁/w₁ ≥ p₂/w₂ ≥ ⋯`), stated without division. -/
def RatioSorted (p w : Fin n → ℝ) : Prop :=
  ∀ i j : Fin n, i ≤ j → p j * w i ≤ p i * w j

/-- Output of Algorithm FRO: a minimum-cost strategy among those that respect the (ratio) order
of the boxes, i.e. among monotone strategies. -/
def IsFRO (p w : Fin n → ℝ) (A : Strategy n D) : Prop :=
  Monotone A ∧ ∀ B : Strategy n D, Monotone B → cost p w A ≤ cost p w B

theorem exists_optimal [NeZero D] (p w : Fin n → ℝ) : ∃ A : Strategy n D, IsOptimal p w A := by
  obtain ⟨A, -, hA⟩ := Finset.exists_min_image (univ : Finset (Strategy n D)) (cost p w)
    ⟨fun _ => 0, mem_univ _⟩
  exact ⟨A, fun B => hA B (mem_univ _)⟩

theorem exists_fro [NeZero D] (p w : Fin n → ℝ) : ∃ A : Strategy n D, IsFRO p w A := by
  obtain ⟨A, hAm, hA⟩ := Finset.exists_min_image (univ.filter (fun A : Strategy n D => Monotone A))
    (cost p w) ⟨fun _ => 0, by simp [monotone_const]⟩
  exact ⟨A, (mem_filter.1 hAm).2, fun B hB => hA B (by simp [hB])⟩

/-- Proposition 2 (scaling): multiplying all probabilities by `cp` and all costs by `cw`
multiplies every cost by `cp * cw`. -/
theorem cost_smul (cp cw : ℝ) (p w : Fin n → ℝ) (A : Strategy n D) :
    cost (cp • p) (cw • w) A = cp * cw * cost p w A := by
  simp only [cost, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- Proposition 2: optimal strategies are invariant under positive scaling. -/
theorem prop2_isOptimal {cp cw : ℝ} (hcp : 0 < cp) (hcw : 0 < cw) (p w : Fin n → ℝ)
    (A : Strategy n D) : IsOptimal (cp • p) (cw • w) A ↔ IsOptimal p w A := by
  have h := mul_pos hcp hcw
  simp only [IsOptimal, cost_smul]
  exact forall_congr' fun B => mul_le_mul_iff_of_pos_left h

/-- Proposition 2: approximation ratios are invariant under positive scaling. -/
theorem prop2_ratio {cp cw : ℝ} (hcp : 0 < cp) (hcw : 0 < cw) (p w : Fin n → ℝ)
    (A B : Strategy n D) :
    cost (cp • p) (cw • w) A / cost (cp • p) (cw • w) B = cost p w A / cost p w B := by
  rw [cost_smul, cost_smul, mul_div_mul_left _ _ (mul_pos hcp hcw).ne']

/-! ### Two rounds -/

/-- The gain `p(S) · w(Sᶜ)` of a first round `S`: `cost = P·W - gain`. -/
def gain (p w : Fin n → ℝ) (S : Finset (Fin n)) : ℝ :=
  (∑ i ∈ S, p i) * ∑ i ∈ Sᶜ, w i

/-- The set of boxes unlocked in the first round. -/
def firstRound (A : Strategy n 2) : Finset (Fin n) := univ.filter (fun i => A i = 0)

/-- The two-round strategy with first round `S`. -/
def ofFirstRound (S : Finset (Fin n)) : Strategy n 2 := fun i => if i ∈ S then 0 else 1

lemma firstRound_ofFirstRound (S : Finset (Fin n)) : firstRound (ofFirstRound S) = S := by
  ext i; by_cases h : i ∈ S <;> simp [firstRound, ofFirstRound, h]

lemma fin2_le_iff (a b : Fin 2) : a ≤ b ↔ (b = 0 → a = 0) := by
  fin_cases a <;> fin_cases b <;> simp

/-- Two-round cost: `cost(A) = P · W - p(S) · w(Sᶜ)` for the first round `S`. -/
theorem cost_two (p w : Fin n → ℝ) (A : Strategy n 2) :
    cost p w A = (∑ i, p i) * (∑ i, w i) - gain p w (firstRound A) := by
  set S := firstRound A
  have hW : ∑ i, w i = ∑ i ∈ S, w i + ∑ i ∈ Sᶜ, w i := (Finset.sum_add_sum_compl S w).symm
  have hP : ∑ i, p i = ∑ i ∈ S, p i + ∑ i ∈ Sᶜ, p i := (Finset.sum_add_sum_compl S p).symm
  have hin : ∀ i ∈ S, ∑ j ∈ univ.filter (fun j => A j ≤ A i), w j = ∑ j ∈ S, w j := by
    intro i hi
    have hi0 : A i = 0 := (mem_filter.1 hi).2
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j; simp [S, firstRound, hi0]
  have hout : ∀ i ∈ Sᶜ, ∑ j ∈ univ.filter (fun j => A j ≤ A i), w j = ∑ j, w j := by
    intro i hi
    have hi0 : A i ≠ 0 := by simpa [S, firstRound] using hi
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext j; simp [fin2_le_iff, hi0]
  have e1 : ∑ i ∈ S, p i * ∑ j ∈ univ.filter (fun j => A j ≤ A i), w j =
      (∑ i ∈ S, p i) * ∑ j ∈ S, w j := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i hi => by rw [hin i hi]
  have e2 : ∑ i ∈ Sᶜ, p i * ∑ j ∈ univ.filter (fun j => A j ≤ A i), w j =
      (∑ i ∈ Sᶜ, p i) * ∑ j, w j := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun i hi => by rw [hout i hi]
  rw [cost, ← Finset.sum_add_sum_compl S, e1, e2, gain, hP, hW]
  ring

/-- The boxes `0, …, k-1`. -/
def pref (n k : ℕ) : Finset (Fin n) := univ.filter (fun i => i.val < k)

/-- The two-round strategy unlocking the first `k` boxes (of the ratio order) in round 1. -/
def prefixStrategy (k : ℕ) : Strategy n 2 := fun i => if i.val < k then 0 else 1

lemma prefixStrategy_monotone (k : ℕ) : Monotone (prefixStrategy (n := n) k) := by
  intro i j hij
  simp only [prefixStrategy]
  by_cases h1 : i.val < k
  · simp [h1]
  · have : ¬ j.val < k := by have := Fin.le_def.1 hij; omega
    simp [h1, this]

lemma firstRound_prefixStrategy (k : ℕ) : firstRound (prefixStrategy (n := n) k) = pref n k := by
  ext i; by_cases h : i.val < k <;> simp [firstRound, prefixStrategy, pref, h]

/-- Every two-round strategy respecting the order is a prefix strategy. -/
theorem monotone_eq_prefixStrategy (A : Strategy n 2) (hA : Monotone A) :
    ∃ k ≤ n, A = prefixStrategy k := by
  refine ⟨(firstRound A).card, ?_, ?_⟩
  · simpa using (firstRound A).card_le_univ
  · -- `firstRound A` is a down-set of `Fin n`, hence equal to `{i | i < card}`
    have hdown : ∀ i j : Fin n, j ≤ i → A i = 0 → A j = 0 := by
      intro i j hji hi
      have := hA hji
      rw [hi] at this
      exact Fin.le_zero_iff.1 this
    have key : ∀ i : Fin n, A i = 0 ↔ i.val < (firstRound A).card := by
      intro i
      constructor
      · intro hi
        have hsub : pref n (i.val + 1) ⊆ firstRound A := by
          intro j hj
          simp only [pref, mem_filter, mem_univ, true_and] at hj
          simp only [firstRound, mem_filter, mem_univ, true_and]
          exact hdown i j (Fin.le_def.2 (by omega)) hi
        have hcard : (pref n (i.val + 1)).card = i.val + 1 := by
          rw [pref, Fin.card_filter_val_lt]; omega
        have := Finset.card_le_card hsub
        omega
      · intro hi
        by_contra hne
        have hsub : firstRound A ⊆ pref n i.val := by
          intro j hj
          simp only [firstRound, mem_filter, mem_univ, true_and] at hj
          simp only [pref, mem_filter, mem_univ, true_and]
          by_contra hji
          exact hne (hdown j i (Fin.le_def.2 (by omega)) hj)
        have hcard : (pref n i.val).card = i.val := by
          rw [pref, Fin.card_filter_val_lt]; omega
        have := Finset.card_le_card hsub
        omega
    funext i
    simp only [prefixStrategy]
    split_ifs with h
    · exact (key i).2 h
    · have : A i ≠ 0 := fun h' => h ((key i).1 h')
      revert this; generalize A i = a; fin_cases a <;> simp

end Podc.MobileDataSearch
