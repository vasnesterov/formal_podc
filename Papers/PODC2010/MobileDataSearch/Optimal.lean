import Papers.PODC2010.MobileDataSearch.Basic

/-!
# Optimal search strategies (Section 3)

Bar-Noy, Cheilaris, Feng, Levin, *Finding mobile data under delay constraints with searching costs*,
PODC 2010, Section 3.

* Lemma 1: if the probabilities are non-increasing and the costs non-decreasing along the indexing,
  then the indexing is a ratio order and every FRO strategy (best order-respecting strategy) is
  optimal (`lemma1_ratioSorted`, `lemma1_isOptimal`). The paper's proof assumes strict
  inequalities between the swapped boxes (false with ties) and only exchanges boxes in adjacent
  rounds; we prove the statement with weak inequalities by an exchange argument on arbitrary
  inversions.
* Lemma 2: in an optimal strategy the round ratios `P_d / W_d` are non-increasing
  (`lemma2`, stated without division; the exact exchange identity is `cost_swap_rounds`).
* Corollary 1: for a ratio-sorted instance, unlocking one box per round in the ratio order is
  optimal, even against strategies with any number of rounds (`corollary1`).
* The uniform-probability and atypical-token cases (`uniformProb_isOptimal`,
  `atypical_isOptimal`).
-/

namespace Podc.MobileDataSearch

open Finset

variable {n D : ℕ}

/-! ### Exchange lemmas -/

/-- Swapping two arguments of `f` in a weighted sum. -/
lemma sum_swap_mul (f g : Fin n → ℝ) (i j : Fin n) :
    ∑ a, f (Equiv.swap i j a) * g a = ∑ a, f a * g a + (f j - f i) * (g i - g j) := by
  by_cases hij : i = j
  · subst hij; simp
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  have key : ∀ a, f (Equiv.swap i j a) * g a - f a * g a =
      (if a = i then (f j - f i) * g i else 0) + (if a = j then (f i - f j) * g j else 0) := by
    intro a
    by_cases hai : a = i
    · subst hai; simp [hij]; ring
    by_cases haj : a = j
    · subst haj; simp [hai]; ring
    simp [hai, haj, Equiv.swap_apply_of_ne_of_ne hai haj]
  simp_rw [key, Finset.sum_add_distrib, Finset.sum_ite_eq' univ]
  simp only [mem_univ, ite_true]
  ring

/-- Transposed form of the cost: `cost(A) = ∑_j w_j ∑_{i : A j ≤ A i} p_i`. -/
lemma cost_eq_transpose (p w : Fin n → ℝ) (A : Strategy n D) :
    cost p w A = ∑ j, w j * ∑ i ∈ univ.filter (fun i => A j ≤ A i), p i := by
  rw [cost]
  simp_rw [Finset.mul_sum, Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp [mul_comm]

/-- Relabelling the boxes by a permutation does not change the cost. -/
lemma cost_comp_equiv (p w : Fin n → ℝ) (A : Strategy n D) (e : Equiv.Perm (Fin n)) :
    cost (p ∘ e) (w ∘ e) (A ∘ e) = cost p w A := by
  rw [cost_eq_pairs, cost_eq_pairs]
  simp only [Function.comp]
  rw [← Equiv.sum_comp e (fun i => ∑ j, if A j ≤ A i then p i * w j else 0)]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact Equiv.sum_comp e (fun j => if A j ≤ A (e i) then p (e i) * w j else 0)

/-- Moving the smaller probability to the later box does not increase the cost. -/
lemma cost_swap_p_le (p w : Fin n → ℝ) (hw : 0 ≤ w) (A : Strategy n D) {i j : Fin n}
    (hA : A j ≤ A i) (hp : p j ≤ p i) :
    cost (p ∘ Equiv.swap i j) w A ≤ cost p w A := by
  simp only [cost, Function.comp]
  rw [sum_swap_mul p (fun a => ∑ b ∈ univ.filter (fun b => A b ≤ A a), w b) i j]
  have hS : ∑ b ∈ univ.filter (fun b => A b ≤ A j), w b ≤
      ∑ b ∈ univ.filter (fun b => A b ≤ A i), w b := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hw b
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact hb.trans hA
  nlinarith

/-- Moving the larger cost to the later box does not increase the cost. -/
lemma cost_swap_w_le (p w : Fin n → ℝ) (hp : 0 ≤ p) (A : Strategy n D) {i j : Fin n}
    (hA : A j ≤ A i) (hw : w i ≤ w j) :
    cost p (w ∘ Equiv.swap i j) A ≤ cost p w A := by
  rw [cost_eq_transpose, cost_eq_transpose]
  simp only [Function.comp]
  rw [sum_swap_mul w (fun a => ∑ b ∈ univ.filter (fun b => A a ≤ A b), p b) i j]
  have hS : ∑ b ∈ univ.filter (fun b => A i ≤ A b), p b ≤
      ∑ b ∈ univ.filter (fun b => A j ≤ A b), p b := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ => hp b
    intro b hb
    simp only [mem_filter, mem_univ, true_and] at hb ⊢
    exact hA.trans hb
  nlinarith

/-- Exchange step of Lemma 1: if `i ≤ j` (so `p j ≤ p i` and `w i ≤ w j`) but box `i` is unlocked
no earlier than box `j`, exchanging the rounds of boxes `i` and `j` does not increase the cost. -/
lemma cost_comp_swap_le (p w : Fin n → ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w) (A : Strategy n D)
    {i j : Fin n} (hA : A j ≤ A i) (hpij : p j ≤ p i) (hwij : w i ≤ w j) :
    cost p w (A ∘ Equiv.swap i j) ≤ cost p w A := by
  set σ := Equiv.swap i j
  have hσ : ∀ f : Fin n → ℝ, f ∘ σ ∘ σ = f := fun f => by
    funext a; simp [σ, Equiv.swap_apply_self]
  have h1 : cost p w (A ∘ σ) = cost (p ∘ σ) (w ∘ σ) A := by
    rw [← cost_comp_equiv (p ∘ σ) (w ∘ σ) A σ]
    simp only [Function.comp_assoc] at hσ ⊢
    rw [hσ, hσ]
  have hwσ : 0 ≤ w ∘ σ := fun a => hw (σ a)
  rw [h1]
  exact (cost_swap_p_le p (w ∘ σ) hwσ A hA hpij).trans (cost_swap_w_le p w hp A hA hwij)

/-- For antitone `p` and monotone `w`, every strategy is dominated by a monotone one. -/
lemma exists_monotone_cost_le (p w : Fin n → ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hpa : ∀ i j : Fin n, i ≤ j → p j ≤ p i) (hwm : ∀ i j : Fin n, i ≤ j → w i ≤ w j)
    (B : Strategy n D) : ∃ B' : Strategy n D, Monotone B' ∧ cost p w B' ≤ cost p w B := by
  -- the potential `Φ(C) = ∑ k, k * C k` increases strictly under the exchange step
  let Φ : Strategy n D → ℝ := fun C => ∑ k, ((C k : ℕ) : ℝ) * ((k : ℕ) : ℝ)
  obtain ⟨C, hCmem, hCmax⟩ := Finset.exists_max_image
    (univ.filter (fun C : Strategy n D => cost p w C ≤ cost p w B)) Φ ⟨B, by simp⟩
  have hC : cost p w C ≤ cost p w B := (mem_filter.1 hCmem).2
  refine ⟨C, ?_, hC⟩
  by_contra hmono
  simp only [Monotone, not_forall, not_le] at hmono
  obtain ⟨i, j, hij, hlt⟩ := hmono
  have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
  have hcost := cost_comp_swap_le p w hp hw C hlt.le (hpa i j hij) (hwm i j hij)
  have hmem : C ∘ Equiv.swap i j ∈ univ.filter
      (fun C : Strategy n D => cost p w C ≤ cost p w B) := by
    simp only [mem_filter, mem_univ, true_and]; exact hcost.trans hC
  have hΦ := hCmax _ hmem
  have hcalc : Φ (C ∘ Equiv.swap i j) = Φ C +
      (((C j : ℕ) : ℝ) - ((C i : ℕ) : ℝ)) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) :=
    sum_swap_mul (fun k => ((C k : ℕ) : ℝ)) (fun k => ((k : ℕ) : ℝ)) i j
  have h1 : ((C j : ℕ) : ℝ) < ((C i : ℕ) : ℝ) := by exact_mod_cast hlt
  have h2 : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) := by exact_mod_cast hij'
  have : 0 < (((C j : ℕ) : ℝ) - ((C i : ℕ) : ℝ)) * (((i : ℕ) : ℝ) - ((j : ℕ) : ℝ)) :=
    mul_pos_of_neg_of_neg (by linarith) (by linarith)
  linarith

/-! ### Lemma 1 -/

/-- Lemma 1 of [Bar-Noy, Cheilaris, Feng, Levin, PODC 2010], first part: if
`p₁ ≥ ⋯ ≥ p_N` and `w₁ ≤ ⋯ ≤ w_N`, then this order is a ratio order (FRO follows it). -/
theorem lemma1_ratioSorted (p w : Fin n → ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hpa : ∀ i j : Fin n, i ≤ j → p j ≤ p i) (hwm : ∀ i j : Fin n, i ≤ j → w i ≤ w j) :
    RatioSorted p w := fun i j hij =>
  mul_le_mul (hpa i j hij) (hwm i j hij) (hw i) (hp i)

/-- Lemma 1 of [Bar-Noy, Cheilaris, Feng, Levin, PODC 2010]: if `p₁ ≥ ⋯ ≥ p_N` and
`w₁ ≤ ⋯ ≤ w_N`, then every FRO strategy (a minimum-cost strategy among those respecting this
order) is optimal, for every number of rounds `D`. Weak inequalities (ties) are allowed. -/
theorem lemma1_isOptimal (p w : Fin n → ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hpa : ∀ i j : Fin n, i ≤ j → p j ≤ p i) (hwm : ∀ i j : Fin n, i ≤ j → w i ≤ w j)
    (A : Strategy n D) (hA : IsFRO p w A) : IsOptimal p w A := by
  intro B
  obtain ⟨B', hB'm, hB'⟩ := exists_monotone_cost_le p w hp hw hpa hwm B
  exact (hA.2 B' hB'm).trans hB'

/-- Uniform probabilities (Section 3): if all probabilities are equal and the boxes are sorted by
non-decreasing cost, every FRO strategy is optimal. -/
theorem uniformProb_isOptimal (c : ℝ) (hc : 0 ≤ c) (w : Fin n → ℝ) (hw : 0 ≤ w)
    (hwm : ∀ i j : Fin n, i ≤ j → w i ≤ w j) (A : Strategy n D)
    (hA : IsFRO (fun _ => c) w A) : IsOptimal (fun _ => c) w A :=
  lemma1_isOptimal _ w (fun _ => hc) hw (fun _ _ _ => le_rfl) hwm A hA

/-- Atypical tokens (Section 3): if higher probabilities go with lower costs (boxes sorted by
non-increasing probability and non-decreasing cost), every FRO strategy is optimal. -/
theorem atypical_isOptimal (p w : Fin n → ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hpa : ∀ i j : Fin n, i ≤ j → p j ≤ p i) (hwm : ∀ i j : Fin n, i ≤ j → w i ≤ w j)
    (A : Strategy n D) (hA : IsFRO p w A) : IsOptimal p w A :=
  lemma1_isOptimal p w hp hw hpa hwm A hA

/-! ### Lemma 2 -/

/-- Indicator bookkeeping for exchanging two adjacent rounds `d`, `d + 1`. -/
lemma swap_rounds_indicator {d d' : Fin D} (hd : d'.val = d.val + 1) (x y : Fin D) :
    ((if Equiv.swap d d' y ≤ Equiv.swap d d' x then 1 else 0 : ℝ) -
      (if y ≤ x then 1 else 0)) =
      (if x = d ∧ y = d' then 1 else 0) - (if x = d' ∧ y = d then 1 else 0) := by
  have hne : d ≠ d' := by intro h; rw [h] at hd; omega
  have hne' : d' ≠ d := Ne.symm hne
  have key : ∀ z : Fin D, z ≠ d → z ≠ d' → (z ≤ d ↔ z ≤ d') ∧ (d ≤ z ↔ d' ≤ z) := by
    intro z h1 h2
    have h1' : z.val ≠ d.val := fun h => h1 (Fin.ext h)
    have h2' : z.val ≠ d'.val := fun h => h2 (Fin.ext h)
    simp only [Fin.le_def]; omega
  have hdd' : d ≤ d' := Fin.le_def.2 (by omega)
  have hd'd : ¬ d' ≤ d := by rw [Fin.le_def]; omega
  by_cases hx : x = d <;> by_cases hx' : x = d' <;> by_cases hy : y = d <;>
    by_cases hy' : y = d' <;> simp_all [Equiv.swap_apply_of_ne_of_ne]

/-- Exchanging rounds `d` and `d + 1` of a strategy changes its cost by exactly
`P_d W_{d+1} - P_{d+1} W_d` (proof of Lemma 2). -/
theorem cost_swap_rounds (p w : Fin n → ℝ) (A : Strategy n D) {d d' : Fin D}
    (hd : d'.val = d.val + 1) :
    cost p w (Equiv.swap d d' ∘ A) - cost p w A =
      roundSum p A d * roundSum w A d' - roundSum p A d' * roundSum w A d := by
  rw [cost_eq_pairs, cost_eq_pairs, ← Finset.sum_sub_distrib]
  have h : ∀ a b : Fin n,
      ((if (Equiv.swap d d' ∘ A) b ≤ (Equiv.swap d d' ∘ A) a then p a * w b else 0) -
        (if A b ≤ A a then p a * w b else 0)) =
      (if A a = d ∧ A b = d' then p a * w b else 0) -
        (if A a = d' ∧ A b = d then p a * w b else 0) := by
    intro a b
    have := swap_rounds_indicator hd (A a) (A b)
    simp only [Function.comp] at this ⊢
    have e : ∀ (P : Prop) [Decidable P], (if P then p a * w b else 0) =
        (if P then 1 else 0 : ℝ) * (p a * w b) := fun P _ => by split_ifs <;> simp
    rw [e, e, e (A a = d ∧ A b = d'), e (A a = d' ∧ A b = d), ← sub_mul, ← sub_mul, this]
  simp_rw [← Finset.sum_sub_distrib, h, Finset.sum_sub_distrib]
  have hr : ∀ e f : Fin D, ∑ a, ∑ b, (if A a = e ∧ A b = f then p a * w b else 0) =
      roundSum p A e * roundSum w A f := by
    intro e f
    rw [roundSum, roundSum, Finset.sum_mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_filter]
    split_ifs with ha
    · exact Finset.sum_congr rfl fun b _ => by simp [ha]
    · simp [ha]
  rw [hr, hr]

/-- Lemma 2 of [Bar-Noy, Cheilaris, Feng, Levin, PODC 2010]: in an optimal strategy,
`P_d / W_d ≥ P_{d+1} / W_{d+1}` for consecutive rounds, stated without division as
`P_{d+1} W_d ≤ P_d W_{d+1}`. -/
theorem lemma2 (p w : Fin n → ℝ) (A : Strategy n D) (hA : IsOptimal p w A) (d : Fin D)
    (hd : d.val + 1 < D) :
    roundSum p A ⟨d.val + 1, hd⟩ * roundSum w A d ≤
      roundSum p A d * roundSum w A ⟨d.val + 1, hd⟩ := by
  have h := cost_swap_rounds p w A (d := d) (d' := ⟨d.val + 1, hd⟩) rfl
  have := hA (Equiv.swap d ⟨d.val + 1, hd⟩ ∘ A)
  linarith

/-! ### Corollary 1 -/

/-- The sequential strategy for `D = N`: box `i` alone in round `i`. -/
def sequential (n : ℕ) : Strategy n n := id

/-- Corollary 1 of [Bar-Noy, Cheilaris, Feng, Levin, PODC 2010]: if the boxes are indexed in
non-increasing order of `p i / w i`, unlocking them one per round in this order is optimal for
`D = N`. We prove the stronger statement that it is at least as good as every strategy with any
number `D` of rounds. -/
theorem corollary1 (p w : Fin n → ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w) (hs : RatioSorted p w)
    (B : Strategy n D) : cost p w (sequential n) ≤ cost p w B := by
  rw [cost_eq_pairs, cost_eq_pairs]
  simp only [sequential, id]
  rw [← sub_nonneg, ← Finset.sum_sub_distrib]
  simp_rw [← Finset.sum_sub_distrib]
  set g : Fin n → Fin n → ℝ := fun i j =>
    (if B j ≤ B i then p i * w j else 0) - (if j ≤ i then p i * w j else 0) with hg
  have hpair : ∀ i j, 0 ≤ g i j + g j i := by
    intro i j
    have hij := mul_nonneg (hp i) (hw j)
    have hji := mul_nonneg (hp j) (hw i)
    rcases lt_trichotomy i j with h | rfl | h
    · have h1 := hs i j h.le
      have : ¬ j ≤ i := not_le.2 h
      simp only [hg, this, h.le, ite_true, ite_false]
      split_ifs <;> first | linarith |
        (exfalso; rcases le_total (B i) (B j) with hb | hb <;> contradiction)
    · simp [hg]
    · have h1 := hs j i h.le
      have : ¬ i ≤ j := not_le.2 h
      simp only [hg, this, h.le, ite_true, ite_false]
      split_ifs <;> first | linarith |
        (exfalso; rcases le_total (B i) (B j) with hb | hb <;> contradiction)
  have h2 : 2 * ∑ i, ∑ j, g i j = ∑ i, ∑ j, (g i j + g j i) := by
    simp_rw [Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => g j i)]
    ring
  have : 0 ≤ ∑ i, ∑ j, (g i j + g j i) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hpair i j
  change 0 ≤ ∑ i, ∑ j, g i j
  linarith

/-- Corollary 1 for `D = N`: the sequential strategy is optimal. -/
theorem corollary1_isOptimal (p w : Fin n → ℝ) (hp : 0 ≤ p) (hw : 0 ≤ w)
    (hs : RatioSorted p w) : IsOptimal p w (sequential n) :=
  fun B => corollary1 p w hp hw hs B

end Podc.MobileDataSearch
