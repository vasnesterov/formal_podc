import Papers.PODC2017.NoisyRadioBroadcast.Coupling

/-!
# Basic facts about `prob` and a binomial lower tail

* `prob_mono`, `prob_nonneg`, `prob_le_one`, `prob_not`, `prob_exists_le` (union bound),
  `prob_congr`.
* `prob_card_le_le` (**Chernoff lower tail**): for a set `S` of (round, node) coins, the number of
  clean coins in `S` is at most `K` with probability at most `λ^{-K} (1 - (1 - λ)(1 - p))^{|S|}`
  for every `0 < λ ≤ 1`.
* `run_congr`: the knowledge state before round `R` depends only on the coins of rounds `< R`.
-/

namespace Podc.NoisyRadioBroadcast

open Finset Cslib.Probability

variable {V : Type*} [Fintype V] [DecidableEq V]

section Basic

variable {p : ℝ} {R : ℕ}

/-- `prob` as an expectation under the product weights. -/
theorem prob_eq_piExpect (p : ℝ) (R : ℕ) (E : (ℕ → V → Bool) → Prop) [DecidablePred E] :
    prob p R E = piExpect (fun (_ : Fin R) => coinProb (1 - p))
      (fun y => if E (extendCoins y) then 1 else 0) := by
  classical
  unfold prob piExpect piWeight
  refine sum_congr rfl fun y _ => ?_
  by_cases h : E (extendCoins y) <;> simp [h]

omit [DecidableEq V] in
theorem weight_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (y : Fin R → V → Bool) :
    0 ≤ ∏ r, coinProb (1 - p) (y r) :=
  prod_nonneg fun r _ => coinProb_nonneg (by linarith) (by linarith) _

theorem sum_weight (p : ℝ) (R : ℕ) :
    ∑ y : Fin R → V → Bool, ∏ r, coinProb (1 - p) (y r) = 1 := by
  rw [← Fintype.prod_sum (fun (_ : Fin R) (c : V → Bool) => coinProb (1 - p) c)]
  simp [sum_coinProb]

theorem prob_mono (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {E F : (ℕ → V → Bool) → Prop}
    (h : ∀ ω, E ω → F ω) : prob p R E ≤ prob p R F := by
  classical
  unfold prob
  refine sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg hp0 hp1 y)
  by_cases hE : E (extendCoins y)
  · simp [hE, h _ hE]
  · simp only [hE, ite_false]; split_ifs <;> norm_num

theorem prob_congr {E F : (ℕ → V → Bool) → Prop} (h : ∀ ω, E ω ↔ F ω) :
    prob p R E = prob p R F := by
  have : E = F := funext fun ω => propext (h ω)
  rw [this]

theorem prob_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : (ℕ → V → Bool) → Prop) :
    0 ≤ prob p R E := by
  classical
  unfold prob
  exact sum_nonneg fun y _ => mul_nonneg (weight_nonneg hp0 hp1 y) (by split_ifs <;> norm_num)

theorem prob_true (p : ℝ) (R : ℕ) : prob (V := V) p R (fun _ => True) = 1 := by
  classical
  simp [prob, sum_weight]

theorem prob_le_one (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (E : (ℕ → V → Bool) → Prop) :
    prob p R E ≤ 1 :=
  (prob_mono hp0 hp1 (F := fun _ => True) fun _ _ => trivial).trans_eq (prob_true p R)

theorem prob_not (p : ℝ) (R : ℕ) (E : (ℕ → V → Bool) → Prop) :
    prob p R (fun ω => ¬ E ω) = 1 - prob p R E := by
  classical
  rw [← prob_true (V := V) p R]
  unfold prob
  rw [← sum_sub_distrib]
  refine sum_congr rfl fun y _ => ?_
  by_cases hE : E (extendCoins y) <;> simp [hE]

/-- **Union bound.** -/
theorem prob_exists_le (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {ι : Type*} (s : Finset ι)
    (E : ι → (ℕ → V → Bool) → Prop) :
    prob p R (fun ω => ∃ i ∈ s, E i ω) ≤ ∑ i ∈ s, prob p R (E i) := by
  classical
  unfold prob
  rw [sum_comm]
  refine sum_le_sum fun y _ => ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (weight_nonneg hp0 hp1 y)
  split_ifs with h
  · obtain ⟨i, hi, hE⟩ := h
    exact (single_le_sum (f := fun i => if E i (extendCoins y) then (1 : ℝ) else 0)
      (fun j _ => by split_ifs <;> norm_num) hi).trans_eq' (by simp [hE])
  · exact sum_nonneg fun j _ => by split_ifs <;> norm_num

end Basic

section Tail

/-- **Chernoff lower tail** for the number of clean coins in a set `S` of (round, node) pairs. -/
theorem prob_card_le_le {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {R : ℕ} (S : Finset (Fin R × V))
    (K : ℕ) {l : ℝ} (hl0 : 0 < l) (hl1 : l ≤ 1) :
    prob p R (fun ω => #(S.filter fun x => ω x.1 x.2 = true) ≤ K) ≤
      (l ^ K)⁻¹ * (1 - (1 - l) * (1 - p)) ^ #S := by
  classical
  -- pointwise: indicator ≤ l^count / l^K
  have hpt : ∀ y : Fin R → V → Bool,
      (if #(S.filter fun x => extendCoins y x.1 x.2 = true) ≤ K then (1 : ℝ) else 0) ≤
        (l ^ K)⁻¹ * ∏ r, ∏ u, (if (r, u) ∈ S ∧ y r u = true then l else 1) := by
    intro y
    have hcount : ∏ r, ∏ u, (if (r, u) ∈ S ∧ y r u = true then l else 1) =
        l ^ #(S.filter fun x => extendCoins y x.1 x.2 = true) := by
      rw [← Fintype.prod_prod_type' (f := fun r u => if (r, u) ∈ S ∧ y r u = true then l else 1),
        prod_ite, prod_const_one, mul_one, prod_const]
      congr 1
      congr 1
      ext x
      simp [extendCoins]
    rw [hcount]
    split_ifs with h
    · rw [← div_eq_inv_mul, le_div_iff₀ (pow_pos hl0 _), one_mul]
      exact pow_le_pow_of_le_one hl0.le hl1 h
    · exact mul_nonneg (inv_nonneg.2 (pow_nonneg hl0.le _)) (pow_nonneg hl0.le _)
  calc prob p R (fun ω => #(S.filter fun x => ω x.1 x.2 = true) ≤ K)
      ≤ ∑ y : Fin R → V → Bool, (∏ r, coinProb (1 - p) (y r)) *
          ((l ^ K)⁻¹ * ∏ r, ∏ u, (if (r, u) ∈ S ∧ y r u = true then l else 1)) := by
        unfold prob
        refine sum_le_sum fun y _ => mul_le_mul_of_nonneg_left ?_ (weight_nonneg hp0 hp1 y)
        convert hpt y
    _ = (l ^ K)⁻¹ * piExpect (fun (_ : Fin R) => coinProb (1 - p))
          (fun y => ∏ r, ∏ u, (if (r, u) ∈ S ∧ y r u = true then l else 1)) := by
        unfold piExpect piWeight
        rw [mul_sum]
        refine sum_congr rfl fun y _ => by ring
    _ = (l ^ K)⁻¹ * (1 - (1 - l) * (1 - p)) ^ #S := by
        have hprod := piExpect_prod (fun (_ : Fin R) => coinProb (1 - p))
          (fun r (c : V → Bool) => ∏ u, (if (r, u) ∈ S ∧ c u = true then l else 1))
        rw [hprod]
        congr 1
        have : ∀ r : Fin R, ∑ c : V → Bool, coinProb (1 - p) c *
            ∏ u, (if (r, u) ∈ S ∧ c u = true then l else 1) =
            ∏ u, (if (r, u) ∈ S then 1 - (1 - l) * (1 - p) else 1) := by
          intro r
          have := coinExpect_prod (1 - p) (fun u (b : Bool) => if (r, u) ∈ S ∧ b = true then l else 1)
          simp only [coinExpect] at this
          rw [this]
          refine prod_congr rfl fun u _ => ?_
          split_ifs <;> simp_all <;> ring
        simp_rw [this]
        rw [← Fintype.prod_prod_type' (f := fun r u =>
          if (r, u) ∈ S then 1 - (1 - l) * (1 - p) else 1), prod_ite_mem, univ_inter, prod_const]

end Tail

section RunCongr

variable (G : SimpleGraph V) {k : ℕ}

/-- The knowledge before round `R` depends only on the coins of rounds `< R`. -/
theorem run_congr (s : V) (f : FaultModel) (sch : AdaptiveSchedule V k) {ω ω' : ℕ → V → Bool}
    {R : ℕ} (h : ∀ r < R, ω r = ω' r) : run G s f sch ω R = run G s f sch ω' R := by
  induction R with
  | zero => rfl
  | succ R ih =>
    simp only [run]
    rw [ih fun r hr => h r (hr.trans (Nat.lt_succ_self R)), h R (Nat.lt_succ_self R)]

theorem determinedUpTo_delivered (s : V) (f : FaultModel) (sch : AdaptiveSchedule V k) (R : ℕ) :
    DeterminedUpTo R (fun ω => Delivered (run G s f sch ω R)) := fun ω ω' h => by
  show Delivered _ ↔ Delivered _
  rw [run_congr G s f sch h]

end RunCongr

end Podc.NoisyRadioBroadcast
