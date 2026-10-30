import Papers.PODC2017.NoisyRadioBroadcast.StarCoupling

/-!
# Regrouping an i.i.d. coin array into independent blocks

`sum_regroup`: an i.i.d. coin array `z : α × β → γ → Bool` (columns `z (a, b)`) can be regrouped
as `z' : α → γ → β → Bool`; the blocks `z' a` are independent (`sum_prod_blocks`). For the star,
`α` = messages (plus "silent"), `β` = number of the transmission, `γ` = nodes.
-/

namespace Podc.NoisyRadioBroadcast

open Finset Cslib.Probability

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] [DecidableEq α] [DecidableEq β]
  [DecidableEq γ]

/-- The regrouping equivalence. -/
def regroupEquiv : (α → γ → β → Bool) ≃ (α × β → γ → Bool) where
  toFun z' x c := z' x.1 c x.2
  invFun z a c b := z (a, b) c
  left_inv _ := rfl
  right_inv _ := rfl

theorem sum_regroup (q : ℝ) (F : (α × β → γ → Bool) → ℝ) :
    ∑ z : α × β → γ → Bool, (∏ x, coinProb q (z x)) * F z =
      ∑ z' : α → γ → β → Bool, (∏ a, ∏ c, coinProb q (z' a c)) *
        F (fun x c => z' x.1 c x.2) := by
  refine (Fintype.sum_equiv (regroupEquiv (α := α) (β := β) (γ := γ)) _ _ fun z' => ?_).symm
  simp only [regroupEquiv, Equiv.coe_fn_mk]
  congr 1
  simp only [coinProb]
  rw [Fintype.prod_prod_type]
  refine prod_congr rfl fun a _ => ?_
  exact prod_comm

/-- Independence of the blocks `z' a`. -/
theorem sum_prod_blocks (q : ℝ) (G : α → (γ → β → Bool) → ℝ) :
    ∑ z' : α → γ → β → Bool, (∏ a, ∏ c, coinProb q (z' a c)) * ∏ a, G a (z' a) =
      ∏ a, ∑ u : γ → β → Bool, (∏ c, coinProb q (u c)) * G a u := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun z' _ => ?_
  rw [← prod_mul_distrib]

/-- Independence of the columns of a block. -/
theorem sum_prod_cols (q : ℝ) (h : γ → (β → Bool) → ℝ) :
    ∑ u : γ → β → Bool, (∏ c, coinProb q (u c)) * ∏ c, h c (u c) =
      ∏ c, ∑ b : β → Bool, coinProb q b * h c b := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun u _ => ?_
  rw [← prod_mul_distrib]

theorem sum_coinProb_mul_indicator_le_one {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (P : (β → Bool) → Prop)
    [DecidablePred P] : ∑ b : β → Bool, coinProb q b * (if P b then 1 else 0) ≤ 1 := by
  calc _ ≤ ∑ b : β → Bool, coinProb q b :=
        sum_le_sum fun b _ => by
          have := coinProb_nonneg hq0 hq1 b
          split_ifs <;> simp [this]
    _ = 1 := sum_coinProb q

/-- `P(all of the first t coins of a column are faulty) = (1 - q)^t`. -/
theorem sum_coinProb_forall_lt_false (q : ℝ) {M : ℕ} (t : ℕ) (ht : t ≤ M) :
    ∑ b : Fin M → Bool, coinProb q b * (if ∀ j : Fin M, j.val < t → b j = false then 1 else 0) =
      (1 - q) ^ t := by
  have h := coinExpect_forall_eq_false q ((univ : Finset (Fin M)).filter fun j => j.val < t)
  have hc : #((univ : Finset (Fin M)).filter fun j => j.val < t) = t := by
    rw [Fin.card_filter_val_lt]; omega
  rw [hc] at h
  rw [← h, coinExpect]
  refine sum_congr rfl fun b _ => ?_
  congr 1
  simp only [mem_filter, mem_univ, true_and]

/-- `P(some of the first t coins of a column is clean) = 1 - (1 - q)^t`. -/
theorem sum_coinProb_exists_lt_true (q : ℝ) {M : ℕ} (t : ℕ) (ht : t ≤ M) :
    ∑ b : Fin M → Bool, coinProb q b * (if ∃ j : Fin M, j.val < t ∧ b j = true then 1 else 0) =
      1 - (1 - q) ^ t := by
  have hpt : ∀ b : Fin M → Bool,
      coinProb q b * (if ∃ j : Fin M, j.val < t ∧ b j = true then 1 else 0) =
        coinProb q b - coinProb q b * (if ∀ j : Fin M, j.val < t → b j = false then 1 else 0) := by
    intro b
    by_cases h : ∃ j : Fin M, j.val < t ∧ b j = true
    · have h' : ¬ ∀ j : Fin M, j.val < t → b j = false := by
        obtain ⟨j, hj, hb⟩ := h; intro hall; simp [hall j hj] at hb
      simp [h, h']
    · have h' : ∀ j : Fin M, j.val < t → b j = false := by
        intro j hj; by_contra hb; exact h ⟨j, hj, by simpa using hb⟩
      rw [ite_eq_right h, ite_eq_left h']; ring
  rw [sum_congr rfl fun b _ => hpt b, sum_sub_distrib, sum_coinProb,
    sum_coinProb_forall_lt_false q t ht]

end Podc.NoisyRadioBroadcast
