import Mathlib

/-!
# Counting functions with a prescribed number of preimages

`#{f : Fin L → α | #{i | f i = j} = k} = C(L, k) · (|α| - 1)^(L - k)`: the law of the number of
balls in a fixed bin when `L` balls are thrown independently and uniformly into `|α|` bins
(binomial distribution, by counting).
-/

namespace Podc.WirelessPacketScheduling

open Finset

-- CSLib candidate
/-- Number of functions `Fin L → α` hitting `j` exactly `k` times. -/
theorem card_filter_count_eq {α : Type*} [Fintype α] [DecidableEq α] (j : α) :
    ∀ (L k : ℕ), (univ.filter (fun f : Fin L → α => (univ.filter (fun i => f i = j)).card = k)).card
      = L.choose k * (Fintype.card α - 1) ^ (L - k) := by
  intro L
  induction L with
  | zero =>
    intro k
    rcases k with _ | k
    · simp
    · simp
  | succ L ih =>
    intro k
    have hcnt : ∀ (a : α) (f : Fin L → α),
        (univ.filter (fun i => (Fin.cons a f : Fin (L+1) → α) i = j)).card
          = (univ.filter (fun i => f i = j)).card + (if a = j then 1 else 0) := by
      intro a f
      rw [card_filter, card_filter, Fin.sum_univ_succ]
      simp [add_comm]
    have e : (univ.filter (fun f : Fin (L+1) → α => (univ.filter (fun i => f i = j)).card = k)).card
        = ∑ a : α, (univ.filter (fun f : Fin L → α =>
            (univ.filter (fun i => f i = j)).card + (if a = j then 1 else 0) = k)).card := by
      simp only [card_filter]
      rw [← (Fin.consEquiv (fun _ : Fin (L+1) => α)).sum_comp, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun f _ => ?_
      have := hcnt a f
      simp only [card_filter] at this
      have h1 : ((Fin.consEquiv fun _ : Fin (L+1) => α) (a, f)) = Fin.cons a f := rfl
      simp only [h1, this]
    rw [e, ← Finset.add_sum_erase _ _ (mem_univ j)]
    have hrest : ∑ a ∈ univ.erase j, (univ.filter (fun f : Fin L → α =>
        (univ.filter (fun i => f i = j)).card + (if a = j then 1 else 0) = k)).card
          = (Fintype.card α - 1) * (L.choose k * (Fintype.card α - 1) ^ (L - k)) := by
      rw [← ih k, ← Finset.card_univ, ← Finset.card_erase_of_mem (mem_univ j), ← smul_eq_mul,
        ← Finset.sum_const]
      refine Finset.sum_congr rfl fun a ha => ?_
      simp [(Finset.ne_of_mem_erase ha)]
    rw [hrest]
    simp only [ite_true]
    rcases k with _ | k
    · simp [pow_succ, mul_comm]
    · simp only [Nat.add_right_cancel_iff]
      rw [ih k, Nat.choose_succ_succ, add_mul, show L + 1 - (k + 1) = L - k by omega]
      congr 1
      rcases Nat.lt_or_ge k L with h | h
      · rw [show L - k = L - (k + 1) + 1 by omega, pow_succ]
        ring
      · rw [Nat.choose_eq_zero_of_lt (by omega)]
        simp

end Podc.WirelessPacketScheduling
