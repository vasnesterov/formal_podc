/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Papers.PODC2021.HTLCBrokeringHardness.Inadequate

/-!
# Lemma 4.2: the execution with leaders `{s, b}`, and the bitcoin budget

* `budget_of_adequate`: in **every** adequate execution of `F = flower K m c` the broker pays all
  item contracts, `Σ_w(X)` bitcoins, out of what it receives: `W` from `s` and `c` from each of
  `y₂, …, y_m`. Hence `Σ_w(X) ≤ W + (m − 1)·c` is necessary for *any* adequate leader set.
* `adequate_of_satisfiable` (Lemma 4.2, repaired): if `K` is satisfiable, `V ≥ 1` and
  `Σ_w(X) ≤ W + (m − 1)·c`, then `{b, s}` is adequate — by the execution described in the paper.
-/

namespace Podc.HTLCBrokeringHardness

open Finset Flower

variable {n m c : ℕ} {K : Knapsack n}

namespace Flower

lemma outflow_le_own {p : Party n m} (hp : p ≠ .b) (S : Finset (Edge n m)) (a : Asset) :
    (flower K m c).outflow S p a ≤ flowerOwn K m c p a := by
  simp only [flowerOwn, TxGraph.brokerOwn, ite_eq_right hp, TxGraph.outTotal]
  exact TxGraph.outflow_mono (subset_univ S) p a

/-- One batch of the execution with leaders `{b, s}`. -/
lemma batch {S S' : Finset (Edge n m)}
    (hS : (flower K m c).Reachable (flowerOwn K m c) {.b, .s} S) (hSS : S ⊆ S')
    (hal : ∀ e ∈ S', e ∉ S → (flower K m c).src e = .b ∨ (flower K m c).src e = .s ∨
      ∀ e', (flower K m c).dst e' = (flower K m c).src e → e' ∈ S)
    (hpay : ∀ e ∈ S', e ∉ S → (flower K m c).src e = .b →
      (flower K m c).outflow S' .b ((flower K m c).asset e) ≤
        (flower K m c).inflow S .b ((flower K m c).asset e)) :
    (flower K m c).Reachable (flowerOwn K m c) {.b, .s} S' := by
  refine hS.batch' hSS (fun e he hne => ?_) (fun e he hne => ?_)
  · rcases hal e he hne with h | h | h
    · exact Or.inl (by simp [h])
    · exact Or.inl (by simp [h])
    · exact Or.inr h
  · by_cases h : (flower K m c).src e = .b
    · rw [h, own_b, zero_add]; exact hpay e he hne h
    · exact (outflow_le_own h _ _).trans (Nat.le_add_right _ _)

end Flower

/-- The broker's bitcoin budget: in every adequate execution of `F`, whatever the leaders,
`Σ_w(X) ≤ W + (m − 1)·c`. -/
theorem budget_of_adequate {L : Finset (Party n m)}
    (hA : (flower K m c).Adequate (flowerOwn K m c) L) : K.totalW ≤ K.W + (m - 1) * c := by
  have h := hA.outTotal_le .b .B
  rw [own_b, zero_add, TxGraph.outTotal, outflow_B, inflow_B] at h
  simpa [Knapsack.totalW] using h

open Classical in
/-- Contracts created once the first `k` levels are done (and, if `half`, the broker's contracts to
level `k`), when the broker initially funds the items of `R`. -/
noncomputable def stage (R : Finset (Fin n)) (k : ℕ) (half : Bool) : Finset (Edge n m) :=
  univ.filter fun e => match e with
    | .fromS => True
    | .toS => False
    | .toX i => i ∈ R
    | .fromX i => i ∈ R
    | .toY j => (j : ℕ) < k ∨ (half = true ∧ (j : ℕ) = k)
    | .toZ j => (j : ℕ) < k ∨ (half = true ∧ (j : ℕ) = k)
    | .fromY j => (j : ℕ) < k
    | .fromZ j => (j : ℕ) < k
    | .fromYB j => (ybLevel j : ℕ) < k

open Classical in
/-- The supplier's contract and the broker's contracts to the items of `R`. -/
noncomputable def pre (R : Finset (Fin n)) : Finset (Edge n m) :=
  univ.filter fun e => match e with
    | .fromS => True
    | .toX i => i ∈ R
    | _ => False

open Classical in
/-- Everything except `(b, s)` and the item contracts `(xᵢ, b)`, `i ∉ R`. -/
noncomputable def almost (R : Finset (Fin n)) : Finset (Edge n m) :=
  univ.filter fun e => match e with
    | .toS => False
    | .fromX i => i ∈ R
    | _ => True

/-- Reachability with leaders `{b, s}`. -/
abbrev Reach (K : Knapsack n) (m c : ℕ) (S : Finset (Edge n m)) : Prop :=
  (flower K m c).Reachable (flowerOwn K m c) {Party.b, Party.s} S

section Steps

variable (R : Finset (Fin n))


lemma reach_fromS : Reach K m c {Edge.fromS} := by
  refine batch Relation.ReflTransGen.refl (empty_subset _) (fun e he _ => ?_) (fun e he _ hb => ?_)
  · simp only [mem_singleton] at he; subst he; exact Or.inr (Or.inl rfl)
  · simp only [mem_singleton] at he; subst he; simp at hb

lemma reach_pre (hRW : ∑ i ∈ R, K.w i ≤ K.W) : Reach K m c (pre R) := by
  refine batch reach_fromS (fun e he => ?_) (fun e he hne => ?_) (fun e he hne hb => ?_)
  · simp only [mem_singleton] at he; subst he; simp [pre]
  · cases e <;> simp [pre] at he hne ⊢
  · cases e <;> simp [pre] at he hne hb ⊢
    rw [outflow_B, inflow_B]
    simpa [pre, ← sum_filter] using hRW

lemma reach_stage0 (hRW : ∑ i ∈ R, K.w i ≤ K.W) : Reach K m c (stage R 0 false) := by
  refine batch (reach_pre R hRW) (fun e he => ?_) (fun e he hne => ?_) (fun e he hne hb => ?_)
  · cases e <;> simp [pre, stage] at he ⊢ <;> exact he
  · cases e <;> simp [pre, stage] at he hne ⊢
    intro e' he'; cases e' <;> simp at he' ⊢; subst he'; exact he
  · cases e <;> simp [pre, stage] at he hne hb ⊢
    all_goals exact absurd he hne

/-- Closes the goals of a batch whose new contract `e` is not actually new (`he`, `hne` contradict). -/
local macro "contra_new" : tactic =>
  `(tactic| all_goals (try (exfalso; first | exact hne he | omega | (simp_all; done))))

lemma reach_half0 (hV : 1 ≤ K.V) (hRV : K.V ≤ ∑ i ∈ R, K.v i) (h : Reach K m c (stage R 0 false)) :
    Reach K m c (stage R 0 true) := by
  refine batch h (fun e he => ?_) (fun e he hne => ?_) (fun e he hne hb => ?_)
  · cases e <;> simp [stage] at he ⊢ <;> exact he
  · cases e <;> simp [stage] at he hne ⊢ <;> contra_new
  · cases e <;> simp [stage] at he hne hb ⊢ <;> contra_new
    all_goals
      subst he
      rw [show inAsset (0 : Fin (m + 1)) = .E by simp [inAsset], outflow_E, inflow_E]
      simp only [mem_filter, mem_univ, true_and, Fin.val_zero, lt_self_iff_false, and_self,
        or_true, ite_true, ← sum_filter, filter_mem_eq_inter, univ_inter]
      omega

lemma reach_full (k : ℕ) (h : Reach K m c (stage R k true)) : Reach K m c (stage R (k + 1) false) := by
  refine batch h (fun e he => ?_) (fun e he hne => ?_) (fun e he hne hb => ?_)
  · cases e <;> simp [stage] at he ⊢ <;> omega
  · cases e <;> simp [stage] at he hne ⊢ <;> contra_new
    all_goals
      intro e' he'
      cases e' <;> simp at he' ⊢
      subst he'
      omega
  · cases e <;> simp [stage] at he hne hb ⊢ <;> contra_new

lemma reach_half (k : ℕ) (_hk : k + 1 ≤ m) (h : Reach K m c (stage R (k + 1) false)) :
    Reach K m c (stage R (k + 1) true) := by
  refine batch h (fun e he => ?_) (fun e he hne => ?_) (fun e he hne hb => ?_)
  · cases e <;> simp [stage] at he ⊢ <;> omega
  · cases e <;> simp [stage] at he hne ⊢ <;> contra_new
  · cases e <;> simp [stage] at he hne hb ⊢ <;> contra_new
    all_goals
      rename_i j
      have hj : (j : ℕ) = k + 1 := by omega
      have hj0 : (j : ℕ) ≠ 0 := by omega
      rw [show inAsset j = .C (((⟨k, by omega⟩ : Fin (m + 1)) : ℕ) + 1) by simp [inAsset, hj],
        inflow_C _ _ _ _ _ (by simp; omega), show (((⟨k, by omega⟩ : Fin (m + 1)) : ℕ) + 1) = j by simp [hj],
        outflow_C _ _ _ _ _ hj0]
      simp [hj]

lemma reach_almost (hbud : K.totalW ≤ K.W + (m - 1) * c) (h : Reach K m c (stage R (m + 1) false)) :
    Reach K m c (almost R) := by
  refine batch h (fun e he => ?_) (fun e he hne => ?_) (fun e he hne hb => ?_)
  · cases e <;> simp [stage, almost] at he ⊢ <;> exact he
  · cases e <;> simp [stage, almost] at he hne ⊢ <;> contra_new
  · cases e <;> simp [stage, almost] at he hne hb <;> contra_new
    rw [asset_toX, outflow_B, inflow_B]
    have h1 : Edge.fromS ∈ (stage R (m + 1) false : Finset (Edge n m)) := by simp [stage]
    have h2 : ∀ j, Edge.fromYB j ∈ (stage R (m + 1) false : Finset (Edge n m)) := fun j => by
      simpa [stage] using Nat.le_of_lt_succ (ybLevel j).isLt
    have h3 : ∀ i, Edge.toX i ∈ (almost R : Finset (Edge n m)) := by simp [almost]
    simp only [h1, h2, h3, ite_true, sum_const, card_univ, Fintype.card_fin, smul_eq_mul]
    simpa [Knapsack.totalW, mul_comm] using hbud

lemma reach_erase (h : Reach K m c (almost R)) : Reach K m c (univ.erase .toS) := by
  refine batch h (fun e he => ?_) (fun e he hne => ?_) (fun e he hne hb => ?_)
  · cases e <;> simp [almost] at he ⊢
  · cases e <;> simp [almost] at he hne ⊢
    intro e' he'
    cases e' <;> simp at he' ⊢
  · cases e <;> simp [almost] at he hne hb ⊢

lemma reach_univ (h : Reach K m c (univ.erase .toS)) : Reach K m c univ := by
  refine batch h (erase_subset _ _) (fun e he hne => ?_) (fun e he hne hb => ?_)
  · cases e <;> simp at hne ⊢
  · cases e <;> simp at hne hb ⊢
    rw [outflow_D, inflow_D]
    simp

end Steps

/-- **Lemma 4.2** of [Chan–Lesani], repaired: if `K` is satisfiable then `{s, b}` is an adequate
leader set of `F = flower K m c`, provided `V ≥ 1` and the broker's bitcoin budget suffices,
`Σ_w(X) ≤ W + (m − 1)·c` (a condition that is also necessary, `budget_of_adequate`). -/
theorem adequate_of_satisfiable (hV : 1 ≤ K.V) (hbud : K.totalW ≤ K.W + (m - 1) * c)
    (hK : K.Satisfiable) : (flower K m c).Adequate (flowerOwn K m c) {.b, .s} := by
  obtain ⟨R, hRV, hRW⟩ := hK
  have hlev : ∀ k, k ≤ m → Reach K m c (stage R k true) := by
    intro k
    induction k with
    | zero => exact fun _ => reach_half0 R hV hRV (reach_stage0 R hRW)
    | succ k ih => exact fun hk => reach_half R k hk (reach_full R k (ih (by omega)))
  exact reach_univ (reach_erase R (reach_almost R hbud (reach_full R m (hlev m le_rfl))))

end Podc.HTLCBrokeringHardness
