/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Papers.PODC2021.HTLCBrokeringHardness.Run

/-!
# Main results: Lemma 4.4, Theorem 4.1, and the counterexample to Lemma 4.2

* `lemma_4_4_of_budget`, `theorem_4_1_of_budget`: the reduction is correct for every number of levels
  `m ≥ 1` and every bitcoin amount `c < min wᵢ` satisfying the broker's budget
  `Σ_w(X) ≤ W + (m − 1)·c`: `K` is satisfiable iff `F` has an adequate leader set of size two iff
  `{b, s}` is a minimum leader set of `F`.
* `lemma_4_2_false`: with the paper's choice `m = ⌈Σ_w(X)/min_w(X) − 1⌉ + 1`, `c = min_w(X) − 1`,
  the budget fails and Lemma 4.2 (hence Lemma 4.4 and the reduction of Theorem 4.1) is false: for
  the items `(1, 2), (1, 2), (1, 4)`, `V = 2`, `W = 4` the knapsack instance is satisfiable but the
  flower graph has **no** adequate leader set at all. `paper_minW_one`: when `min_w(X) = 1` the
  paper's graph is adequate only if all items fit into the knapsack; `lemma_4_2_false_minW_one`: a
  satisfiable weight-1 instance whose flower graph (with `c = min_w(X) − 1 = 0`) has no adequate
  leader set for any number of levels `m`.
* `theorem_4_1_fixed`: with `m = ⌈Σ_w(X)/(min_w(X) − 1)⌉ + 1` (the evident intent of the formula),
  the reduction is correct whenever all weights are `≥ 2`; `theorem_4_1_repaired`: doubling all
  weights and the capacity first gives a correct reduction for all instances with positive weights.
-/

namespace Podc.HTLCBrokeringHardness

open Finset Flower

variable {n m c : ℕ} {K : Knapsack n}

/-- **Lemma 4.4** of [Chan–Lesani] (for any `m ≥ 1` and `c` satisfying the budget): `K` is
satisfiable iff `F` has an adequate leader set of size two. -/
theorem lemma_4_4_of_budget (hV : 2 ≤ K.V) (hv : ∀ i, K.v i < K.V) (hc : ∀ i, c < K.w i)
    (hm : 1 ≤ m) (hbud : K.totalW ≤ K.W + (m - 1) * c) :
    K.Satisfiable ↔ ∃ L : Finset (Party n m), L.card = 2 ∧ (flower K m c).Adequate (flowerOwn K m c) L := by
  constructor
  · exact fun hK => ⟨{.b, .s}, card_pair (by simp), adequate_of_satisfiable (by omega) hbud hK⟩
  · rintro ⟨L, hL, hA⟩
    rw [(lemma_4_3 hV hv hc hA).2 hL] at hA
    exact satisfiable_of_adequate hm le_rfl hA

/-- **Theorem 4.1** of [Chan–Lesani], the reduction (for any `m ≥ 1` and `c` satisfying the budget):
`K` is satisfiable iff `{b, s}` is a minimum leader set of `F`, iff the minimum leader sets of `F`
have size two. -/
theorem theorem_4_1_of_budget (hV : 2 ≤ K.V) (hv : ∀ i, K.v i < K.V) (hc : ∀ i, c < K.w i)
    (hm : 1 ≤ m) (hbud : K.totalW ≤ K.W + (m - 1) * c) :
    (K.Satisfiable ↔ (flower K m c).IsMinimumLeaderSet (flowerOwn K m c) {.b, .s}) ∧
    (K.Satisfiable ↔ ∃ L : Finset (Party n m),
      (flower K m c).IsMinimumLeaderSet (flowerOwn K m c) L ∧ L.card = 2) := by
  have hmin : K.Satisfiable → (flower K m c).IsMinimumLeaderSet (flowerOwn K m c) {.b, .s} :=
    fun hK => ⟨adequate_of_satisfiable (by omega) hbud hK, fun L' hL' => by
      rw [card_pair (by simp)]; exact (lemma_4_3 hV hv hc hL').1⟩
  refine ⟨⟨hmin, fun h => satisfiable_of_adequate hm le_rfl h.1⟩,
    ⟨fun hK => ⟨_, hmin hK, card_pair (by simp)⟩, fun ⟨L, hL, h2⟩ => ?_⟩⟩
  exact (lemma_4_4_of_budget hV hv hc hm hbud).2 ⟨L, h2, hL.1⟩

/-! ### The paper's parameters -/

/-- For the paper's flower graph, the budget `Σ_w(X) ≤ W + (m − 1)(min_w(X) − 1)` is necessary for
*any* leader set to be adequate. -/
theorem paper_budget_of_adequate {L : Finset (Party n K.paperM)}
    (hA : (paperFlower K).Adequate (paperOwn K) L) :
    K.totalW ≤ K.W + (K.paperM - 1) * (K.minW - 1) :=
  budget_of_adequate hA

/-- With `min_w(X) = 1` the paper's flower graph has an adequate leader set only if all items fit
into the knapsack. So Lemma 4.2 fails for every satisfiable instance with `min_w(X) = 1 < Σ_w(X) − W`. -/
theorem paper_minW_one (h1 : K.minW = 1) {L : Finset (Party n K.paperM)}
    (hA : (paperFlower K).Adequate (paperOwn K) L) : K.totalW ≤ K.W := by
  simpa [h1] using paper_budget_of_adequate hA

/-- **Lemma 4.3** of [Chan–Lesani] for the paper's flower graph (true as stated, under the paper's
assumption that no item has value `≥ V`, with `V ≥ 2` and positive weights). -/
theorem lemma_4_3_paper (hV : 2 ≤ K.V) (hv : ∀ i, K.v i < K.V) (hw : ∀ i, 0 < K.w i)
    {L : Finset (Party n K.paperM)} (hA : (paperFlower K).Adequate (paperOwn K) L) :
    2 ≤ L.card ∧ (L.card = 2 → L = {.b, .s}) :=
  lemma_4_3 hV hv (fun i => by have := K.minW_le i; have := hw i; omega) hA

/-- **Lemma 4.4, backward direction**, for the paper's flower graph (true as stated). -/
theorem lemma_4_4_backward_paper (hV : 2 ≤ K.V) (hv : ∀ i, K.v i < K.V) (hw : ∀ i, 0 < K.w i)
    {L : Finset (Party n K.paperM)} (hL : L.card = 2) (hA : (paperFlower K).Adequate (paperOwn K) L) :
    K.Satisfiable := by
  rw [(lemma_4_3_paper hV hv hw hA).2 hL] at hA
  exact satisfiable_of_adequate (by simp [Knapsack.paperM]) le_rfl hA

/-- The counterexample instance: items `(v, w) = (1, 2), (1, 2), (1, 4)`, `V = 2`, `W = 4`. -/
def K₁ : Knapsack 3 := ⟨![1, 1, 1], ![2, 2, 4], 2, 4⟩

lemma K₁_minW : K₁.minW = 2 :=
  le_antisymm (K₁.minW_le 0) (le_ciInf fun i => by fin_cases i <;> decide)

lemma K₁_totalW : K₁.totalW = 8 := by simp [Knapsack.totalW, K₁, Fin.sum_univ_three]

lemma K₁_paperM : K₁.paperM = 4 := by
  rw [Knapsack.paperM, K₁_totalW, K₁_minW]
  norm_num

lemma K₁_satisfiable : K₁.Satisfiable := ⟨{0, 1}, by decide, by decide⟩

/-- **Lemma 4.2 of [Chan–Lesani] is false** for the paper's construction (`m = ⌈Σ_w(X)/min_w(X) −
1⌉ + 1`, bitcoin contracts `(yᵢ, b) = (min_w(X) − 1) B`): the instance `K₁` satisfies all the paper's
assumptions (`V ≥ 2`, no single item of value `≥ V`, positive weights) and is satisfiable, yet its
flower graph has no adequate leader set at all, in particular none of size two. Hence the forward
direction of Lemma 4.4 is false too, and the reduction does not prove Theorem 4.1. -/
theorem lemma_4_2_false :
    K₁.Satisfiable ∧ 2 ≤ K₁.V ∧ (∀ i, K₁.v i < K₁.V) ∧ (∀ i, 0 < K₁.w i) ∧
      ∀ L, ¬ (paperFlower K₁).Adequate (paperOwn K₁) L := by
  refine ⟨K₁_satisfiable, by decide, by decide, by decide, fun L hA => ?_⟩
  have h := paper_budget_of_adequate hA
  rw [K₁_paperM, K₁_minW, K₁_totalW] at h
  revert h; decide

/-- A weight-1 instance: items `(v, w) = (1, 1), (1, 1), (1, 2)`, `V = 2`, `W = 2`. -/
def K₂ : Knapsack 3 := ⟨![1, 1, 1], ![1, 1, 2], 2, 2⟩

lemma K₂_minW : K₂.minW = 1 :=
  le_antisymm (K₂.minW_le 0) (le_ciInf fun i => by fin_cases i <;> decide)

/-- **Lemma 4.2 of [Chan–Lesani] fails for weight-1 instances**, independently of the choice of `m`:
with `min_w(X) = 1` the contracts `(yᵢ, b)` carry `min_w(X) − 1 = 0` bitcoins. The instance `K₂`
satisfies all the paper's assumptions (`V ≥ 2`, no single item of value `≥ V`, positive weights,
and even `wᵢ ≤ W` for every item) and is satisfiable, but for **every** number
of levels `m` the flower graph with `c = min_w(X) − 1` has no adequate leader set. (The intended formula
`m = ⌈Σ_w(X)/(min_w(X) − 1)⌉ + 1` is undefined here.) -/
theorem lemma_4_2_false_minW_one :
    K₂.Satisfiable ∧ 2 ≤ K₂.V ∧ (∀ i, K₂.v i < K₂.V) ∧ (∀ i, 0 < K₂.w i ∧ K₂.w i ≤ K₂.W) ∧
      ∀ m (L : Finset (Party 3 m)),
        ¬ (flower K₂ m (K₂.minW - 1)).Adequate (flowerOwn K₂ m (K₂.minW - 1)) L := by
  refine ⟨⟨{0, 1}, by decide, by decide⟩, by decide, by decide, by decide, fun m L hA => ?_⟩
  have h := budget_of_adequate hA
  rw [K₂_minW] at h
  have ht : K₂.totalW = 4 := by simp [Knapsack.totalW, K₂, Fin.sum_univ_three]
  rw [ht] at h
  revert h; simp [K₂]

/-! ### The repaired parameters -/

/-- The intended number of levels: `m = ⌈Σ_w(X) / (min_w(X) − 1)⌉ + 1`. -/
noncomputable def Knapsack.fixedM {n : ℕ} (K : Knapsack n) : ℕ :=
  ⌈(K.totalW : ℚ) / ((K.minW - 1 : ℕ) : ℚ)⌉₊ + 1

lemma budget_fixedM (hw : ∀ i, 2 ≤ K.w i) : K.totalW ≤ K.W + (K.fixedM - 1) * (K.minW - 1) := by
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · simp [Knapsack.totalW]
  have hmin : 2 ≤ K.minW := le_ciInf hw
  have hd : (0 : ℚ) < ((K.minW - 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < K.minW - 1)
  have h1 : (K.totalW : ℚ) ≤ (⌈(K.totalW : ℚ) / ((K.minW - 1 : ℕ) : ℚ)⌉₊ : ℚ) * ((K.minW - 1 : ℕ) : ℚ) :=
    (div_le_iff₀ hd).1 (Nat.le_ceil _)
  have h2 : K.totalW ≤ ⌈(K.totalW : ℚ) / ((K.minW - 1 : ℕ) : ℚ)⌉₊ * (K.minW - 1) := by exact_mod_cast h1
  simp only [Knapsack.fixedM, Nat.add_sub_cancel]
  omega

/-- **Theorem 4.1**, repaired reduction for weights `≥ 2`: with `m = ⌈Σ_w(X)/(min_w(X) − 1)⌉ + 1`,
`K` is satisfiable iff `{b, s}` is a minimum leader set of the flower graph. -/
theorem theorem_4_1_fixed (hV : 2 ≤ K.V) (hv : ∀ i, K.v i < K.V) (hw : ∀ i, 2 ≤ K.w i) :
    K.Satisfiable ↔
      (flower K K.fixedM (K.minW - 1)).IsMinimumLeaderSet (flowerOwn K K.fixedM (K.minW - 1)) {.b, .s} :=
  (theorem_4_1_of_budget hV hv (fun i => by have := K.minW_le i; have := hw i; omega)
    (by simp [Knapsack.fixedM]) (budget_fixedM hw)).1

/-- Doubling all weights and the capacity. -/
def Knapsack.double {n : ℕ} (K : Knapsack n) : Knapsack n := ⟨K.v, fun i => 2 * K.w i, K.V, 2 * K.W⟩

lemma Knapsack.satisfiable_double : K.double.Satisfiable ↔ K.Satisfiable := by
  simp only [Knapsack.Satisfiable, Knapsack.double, ← mul_sum]
  exact exists_congr fun R => and_congr_right fun _ => by omega

/-- **Theorem 4.1**, repaired reduction for all instances with positive weights (and the paper's
standing assumptions `V ≥ 2`, `vᵢ < V`): first double all weights and the capacity, then build the
flower graph with `m = ⌈Σ_w/(min_w − 1)⌉ + 1`. -/
theorem theorem_4_1_repaired (hV : 2 ≤ K.V) (hv : ∀ i, K.v i < K.V) (hw : ∀ i, 1 ≤ K.w i) :
    K.Satisfiable ↔
      (flower K.double K.double.fixedM (K.double.minW - 1)).IsMinimumLeaderSet
        (flowerOwn K.double K.double.fixedM (K.double.minW - 1)) {.b, .s} := by
  rw [← Knapsack.satisfiable_double]
  exact theorem_4_1_fixed hV hv fun i => by simp only [Knapsack.double]; have := hw i; omega

end Podc.HTLCBrokeringHardness
