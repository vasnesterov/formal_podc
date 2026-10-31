import Papers.PODC2025.KnapsackLCA.Defs

/-!
# No sublinear LCA for optimal or approximate Knapsack (Lemma 3.1, Theorems 3.2, 3.3)

* `lemma_3_1`: `R(OR_n) ≥ n/3` (proved, via the staged needle lemma).
* `theorem_3_2`, `theorem_3_3`: the paper's reductions from `OR_n`, formalized as
  query-preserving simulations (`orAlg`). They use the instance `I(x)` with profits
  `x_1, …, x_n, β`, whose total profit is *not* `1`: they hold for LCAs that are correct on all
  well-formed instances (Definition 2.2 without the normalisation of the profits).
* `theorem_3_2_normalized`, `theorem_3_3_normalized`: the statements for LCAs that are only
  required to be correct on *normalised* instances (total profit `1`, as Definition 2.2 demands).
  The paper's reduction does not apply (normalising `I(x)` requires knowing `|x|`); we prove
  them directly with a normalised "moving mass" family and the needle lemma. The bound becomes
  `⌊n / b⌋ / 3` with `b = ⌊1/α²⌋ + 1`, still `Ω(n)` for every fixed `α`.
-/

namespace Podc.KnapsackLCA

open Cslib Cslib.Probability.PMF Cslib.QueryTree

variable {Ω : Type*}

namespace LCA

variable {n : ℕ} (A : LCA n Ω)

theorem Correct.mono {𝓘 𝓘' : Set (Instance n)} {V V' : Instance n → Finset (Fin n) → Prop}
    {δ : ℝ} (h : A.Correct 𝓘 V δ) (h𝓘 : 𝓘' ⊆ 𝓘) (hV : ∀ I C, V I C → V' I C) :
    A.Correct 𝓘' V' δ := by
  intro I hI
  obtain ⟨C, hC⟩ := h I (h𝓘 hI)
  exact ⟨C, fun i => (hC i).trans (probReal_mono _ fun r hr => ⟨hV _ _ hr.1, hr.2⟩)⟩

end LCA

/-! ### Unit-weight instances -/

section UnitWeight

variable {n : ℕ}

theorem load_eq_card {I : Instance n} (hw : ∀ i, I.weight i = 1) (C : Finset (Fin n)) :
    I.load C = C.card := by
  simp [Instance.load, hw]

theorem feasible_iff_card_le_one {I : Instance n} (hw : ∀ i, I.weight i = 1) (hcap : I.cap = 1)
    (C : Finset (Fin n)) : I.Feasible C ↔ C.card ≤ 1 := by
  simp [Instance.Feasible, load_eq_card hw, hcap]

/-- In a unit-weight instance with weight limit 1, a feasible set containing `i` is `{i}`. -/
theorem eq_singleton_of_feasible {I : Instance n} (hw : ∀ i, I.weight i = 1) (hcap : I.cap = 1)
    {C : Finset (Fin n)} (hC : I.Feasible C) {i : Fin n} (hi : i ∈ C) : C = {i} := by
  rw [feasible_iff_card_le_one hw hcap] at hC
  exact Finset.eq_singleton_iff_unique_mem.2 ⟨hi, fun j hj => Finset.card_le_one.1 hC j hj i hi⟩

theorem feasible_singleton {I : Instance n} (hw : ∀ i, I.weight i = 1) (hcap : I.cap = 1)
    (i : Fin n) : I.Feasible {i} := by
  rw [feasible_iff_card_le_one hw hcap]; simp

/-- A feasible set avoiding `j` has value at most `c` if every other item has profit `≤ c`
(and `c ≥ 0`). -/
theorem value_le_of_feasible {I : Instance n} (hw : ∀ i, I.weight i = 1) (hcap : I.cap = 1)
    {C : Finset (Fin n)} (hC : I.Feasible C) {c : ℝ} (hc : 0 ≤ c) {j : Fin n} (hj : j ∉ C)
    (hp : ∀ i, i ≠ j → I.profit i ≤ c) : I.value C ≤ c := by
  rcases C.eq_empty_or_nonempty with h | ⟨i, hi⟩
  · simp [Instance.value, h, hc]
  · rw [eq_singleton_of_feasible hw hcap hC hi] at hj ⊢
    simp only [Instance.value, Finset.sum_singleton]
    exact hp i fun h => hj (by simp [h])

end UnitWeight

/-! ### Lemma 3.1 -/

/-- **Lemma 3.1.** The randomized query complexity of `OR_n` is at least `n/3`: every randomized
query algorithm computing `OR_n` with error at most `1/3` on every input makes at least `n/3`
queries. -/
theorem lemma_3_1 {n : ℕ} (μ : PMF Ω) (T : Ω → QueryTree (Fin n) Bool Bool) (q : ℕ)
    (hq : ∀ r x, (T r).cost x ≤ q)
    (hcorrect : ∀ x, 2 / 3 ≤ probReal μ {r | (T r).eval x = orFn x}) :
    (n : ℝ) / 3 ≤ q := by
  have := or_lower_bound μ T q (1 / 3) hq fun x => by linarith [hcorrect x]
  linarith

/-! ### The reduction from `OR_n` (Theorems 3.2 and 3.3 as in the paper) -/

section Reduction

variable {n : ℕ}

/-- The instance `I(x)` of the proofs of Theorems 3.2 (`β = 1/2`) and 3.3: items `1..n` are
`(x_i, 1)`, the last item is `(β, 1)`, weight limit `1`. -/
noncomputable def orInstance (β : ℝ) (x : Fin n → Bool) : Instance (n + 1) where
  item := Fin.snoc (α := fun _ => ℝ × ℕ) (fun i => ((if x i then 1 else 0 : ℝ), 1)) (β, 1)
  cap := 1

theorem orInstance_weight (β : ℝ) (x : Fin n → Bool) (i : Fin (n + 1)) :
    (orInstance β x).weight i = 1 := by
  induction i using Fin.lastCases <;> simp [orInstance, Instance.weight]

@[simp] theorem orInstance_profit_last (β : ℝ) (x : Fin n → Bool) :
    (orInstance β x).profit (Fin.last n) = β := by
  simp [orInstance, Instance.profit]

@[simp] theorem orInstance_profit_castSucc (β : ℝ) (x : Fin n → Bool) (i : Fin n) :
    (orInstance β x).profit i.castSucc = if x i then 1 else 0 := by
  simp [orInstance, Instance.profit]

theorem orInstance_wellFormed {β : ℝ} (hβ : 0 ≤ β) (x : Fin n → Bool) :
    (orInstance β x).WellFormed := by
  refine ⟨fun i => ?_, fun i => by rw [orInstance_weight]; rfl⟩
  induction i using Fin.lastCases with
  | last => simpa using hβ
  | cast i => simp only [orInstance_profit_castSucc]; split_ifs <;> norm_num

/-- In `I(x)`, the last item belongs to an `α`-approximate solution iff `OR(x) = 0`
(for `0 < β < α`). -/
theorem last_mem_iff {α β : ℝ} (hβ : 0 < β) (hβα : β < α) (x : Fin n → Bool)
    {C : Finset (Fin (n + 1))} (hC : (orInstance β x).IsApprox α C) :
    Fin.last n ∈ C ↔ orFn x = false := by
  have hw := orInstance_weight β x
  have hcap : (orInstance β x).cap = 1 := rfl
  constructor
  · intro hl
    rw [eq_singleton_of_feasible hw hcap hC.1 hl] at hC
    by_contra hor
    simp only [orFn, Bool.not_eq_false, decide_eq_true_eq] at hor
    obtain ⟨i, hi⟩ := hor
    have := hC.2 {i.castSucc} (feasible_singleton hw hcap _)
    simp [Instance.value, hi] at this
    linarith
  · intro hor
    simp only [orFn, decide_eq_false_iff_not, not_exists, Bool.not_eq_true] at hor
    by_contra hl
    have h1 := hC.2 {Fin.last n} (feasible_singleton hw hcap _)
    have h2 := value_le_of_feasible hw hcap hC.1 le_rfl hl fun i hi => by
      induction i using Fin.lastCases with
      | last => exact absurd rfl hi
      | cast i => simp [hor i]
    simp only [Instance.value, Finset.sum_singleton, orInstance_profit_last] at h1 h2
    nlinarith

/-- The simulation of one item query of `I(x)` by at most one query to `x`. -/
def simStep (β : ℝ) (j : Fin (n + 1)) : QueryTree (Fin n) Bool (ℝ × ℕ) :=
  Fin.lastCases (motive := fun _ => QueryTree (Fin n) Bool (ℝ × ℕ)) (.leaf (β, 1))
    (fun i => .query i fun b => .leaf ((if b then 1 else 0 : ℝ), 1)) j

theorem eval_simStep (β : ℝ) (x : Fin n → Bool) (j : Fin (n + 1)) :
    (simStep β j).eval x = (orInstance β x).item j := by
  induction j using Fin.lastCases <;> simp [simStep, orInstance]

theorem cost_simStep_le (β : ℝ) (x : Fin n → Bool) (j : Fin (n + 1)) :
    (simStep β j).cost x ≤ 1 := by
  induction j using Fin.lastCases <;> simp [simStep]

/-- The `OR_n` algorithm built from an LCA: ask the LCA (simulating `I(x)`) whether the last
item is in its solution, and negate the answer. -/
def orAlg (A : LCA (n + 1) Ω) (β : ℝ) (r : Ω) : QueryTree (Fin n) Bool Bool :=
  ((A.run 1 r (Fin.last n)).simulate (simStep β)).seq fun b => .leaf (!b)

theorem eval_orAlg (A : LCA (n + 1) Ω) (β : ℝ) (r : Ω) (x : Fin n → Bool) :
    (orAlg A β r).eval x = !A.answer (orInstance β x) r (Fin.last n) := by
  simp only [orAlg, eval_seq, eval_simulate, eval_leaf, LCA.answer]
  congr 2
  funext j
  exact eval_simStep β x j

theorem cost_orAlg_le (A : LCA (n + 1) Ω) (β : ℝ) {q : ℕ} (hq : A.QueryBound q) (r : Ω)
    (x : Fin n → Bool) : (orAlg A β r).cost x ≤ q := by
  simp only [orAlg, cost_seq, cost_leaf, add_zero]
  exact (cost_simulate_le _ _ _ 1 fun j => cost_simStep_le β x j).trans (by simpa using hq _ _ _ _)

/-- The reduction of Theorems 3.2/3.3 with failure probability `δ`: an LCA giving access to an
`α`-approximate solution of every well-formed instance with at most `q` queries yields an
`OR_n` algorithm with error `δ` and at most `q` queries, so `n (1 - 2δ) ≤ q`. -/
theorem reduction {α β δ : ℝ} (hβ : 0 < β) (hβα : β < α) (A : LCA (n + 1) Ω) {q : ℕ}
    (hq : A.QueryBound q) (hA : A.Correct {I | I.WellFormed} (fun I C => I.IsApprox α C) δ) :
    (n : ℝ) * (1 - 2 * δ) ≤ q := by
  refine or_lower_bound A.seed (orAlg A β) q δ (cost_orAlg_le A β hq) fun x => ?_
  obtain ⟨C, hC⟩ := hA (orInstance β x) (orInstance_wellFormed hβ.le x)
  refine (hC (Fin.last n)).trans (probReal_mono _ fun r hr => ?_)
  obtain ⟨hval, hans⟩ := hr
  simp only [Set.mem_ofPred_eq, eval_orAlg]
  have := last_mem_iff hβ hβα x hval
  cases h : A.answer (orInstance β x) r (Fin.last n) <;> cases h' : orFn x <;> simp_all

/-- **Theorem 3.2.** An LCA (correct on all well-formed instances, failure probability `1/3`)
giving query access to an optimal solution of Knapsack on `n + 1` items makes at least `n/3`
queries. -/
theorem theorem_3_2 (A : LCA (n + 1) Ω) {q : ℕ} (hq : A.QueryBound q)
    (hA : A.Correct {I | I.WellFormed} (fun I C => I.IsOptimal C) (1 / 3)) :
    (n : ℝ) / 3 ≤ q := by
  have := reduction (α := 1) (β := 1 / 2) (by norm_num) (by norm_num) A hq
    (hA.mono A le_rfl fun I C h => h.isApprox_one)
  linarith

/-- **Theorem 3.3.** For every `α ∈ (0, 1]`, an LCA (correct on all well-formed instances,
failure probability `1/3`) giving query access to an `α`-approximate solution of Knapsack on
`n + 1` items makes at least `n/3` queries. -/
theorem theorem_3_3 {α : ℝ} (hα : 0 < α) (A : LCA (n + 1) Ω) {q : ℕ} (hq : A.QueryBound q)
    (hA : A.Correct {I | I.WellFormed} (fun I C => I.IsApprox α C) (1 / 3)) :
    (n : ℝ) / 3 ≤ q := by
  have := reduction (β := α / 2) (by linarith) (by linarith) A hq hA
  linarith

end Reduction

/-! ### Normalised instances (repair of the proofs of Theorems 3.2 and 3.3) -/

section Normalized

variable {n : ℕ}

/-- Profit of the ordinary item with index `k` in the hard family: `c` everywhere in the base
instance (`m = none`); in the needle instance for block `m`, the block `[m b, m b + b)` has its
whole mass `b c` moved to its first item. -/
def blockProfit (b : ℕ) (c : ℝ) : Option ℕ → ℕ → ℝ
  | none, _ => c
  | some m, k => if k = m * b then b * c else if m * b < k ∧ k < m * b + b then 0 else c

/-- The normalised hard instance: ordinary items with profits `blockProfit b c m`, a special
last item of profit `γ c`, all weights `1`, weight limit `1`. -/
noncomputable def needleInstance (b : ℕ) (c γ : ℝ) (m : Option ℕ) : Instance (n + 1) where
  item := Fin.snoc (α := fun _ => ℝ × ℕ) (fun i : Fin n => (blockProfit b c m i.val, 1)) (γ * c, 1)
  cap := 1

theorem needleInstance_weight (b : ℕ) (c γ : ℝ) (m : Option ℕ) (i : Fin (n + 1)) :
    (needleInstance (n := n) b c γ m).weight i = 1 := by
  induction i using Fin.lastCases <;> simp [needleInstance, Instance.weight]

@[simp] theorem needleInstance_profit_last (b : ℕ) (c γ : ℝ) (m : Option ℕ) :
    (needleInstance (n := n) b c γ m).profit (Fin.last n) = γ * c := by
  simp [needleInstance, Instance.profit]

@[simp] theorem needleInstance_profit_castSucc (b : ℕ) (c γ : ℝ) (m : Option ℕ) (i : Fin n) :
    (needleInstance (n := n) b c γ m).profit i.castSucc = blockProfit b c m i.val := by
  simp [needleInstance, Instance.profit]

theorem blockProfit_nonneg (b : ℕ) {c : ℝ} (hc : 0 ≤ c) (m : Option ℕ) (k : ℕ) :
    0 ≤ blockProfit b c m k := by
  cases m with
  | none => exact hc
  | some m => simp only [blockProfit]; split_ifs <;> positivity

theorem sum_blockProfit {b : ℕ} (hb0 : 0 < b) (c : ℝ) (m : Option ℕ)
    (hm : ∀ m', m = some m' → (m' + 1) * b ≤ n) :
    ∑ k ∈ Finset.range n, blockProfit b c m k = n * c := by
  cases m with
  | none => simp [blockProfit]
  | some m =>
    have hmb := hm m rfl
    have h1 : m * b ≤ m * b + b := Nat.le_add_right _ _
    have h2 : m * b + b ≤ n := by nlinarith
    rw [← Finset.sum_range_add_sum_Ico _ h2, ← Finset.sum_range_add_sum_Ico _ h1]
    have e1 : ∑ k ∈ Finset.range (m * b), blockProfit b c (some m) k = (m * b : ℕ) * c := by
      rw [Finset.sum_congr rfl fun k hk => (show blockProfit b c (some m) k = c by
        simp only [Finset.mem_range] at hk
        simp only [blockProfit]; rw [ite_eq_right (by omega), ite_eq_right (by omega)])]
      simp
    have e3 : ∑ k ∈ Finset.Ico (m * b + b) n, blockProfit b c (some m) k =
        (n - (m * b + b) : ℕ) * c := by
      rw [Finset.sum_congr rfl fun k hk => (show blockProfit b c (some m) k = c by
        simp only [Finset.mem_Ico] at hk
        simp only [blockProfit]; rw [ite_eq_right (by omega), ite_eq_right (by omega)])]
      simp
    have e2 : ∑ k ∈ Finset.Ico (m * b) (m * b + b), blockProfit b c (some m) k = b * c := by
      rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
      rcases Nat.eq_zero_or_pos b with hb | hb
      · simp [hb]
      obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
      rw [Finset.sum_range_succ', Finset.sum_eq_zero fun j hj => ?_]
      · simp [blockProfit]
      · simp only [Finset.mem_range] at hj
        simp only [blockProfit]; rw [ite_eq_right (by omega), ite_eq_left (by omega)]
    rw [e1, e2, e3]
    have : ((n - (m * b + b) : ℕ) : ℝ) = n - (m * b + b) := by
      rw [Nat.cast_sub h2]; push_cast; ring
    rw [this]; push_cast; ring

theorem needleInstance_normalized {b : ℕ} (hb0 : 0 < b) {c γ : ℝ} (hc : 0 ≤ c) (hγ : 0 ≤ γ)
    (hsum : n * c + γ * c = 1) (m : Option ℕ) (hm : ∀ m', m = some m' → (m' + 1) * b ≤ n) :
    (needleInstance (n := n) b c γ m).Normalized := by
  refine ⟨⟨fun i => ?_, fun i => by rw [needleInstance_weight]; rfl⟩, ?_⟩
  · induction i using Fin.lastCases with
    | last => simpa using mul_nonneg hγ hc
    | cast i => simpa using blockProfit_nonneg b hc m i.val
  · rw [Fin.sum_univ_castSucc]
    simp only [needleInstance_profit_castSucc, needleInstance_profit_last]
    rw [Fin.sum_univ_eq_sum_range (fun k => blockProfit b c m k), sum_blockProfit hb0 c m hm, hsum]

/-- In the base instance every `α`-approximate solution contains the special item
(as `c < α γ c`). -/
theorem last_mem_base {c γ α' : ℝ} (hc : 0 < c) (hαγ : 1 < α' * γ) (bb : ℕ)
    {C : Finset (Fin (n + 1))} (hC : (needleInstance (n := n) bb c γ none).IsApprox α' C) :
    Fin.last n ∈ C := by
  have hw := needleInstance_weight (n := n) bb c γ none
  by_contra hl
  have h1 := hC.2 {Fin.last n} (feasible_singleton hw rfl _)
  have h2 := value_le_of_feasible hw rfl hC.1 hc.le hl fun i hi => by
    induction i using Fin.lastCases with
    | last => exact absurd rfl hi
    | cast i => simp [blockProfit]
  simp only [Instance.value, Finset.sum_singleton, needleInstance_profit_last] at h1 h2
  nlinarith

/-- In the needle instance for block `m`, no `α`-approximate solution contains the special
item (as `γ c < α b c`). -/
theorem last_not_mem_needle {c γ α : ℝ} {b : ℕ} (hc : 0 < c) (hγ : γ < α * b) (m : ℕ)
    (hm : (m + 1) * b ≤ n) (hb : 0 < b)
    {C : Finset (Fin (n + 1))} (hC : (needleInstance (n := n) b c γ (some m)).IsApprox α C) :
    Fin.last n ∉ C := by
  have hw := needleInstance_weight (n := n) b c γ (some m)
  intro hl
  rw [eq_singleton_of_feasible hw rfl hC.1 hl] at hC
  have hlt : m * b < n := by nlinarith
  have := hC.2 {(⟨m * b, hlt⟩ : Fin n).castSucc} (feasible_singleton hw rfl _)
  rw [Instance.value, Instance.value, Finset.sum_singleton, Finset.sum_singleton,
    needleInstance_profit_castSucc, needleInstance_profit_last] at this
  simp only [blockProfit, ↓reduceIte] at this
  nlinarith

/-- The core of the normalised lower bound, for block size `b ≥ 1` and profits with
`1 < α γ` and `γ < α b`: `⌊n / b⌋ (1 - 2δ) ≤ q`. -/
theorem normalized_core {α γ δ : ℝ} {b : ℕ} (hb : 0 < b) (hγ0 : 0 ≤ γ) (hαγ : 1 < α * γ)
    (hγb : γ < α * b) (A : LCA (n + 1) Ω) {q : ℕ} (hq : A.QueryBound q)
    (hA : A.Correct {I | I.Normalized} (fun I C => I.IsApprox α C) δ) :
    ((n / b : ℕ) : ℝ) * (1 - 2 * δ) ≤ q := by
  classical
  set c : ℝ := 1 / (n + γ)
  have hnγ : 0 < (n : ℝ) + γ := by
    have hγne : γ ≠ 0 := by rintro rfl; simp at hαγ; linarith
    have : (0 : ℝ) < γ := lt_of_le_of_ne hγ0 (Ne.symm hγne)
    positivity
  have hc : 0 < c := by positivity
  have hsum : n * c + γ * c = 1 := by
    simp only [c]; field_simp
  set M := n / b
  have hMb : ∀ m : Fin M, ((m : ℕ) + 1) * b ≤ n := fun m =>
    (Nat.le_div_iff_mul_le hb).1 m.2
  set I₀ := needleInstance (n := n) b c γ none
  set Im : Fin M → Instance (n + 1) := fun m => needleInstance b c γ (some m.val)
  -- every position is changed by at most one needle instance
  have hD : ∀ p : Fin (n + 1),
      (Finset.univ.filter fun m : Fin M => (Im m).item p ≠ I₀.item p).card ≤ 1 := by
    intro p
    refine Finset.card_le_one.2 fun m₁ h₁ m₂ h₂ => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    induction p using Fin.lastCases with
    | last => simp [Im, I₀, needleInstance] at h₁
    | cast k =>
      have key : ∀ m : Fin M, (Im m).item k.castSucc ≠ I₀.item k.castSucc →
          (m : ℕ) = k.val / b := by
        intro m hm
        simp only [Im, I₀, needleInstance, Fin.snoc_castSucc, ne_eq, Prod.mk.injEq, and_true,
          blockProfit] at hm
        have : (m : ℕ) * b ≤ k.val ∧ k.val < (m : ℕ) * b + b := by
          by_contra hcon
          apply hm
          rw [ite_eq_right (by omega), ite_eq_right (by omega)]
        exact (Nat.div_eq_of_lt_le (by linarith [this.1]) (by linarith [this.2])).symm
      exact Fin.ext ((key m₁ h₁).trans (key m₂ h₂).symm)
  have hneedle := card_mul_probReal_le_sum_add A.seed (fun r => A.run 1 r (Fin.last n))
    I₀.item q (fun r => hq _ _ _ _) Finset.univ (fun m => (Im m).item) 1 hD (fun b => b = true)
  -- base instance: the answer on the special item is "yes" with probability `≥ 1 - δ`
  have h0 : 1 - δ ≤ probReal A.seed {r | (A.run 1 r (Fin.last n)).eval I₀.item = true} := by
    obtain ⟨C, hC⟩ := hA I₀ (needleInstance_normalized hb hc.le hγ0 hsum none (by simp))
    refine (hC (Fin.last n)).trans (probReal_mono _ fun r hr => ?_)
    have := last_mem_base hc hαγ b hr.1
    simpa [LCA.answer, I₀, needleInstance] using hr.2.2 this
  -- needle instances: "yes" with probability `≤ δ`
  have hm : ∀ m : Fin M,
      probReal A.seed {r | (A.run 1 r (Fin.last n)).eval (Im m).item = true} ≤ δ := by
    intro m
    obtain ⟨C, hC⟩ := hA (Im m) (needleInstance_normalized hb hc.le hγ0 hsum _
      (fun m' h => by cases h; exact hMb m))
    have hev : {r | (Im m).IsApprox α (C r) ∧
        (A.answer (Im m) r (Fin.last n) = true ↔ Fin.last n ∈ C r)} ⊆
        {r | (A.run 1 r (Fin.last n)).eval (Im m).item = true}ᶜ := by
      intro r hr
      have := last_not_mem_needle hc hγb m (hMb m) hb hr.1
      simp only [Set.mem_compl_iff, Set.mem_ofPred_eq]
      intro h
      exact this (hr.2.1 (by simpa [LCA.answer, Im, needleInstance] using h))
    have := (hC (Fin.last n)).trans (probReal_mono _ hev)
    rw [probReal_compl] at this
    linarith
  have hsum' : ∑ m : Fin M, probReal A.seed
      {r | (A.run 1 r (Fin.last n)).eval (Im m).item = true} ≤ M * δ := by
    calc _ ≤ ∑ _m : Fin M, δ := Finset.sum_le_sum fun m _ => hm m
      _ = M * δ := by simp
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_one, mul_one] at hneedle
  nlinarith

/-- **Theorem 3.3, normalised.** For every `α > 0` (the paper: `α ∈ (0, 1]`), an LCA that is only required to be
correct (failure probability `1/3`) on *normalised* instances (Definition 2.2) and gives query
access to an `α`-approximate solution of Knapsack on `n + 1` items makes at least
`⌊n / b⌋ / 3` queries, where `b = ⌊1/α²⌋ + 1`. -/
theorem theorem_3_3_normalized {α : ℝ} (hα : 0 < α) (A : LCA (n + 1) Ω) {q : ℕ}
    (hq : A.QueryBound q)
    (hA : A.Correct {I | I.Normalized} (fun I C => I.IsApprox α C) (1 / 3)) :
    ((n / (⌊1 / α ^ 2⌋₊ + 1) : ℕ) : ℝ) / 3 ≤ q := by
  set b := ⌊1 / α ^ 2⌋₊ + 1
  have hb : 1 / α ^ 2 < b := by simp only [b]; push_cast; exact Nat.lt_floor_add_one _
  have hα2 : 1 < α ^ 2 * b := by
    rw [div_lt_iff₀ (by positivity)] at hb; linarith
  set γ := (1 / α + α * b) / 2
  have hγ0 : 0 ≤ γ := by positivity
  have hαγ : 1 < α * γ := by
    simp only [γ]; field_simp; nlinarith
  have hγb : γ < α * b := by
    simp only [γ]
    have : 1 / α < α * b := by rw [div_lt_iff₀ hα]; nlinarith
    linarith
  have := normalized_core (by omega) hγ0 hαγ hγb A hq hA
  linarith

/-- **Theorem 3.2, normalised.** An LCA that is only required to be correct (failure
probability `1/3`) on normalised instances and gives query access to an optimal solution of
Knapsack on `n + 1` items makes at least `⌊n / 2⌋ / 3` queries. -/
theorem theorem_3_2_normalized (A : LCA (n + 1) Ω) {q : ℕ} (hq : A.QueryBound q)
    (hA : A.Correct {I | I.Normalized} (fun I C => I.IsOptimal C) (1 / 3)) :
    ((n / 2 : ℕ) : ℝ) / 3 ≤ q := by
  have := theorem_3_3_normalized one_pos A hq
    (hA.mono A le_rfl fun I C h => h.isApprox_one)
  norm_num at this
  exact this

end Normalized

end Podc.KnapsackLCA
