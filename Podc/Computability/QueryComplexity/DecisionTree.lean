import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Cslib.Foundations.Data.Nat.Factorial

-- CSLib candidate: Cslib/Computability/QueryComplexity/DecisionTree.lean

/-!
# Binary decision trees and the information-theoretic (average-case) lower bound

A deterministic algorithm that accesses its input only through yes/no queries (comparisons,
probes, …) is a binary decision tree: an internal node asks a query `q : Q`, and the answer
`o q : Bool` of the oracle `o : Q → Bool` selects the subtree. The number of queries made on
oracle `o` is the length of the root-to-leaf path followed (`DecisionTree.cost`).

## Main definitions

* `Cslib.DecisionTree Q α`: binary decision trees with queries in `Q` and outputs in `α`.
* `Cslib.DecisionTree.eval t o`, `Cslib.DecisionTree.cost t o`: output and number of queries on
  the oracle `o`.

## Main statements

* `Cslib.DecisionTree.card_mul_logb_le_sum_cost`: if a tree gives pairwise different outputs on
  the oracles of a finite family `S`, then the total number of queries over `S` is at least
  `|S| log₂ |S|`; i.e. the *average* number of queries is at least `log₂ |S|`
  (`Cslib.DecisionTree.logb_card_le_avg_cost`).
* `Cslib.half_mul_logb_le_logb_factorial`: `log₂ n! ≥ (n log₂ n)/2` for `n ≥ 8` (the `Ω(n log n)`
  sorting bound, from CSLib's `Nat.mul_log_sub_le_log_factorial`).

## Implementation notes

The average-depth bound is proved directly by induction on the tree, using convexity of
`x ↦ x log x` (`(a+b) log₂(a+b) ≤ a log₂ a + b log₂ b + (a+b)`), rather than via Kraft's
inequality.
-/

namespace Cslib

/-- A binary decision tree: queries in `Q`, outputs in `α`. -/
inductive DecisionTree (Q α : Type*) where
  /-- Stop and output `a`. -/
  | leaf (a : α) : DecisionTree Q α
  /-- Ask query `q`; continue with `yes` if the answer is `true`, with `no` otherwise. -/
  | node (q : Q) (yes no : DecisionTree Q α) : DecisionTree Q α

namespace DecisionTree

variable {Q α ι : Type*}

/-- The output of the tree on the oracle `o`. -/
def eval : DecisionTree Q α → (Q → Bool) → α
  | leaf a, _ => a
  | node q t₁ t₂, o => if o q then eval t₁ o else eval t₂ o

/-- The number of queries the tree asks on the oracle `o`. -/
def cost : DecisionTree Q α → (Q → Bool) → ℕ
  | leaf _, _ => 0
  | node q t₁ t₂, o => 1 + if o q then cost t₁ o else cost t₂ o

/-- Map the outputs of a tree. -/
def map {β : Type*} (g : α → β) : DecisionTree Q α → DecisionTree Q β
  | leaf a => leaf (g a)
  | node q t₁ t₂ => node q (map g t₁) (map g t₂)

/-- Rename the queries of a tree. -/
def comap {Q' : Type*} (g : Q → Q') : DecisionTree Q α → DecisionTree Q' α
  | leaf a => leaf a
  | node q t₁ t₂ => node (g q) (comap g t₁) (comap g t₂)

@[simp] theorem eval_map {β : Type*} (g : α → β) (t : DecisionTree Q α) (o : Q → Bool) :
    (t.map g).eval o = g (t.eval o) := by
  induction t with
  | leaf a => rfl
  | node q t₁ t₂ ih₁ ih₂ => simp only [map, eval]; split <;> simp [ih₁, ih₂]

@[simp] theorem cost_map {β : Type*} (g : α → β) (t : DecisionTree Q α) (o : Q → Bool) :
    (t.map g).cost o = t.cost o := by
  induction t with
  | leaf a => rfl
  | node q t₁ t₂ ih₁ ih₂ => simp only [map, cost]; split <;> simp [ih₁, ih₂]

@[simp] theorem eval_comap {Q' : Type*} (g : Q → Q') (t : DecisionTree Q α) (o : Q' → Bool) :
    (t.comap g).eval o = t.eval (o ∘ g) := by
  induction t with
  | leaf a => rfl
  | node q t₁ t₂ ih₁ ih₂ => simp [comap, eval, ih₁, ih₂]

@[simp] theorem cost_comap {Q' : Type*} (g : Q → Q') (t : DecisionTree Q α) (o : Q' → Bool) :
    (t.comap g).cost o = t.cost (o ∘ g) := by
  induction t with
  | leaf a => rfl
  | node q t₁ t₂ ih₁ ih₂ => simp [comap, cost, ih₁, ih₂]

end DecisionTree

/-- Convexity of `x ↦ x log x` at two points: `(a+b) log(a+b) ≤ a log a + b log b + (a+b) log 2`. -/
theorem add_mul_log_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * Real.log (a + b) ≤ a * Real.log a + b * Real.log b + (a + b) * Real.log 2 := by
  rcases eq_or_lt_of_le (add_nonneg ha hb) with h | h
  · rw [← h]; simp only [zero_mul, Real.log_zero, mul_zero, add_zero]
    have ha0 : a = 0 := by linarith
    have hb0 : b = 0 := by linarith
    subst ha0 hb0; simp
  have hc := Real.convexOn_mul_log.2 (Set.mem_Ici.2 ha) (Set.mem_Ici.2 hb)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at hc
  have hmid : 1 / 2 * a + 1 / 2 * b = (a + b) / 2 := by ring
  rw [hmid, Real.log_div h.ne' (by norm_num)] at hc
  nlinarith [hc]

/-- Base-2 version: `(a+b) log₂(a+b) ≤ a log₂ a + b log₂ b + (a+b)`. -/
theorem add_mul_logb_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (a + b) * Real.logb 2 (a + b) ≤ a * Real.logb 2 a + b * Real.logb 2 b + (a + b) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have := add_mul_log_add_le ha hb
  calc (a + b) * Real.logb 2 (a + b) = ((a + b) * Real.log (a + b)) / Real.log 2 := by
        rw [Real.logb, mul_div_assoc]
    _ ≤ (a * Real.log a + b * Real.log b + (a + b) * Real.log 2) / Real.log 2 :=
        div_le_div_of_nonneg_right this h2.le
    _ = a * Real.logb 2 a + b * Real.logb 2 b + (a + b) := by
        rw [Real.logb, Real.logb]; field_simp

namespace DecisionTree

variable {Q α ι : Type*}

/-- **Average-case information-theoretic lower bound.** If a decision tree gives pairwise
different outputs on the oracles `o i`, `i ∈ S`, then the total number of queries over `S` is at
least `|S| log₂ |S|`. -/
theorem card_mul_logb_le_sum_cost (t : DecisionTree Q α) (S : Finset ι) (o : ι → Q → Bool)
    (hinj : Set.InjOn (fun i => t.eval (o i)) S) :
    (S.card : ℝ) * Real.logb 2 S.card ≤ ∑ i ∈ S, (t.cost (o i) : ℝ) := by
  induction t generalizing S with
  | leaf a =>
    have hS : S.card ≤ 1 := by
      rw [Finset.card_le_one]
      intro i hi j hj
      exact hinj hi hj rfl
    have : Real.logb 2 S.card = 0 := by
      rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hS with h | h <;> simp [h]
    rw [this, mul_zero]
    exact Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  | node q t₁ t₂ ih₁ ih₂ =>
    set S₁ := S.filter (fun i => o i q = true)
    set S₂ := S.filter (fun i => ¬ o i q = true)
    have h₁ := ih₁ S₁ (by
      intro i hi j hj hij
      simp only [S₁, Finset.coe_filter, Set.mem_ofPred_eq] at hi hj
      exact hinj hi.1 hj.1 (by simpa [eval, hi.2, hj.2] using hij))
    have h₂ := ih₂ S₂ (by
      intro i hi j hj hij
      simp only [S₂, Finset.coe_filter, Set.mem_ofPred_eq] at hi hj
      exact hinj hi.1 hj.1 (by simpa [eval, hi.2, hj.2] using hij))
    have hcard : S.card = S₁.card + S₂.card :=
      (Finset.card_filter_add_card_filter_not _).symm
    have hsum : ∑ i ∈ S, ((node q t₁ t₂).cost (o i) : ℝ) =
        S.card + ∑ i ∈ S₁, (t₁.cost (o i) : ℝ) + ∑ i ∈ S₂, (t₂.cost (o i) : ℝ) := by
      have e1 : ∑ i ∈ S₁, ((node q t₁ t₂).cost (o i) : ℝ) =
          S₁.card + ∑ i ∈ S₁, (t₁.cost (o i) : ℝ) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp [cost, (Finset.mem_filter.1 hi).2]
      have e2 : ∑ i ∈ S₂, ((node q t₁ t₂).cost (o i) : ℝ) =
          S₂.card + ∑ i ∈ S₂, (t₂.cost (o i) : ℝ) := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i hi => ?_
        simp [cost, (Finset.mem_filter.1 hi).2]
      rw [← Finset.sum_filter_add_sum_filter_not S (fun i => o i q = true)]
      change ∑ i ∈ S₁, _ + ∑ i ∈ S₂, _ = _
      rw [e1, e2, hcard]; push_cast; ring
    rw [hsum, hcard]
    push_cast
    have := add_mul_logb_add_le (Nat.cast_nonneg S₁.card : (0 : ℝ) ≤ S₁.card)
      (Nat.cast_nonneg S₂.card : (0 : ℝ) ≤ S₂.card)
    linarith

/-- The average number of queries over a family with pairwise different outputs is at least
`log₂ |S|`. -/
theorem logb_card_le_avg_cost (t : DecisionTree Q α) (S : Finset ι) (o : ι → Q → Bool)
    (hS : S.Nonempty) (hinj : Set.InjOn (fun i => t.eval (o i)) S) :
    Real.logb 2 S.card ≤ (∑ i ∈ S, (t.cost (o i) : ℝ)) / S.card := by
  have hpos : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
  rw [le_div_iff₀ hpos, mul_comm]
  exact card_mul_logb_le_sum_cost t S o hinj

end DecisionTree

/-- For `n ≥ 8`, `log₂ n! ≥ (n log₂ n) / 2` — the `Ω(n log n)` form of the sorting bound. -/
theorem half_mul_logb_le_logb_factorial {n : ℕ} (hn : 8 ≤ n) :
    (n : ℝ) * Real.logb 2 n / 2 ≤ Real.logb 2 (n.factorial) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hnr : (8 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 2 ≤ Real.log n := by
    have he : Real.exp 2 ≤ 8 := by
      have := Real.exp_one_lt_d9
      have h22 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
      rw [h22]; nlinarith [Real.exp_pos 1]
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have := Nat.mul_log_sub_le_log_factorial n
  have key : (n : ℝ) * Real.log n / 2 ≤ Real.log (n.factorial) := by nlinarith
  calc (n : ℝ) * Real.logb 2 n / 2 = ((n : ℝ) * Real.log n / 2) / Real.log 2 := by
        rw [Real.logb]; ring
    _ ≤ Real.log (n.factorial) / Real.log 2 := div_le_div_of_nonneg_right key h2.le
    _ = Real.logb 2 (n.factorial) := rfl

end Cslib
