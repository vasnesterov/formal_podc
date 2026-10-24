import Papers.PODC2017.MaxISLocalRatio.SeqLR

/-!
# Line 11 of Algorithm 1 must accumulate the reductions

Line 11 of Algorithm 1 reads `w₁(v) = w(v) - w(u)` inside the loops `foreach u ∈ U, foreach v ∈ N(u)`,
with `w` the weights *before* the step. Taken literally, a vertex adjacent to several `u ∈ U` only
keeps the reduction of the *last* `u` processed, instead of the sum `w₂(v) = ∑_{u ∈ U ∩ N(v)} w(u)`
defined in the text of Section 2.1 (and used in the proof of Lemma 2.2). The intended line is
`w₁(v) = w₁(v) - w(u)`.

We show that with the literal line the induction step of Lemma 2.2 fails, and so does the
`Δ`-approximation of Algorithm 1. Graph (`Δ = 2`): edges `a₁v`, `a₂v`, `a₁b`, weights
`w(a₁) = 3, w(a₂) = 1, w(v) = 2, w(b) = 3` (vertices `0, 1, 2, 3`). Take `U = {a₁, a₂}`, processed
in the order `a₁, a₂`. Literal line 11 gives `w₁ = (0, 0, 1, 0)` (with the closed neighbourhood):
`v` keeps weight `2 - w(a₂) = 1`. The recursive call can only pick `U = {v}` and returns `{v}`, which
is optimal for `w₁`; line 13 then adds nothing (`a₁, a₂ ∈ N(v)`), so Algorithm 1 returns `{v}` of
weight `2`, while `{v, b}` is independent of weight `5 > Δ · 2`.

With the accumulated reduction, `w₁(v) = 2 - 3 - 1 < 0` and `v` is removed (`seqLR_isApprox`).
-/

set_option linter.unusedSectionVars false

namespace Podc.MaxISLocalRatio.LiteralLine11

open Finset

/-- The example graph on `{a₁, a₂, v, b} = {0, 1, 2, 3}` with edges `02`, `12`, `03`. -/
def exG : SimpleGraph (Fin 4) where
  Adj i j := (i = 0 ∧ j = 2) ∨ (i = 2 ∧ j = 0) ∨ (i = 1 ∧ j = 2) ∨ (i = 2 ∧ j = 1) ∨
    (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0)
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

instance : DecidableRel exG.Adj := fun i j => by unfold exG; infer_instance

/-- The weights `w(a₁) = 3, w(a₂) = 1, w(v) = 2, w(b) = 3`. -/
def exW : Fin 4 → ℝ := ![3, 1, 2, 3]

/-- Literal lines 8–11 of Algorithm 1: process `U` in the order `order`; for each `u` and each
`v ∈ N[u]` overwrite `w₁(v) := w(v) - w(u)`. -/
def litReduce {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (order : List V) (w : V → ℝ) : V → ℝ :=
  order.foldl (fun w₁ u v => if v ∈ cl G u then w v - w u else w₁ v) w

theorem cl_zero : cl exG 0 = {0, 2, 3} := by decide

theorem cl_one : cl exG 1 = {1, 2} := by decide

theorem exG_degree_le (v : Fin 4) : exG.degree v ≤ 2 := by
  fin_cases v <;> decide

theorem exU_indep : exG.IsIndepSet (({0, 1} : Finset (Fin 4)) : Set (Fin 4)) := by
  intro i hi j hj hij
  simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all [exG]

/-- Literal line 11 with `U = {a₁, a₂}` in the order `a₁, a₂` gives `w₁ = (0, 0, 1, 0)`. -/
theorem litReduce_ex : litReduce exG [0, 1] exW = ![0, 0, 1, 0] := by
  funext v
  fin_cases v <;> norm_num [litReduce, exW, cl_zero, cl_one]

/-- `{v}` is an optimal solution for the literal reduced weights (so also `2`-approximate). -/
theorem lit_x_isApprox : IsApprox exG 2 (litReduce exG [0, 1] exW) {2} := by
  rw [litReduce_ex]
  refine ⟨by simp, fun T _ => ?_⟩
  have h1 : wt (![0, 0, 1, 0] : Fin 4 → ℝ) T ≤ wt ![0, 0, 1, 0] univ :=
    sum_le_sum_of_subset_of_nonneg (subset_univ T) fun i _ _ => by fin_cases i <;> simp
  have h2 : wt (![0, 0, 1, 0] : Fin 4 → ℝ) univ = 1 := by simp [wt, Fin.sum_univ_four]
  have h3 : wt (![0, 0, 1, 0] : Fin 4 → ℝ) {2} = 1 := by simp [wt]
  linarith

/-- Line 13 adds nothing: both `a₁` and `a₂` are adjacent to `v`. -/
theorem lit_extend : extend exG {0, 1} {2} = {2} := by decide

/-- **The literal Algorithm 1 is not a `Δ`-approximation**: `{v, b}` is independent and has weight
`5 > 2 · w({v})`, although `Δ = 2`. Hence Lemma 2.2 fails for the literal reduction: `x = {v}` is
`2`-approximate for the literal `w₁`, but `x' = {v}` is not `2`-approximate for `w`. -/
theorem literal_line_11_fails :
    IsApprox exG 2 (litReduce exG [0, 1] exW) {2} ∧ extend exG {0, 1} {2} = {2} ∧
      exG.IsIndepSet (({2, 3} : Finset (Fin 4)) : Set (Fin 4)) ∧
      2 * wt exW {2} < wt exW {2, 3} ∧ ¬ IsApprox exG 2 exW (extend exG {0, 1} {2}) := by
  have hind : exG.IsIndepSet (({2, 3} : Finset (Fin 4)) : Set (Fin 4)) := by
    intro i hi j hj hij
    simp only [coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all [exG]
  have hw : 2 * wt exW {2} < wt exW {2, 3} := by norm_num [wt, exW]
  refine ⟨lit_x_isApprox, lit_extend, hind, hw, fun h => ?_⟩
  rw [lit_extend] at h
  have := h.2 _ hind
  linarith

/-- With the accumulated reduction of the text (`red`), `v` drops to weight `2 - 3 - 1 < 0`. -/
theorem red_ex : exW 2 - red exG {0, 1} exW 2 = -2 := by
  have : ({0, 1} : Finset (Fin 4)).filter (fun u => 2 ∈ cl exG u) = {0, 1} := by decide
  simp only [red, this]
  norm_num [exW]

end Podc.MaxISLocalRatio.LiteralLine11
