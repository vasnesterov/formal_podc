import Papers.PODC2019.HardnessOptimization.MDS

/-!
# A dominating set of size `4 log k + 2` that refutes an intermediate claim of the paper

In the converse direction of Lemma 2.1 the paper claims that a dominating set `D` of size
`4 log k + 2` with two row vertices "contains exactly one of every pair of neighbors `f^h_S, t^h_S`".
This is false: take `k = 2`, the inputs `x = y = ` "column `p` is all ones", and
`D = {a^p_2, b^p_2, u^0_{A₁}, u^0_{B₁}, t^0_{A₂}, t^0_{B₂}}`. Then `D` dominates `G_{x,y}` and contains
neither `f^0_{A₁}` nor `t^0_{A₁}` (the first-layer cycle is dominated by `{u_A, u_B}`). The lemma itself
survives (here `x(i,p) = y(i,p) = 1`), see `lemma_2_1`.
-/

namespace HardnessOptimization

instance {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : Finset V) : Decidable (IsDominating G D) := by
  unfold IsDominating; infer_instance

/-- The column index `p = 0`. -/
def pc : Idx 1 := fun _ => false

/-- Inputs with `x(i, p) = y(i, p) = 1` for all `i` and zero elsewhere. -/
def colInput : Idx 1 → Idx 1 → Bool := fun _ j => decide (j = pc)

/-- The dominating set of the counterexample. -/
def cexD : Finset (MV 1) :=
  {.row false true pc, .row true true pc, .gad false false 0 2, .gad true false 0 2,
    .gad false true 0 1, .gad true true 0 1}

/-- The paper's intermediate claim fails: `cexD` is a dominating set of size `4 log k + 2 = 6` that
contains neither `f^0_{A₁}` nor `t^0_{A₁}`. -/
theorem paper_intermediate_claim_false :
    IsDominating (mdsGraph colInput colInput) cexD ∧ cexD.card = 4 * 1 + 2 ∧
      MV.gad false false 0 0 ∉ cexD ∧ MV.gad false false 0 1 ∉ cexD := by
  refine ⟨?_, by decide, by decide, by decide⟩
  intro v
  rcases v with ⟨s, ℓ, i⟩ | ⟨s, ℓ, h, κ⟩
  · obtain rfl | rfl : i = pc ∨ i = fun _ => true := by
      cases h0 : i 0
      · left; funext a; rw [Subsingleton.elim a 0, h0]; rfl
      · right; funext a; rw [Subsingleton.elim a 0, h0]
    all_goals cases s <;> cases ℓ <;> decide
  · obtain rfl : h = 0 := Subsingleton.elim _ _
    cases s <;> cases ℓ <;> fin_cases κ <;> decide

end HardnessOptimization
