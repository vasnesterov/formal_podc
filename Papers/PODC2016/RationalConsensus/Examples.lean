import Papers.PODC2016.RationalConsensus.Theorem1
import Papers.PODC2016.RationalConsensus.Theorem2

/-!
# Non-vacuity

The hypotheses of Theorems 1 and 2 are satisfiable: `σ_cons` (Algorithm 1 as written, `selfShare = true`) solves
fair consensus for `n = 3`, `f = 1` (over `𝔽_5`), and hence, by Theorem 1, it is not a
`1`-Nash equilibrium for any utilities in which agents care only about consensus.
-/

namespace Podc.RationalConsensus.Cons

local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
local instance : Fact (1 < 3) := ⟨by norm_num⟩

/-- `σ_cons` solves fair consensus for `n = 3`, `f = 1`. -/
theorem sigmaCons_fair_3_1 :
    SolvesFairConsensus (seedMeasure 3 1 5) (sigmaCons (n := 3) (f := 1) (p := 5) true) 1 :=
  theorem_2 (by norm_num) (by norm_num)

/-- The received-only reading of the forwarding step is not even fair consensus for `n = 3`,
`f = 1`. -/
theorem sigmaCons_receivedOnly_not_fair_3_1 :
    ¬ SolvesFairConsensus (seedMeasure 3 1 5) (sigmaCons (n := 3) (f := 1) (p := 5) false) 1 :=
  theorem_2_receivedOnly_false (by norm_num) (Or.inl rfl)

/-- Theorem 1 applied to `σ_cons`: it is not a `1`-Nash equilibrium. -/
theorem sigmaCons_not_nash (u : Utility (Fin 3)) :
    ¬ IsNash (seedMeasure 3 1 5) u (sigmaCons (n := 3) (f := 1) (p := 5) true) 1 := by
  have : MeasureTheory.IsProbabilityMeasure (seedMeasure 3 1 5) := by
    unfold seedMeasure; infer_instance
  exact theorem_1 (by simp) _ u _ le_rfl sigmaCons_fair_3_1

end Podc.RationalConsensus.Cons
