import Papers.PODC2010.EdgeDominatingSets.LowerBound
import Papers.PODC2010.EdgeDominatingSets.Theorem5

/-!
# Non-vacuity and tightness

The hypothesis of the lower bounds (the algorithm outputs an edge dominating set on the lower-bound
graph) is satisfiable, and the matching upper bounds are attained on these graphs: the algorithms of
Theorems 3 and 4 run on the graphs of Theorems 1 and 2 output edge dominating sets
(`nonvacuous_theorem_1/2`), and combining the lower and upper bounds, their outputs there have size
exactly `(4 - 2/d)·γ'`, resp. `(4 - 6/(d+1))·γ'` (`tight_theorem_1/2`).
-/

namespace Podc.EdgeDominatingSets

open Cslib.PortNumbering

/-- The lower-bound graph of Theorem 1 is a valid input for the algorithm of Theorem 3, which
outputs an edge dominating set on it. -/
theorem nonvacuous_theorem_1 (k : ℕ) [NeZero (2 * k)] :
    IsEDS (graph1 k).toSimpleGraph (outEdges (graph1 k) (alg3.eval (graph1 k) 1 fun _ => ())) :=
  (theorem_3 (d := 2 * k) (Nat.pos_of_ne_zero (NeZero.ne _)) (graph1 k) (graph1_isSimple k)
    (fun _ => rfl)).2.1

/-- The lower-bound graph of Theorem 2 is a valid input for the algorithm of Theorem 4, which
outputs an edge dominating set on it. -/
theorem nonvacuous_theorem_2 (k : ℕ) :
    IsEDS (graph2 k).toSimpleGraph
      (outEdges (graph2 k) ((alg4 (2 * k + 1)).eval (graph2 k) (2 + 2 * ((2 * k + 1) * (2 * k + 1)))
        fun _ => ())) :=
  (theorem_4 (d := 2 * k + 1) (odd_two_mul_add_one k) (graph2 k) (graph2_isSimple k)
    (fun _ => rfl)).2.1

/-- Tightness of Theorems 1 and 3: on the graph of Theorem 1, the output of `alg3` has size exactly
`(4 - 2/d) · γ'(G)` with `d = 2k`. -/
theorem tight_theorem_1 (k : ℕ) [NeZero (2 * k)] (hk : 0 < k) :
    ((outEdges (graph1 k) (alg3.eval (graph1 k) 1 fun _ => ())).card : ℝ) =
      (4 - 2 / (2 * k : ℝ)) * edgeDomNum (graph1 k).toSimpleGraph := by
  refine le_antisymm ?_ (graph1_lower k hk alg3 1 (nonvacuous_theorem_1 k))
  have := (theorem_3 (d := 2 * k) (by omega) (graph1 k) (graph1_isSimple k) (fun _ => rfl)).2.2
  push_cast at this
  exact this

/-- Tightness of Theorems 2 and 4: on the graph of Theorem 2, the output of `alg4` has size exactly
`(4 - 6/(d+1)) · γ'(G)` with `d = 2k + 1`. -/
theorem tight_theorem_2 (k : ℕ) :
    ((outEdges (graph2 k) ((alg4 (2 * k + 1)).eval (graph2 k) (2 + 2 * ((2 * k + 1) * (2 * k + 1)))
        fun _ => ())).card : ℝ) =
      (4 - 6 / ((2 * k + 1 : ℕ) + 1 : ℝ)) * edgeDomNum (graph2 k).toSimpleGraph :=
  le_antisymm (theorem_4 (d := 2 * k + 1) (odd_two_mul_add_one k) (graph2 k) (graph2_isSimple k)
    (fun _ => rfl)).2.2 (graph2_lower k _ _ (nonvacuous_theorem_2 k))

end Podc.EdgeDominatingSets
