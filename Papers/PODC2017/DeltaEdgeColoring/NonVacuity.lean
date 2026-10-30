import Papers.PODC2017.DeltaEdgeColoring.CliqueDecomposition
import Cslib.Computability.Distributed.Local.ColorReduction

/-!
# Non-vacuity of the black-box vertex colourer

The hypothesis `IsDeltaColorer col` of Theorems 2.4–2.6 and 3.2 is satisfiable by a genuine
LOCAL algorithm: start from the identifiers as colours (`n` colours) and run CSLib's standard
colour reduction (`Cslib.LocallyIterative.colorReduction`) for `n` rounds. (The paper uses the much
faster algorithm of Fraigniaud–Heinrich–Kosowski [17]; only its output specification matters for
the statements we check.)
-/

open Finset

namespace Podc.DeltaEdgeColoring

set_option linter.unusedSectionVars false

variable {V : Type*} [Fintype V] [DecidableEq V]

open Classical in
/-- The colourer "identifiers, then standard colour reduction for `n` rounds". -/
noncomputable def reductionColorer (H : SimpleGraph V) (Δ : ℕ) : V → ℕ :=
  (Cslib.LocallyIterative.colorReduction (Fintype.card V) Δ).run H
    (fun v => (Fintype.equivFin V v : ℕ)) (Fintype.card V)

theorem isDeltaColorer_reductionColorer : IsDeltaColorer (V := V) reductionColorer := by
  classical
  intro H Δ hΔ
  have hdeg : ∀ v, H.degree v ≤ Δ := fun v => by
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← Set.ncard_coe_finset,
      SimpleGraph.coe_neighborFinset]
    exact hΔ v
  have hp : Cslib.LocallyIterative.IsProper H (fun v => (Fintype.equivFin V v : ℕ)) := by
    intro u v huv h
    exact H.ne_of_adj huv ((Fintype.equivFin V).injective (Fin.ext h))
  have hm : ∀ v, (Fintype.equivFin V v : ℕ) < Fintype.card V := fun v => (Fintype.equivFin V v).2
  refine ⟨fun u v huv => ?_, fun v => ?_⟩
  · exact Cslib.LocallyIterative.colorReduction_isProper hdeg hp hm (Fintype.card V) huv
  · exact Cslib.LocallyIterative.colorReduction_le hdeg hp hm (Nat.sub_le _ _) v

/-- Non-vacuity of Theorems 2.5 and 2.6: CD-Coloring with the reduction colourer on the maximal
cliques of any graph is proper. -/
example [LinearOrder V] (G : SimpleGraph V) {D S t : ℕ} (ht : 0 < t)
    (hD : ∀ v, diversity G v ≤ D) (hS : ∀ K : Finset V, G.IsClique (K : Set V) → #K ≤ S)
    (x : ℕ) ⦃u v : V⦄ (huv : G.Adj u v) :
    cdColoring reductionColorer D t G (maximalCliques G) S x u ≠
      cdColoring reductionColorer D t G (maximalCliques G) S x v :=
  theorem_2_5 isDeltaColorer_reductionColorer ht (isCliqueCover_maximalCliques hD hS) x huv

end Podc.DeltaEdgeColoring
