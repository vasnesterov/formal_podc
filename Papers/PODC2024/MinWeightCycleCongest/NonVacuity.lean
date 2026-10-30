import Papers.PODC2024.MinWeightCycleCongest.LowerBound
import Podc.Computability.Distributed.Congest.GatherInputs

/-!
# Non-vacuity of the hypotheses of Theorems 1.2.A and 1.4.A

On networks of diameter `≤ 2`, the full-information flooding algorithm `gatherInputsAlg` (with
messages of `gatherInputsBits` bits, i.e. large `B`) lets every node learn the whole weighted
graph in `2` rounds and output its exact minimum weight cycle. So the hypotheses `hA` of
`theorem_1_2_A` and `theorem_1_4_A` are satisfiable (for every `α ≥ 1`); the theorems are not
vacuous.
-/

namespace Podc.MinWeightCycleCongest

open Cslib.Congest

open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {W : ℕ}

/-! ### Directed graphs -/

/-- Rebuild a digraph from (gathered) local views. -/
def reconD (k : V → Option (DInput V W)) : WDigraph V W :=
  ⟨fun u v => ((k u).map fun f => (f v).1).join⟩

/-- Output the exact MWC of the rebuilt digraph. -/
noncomputable def estD : V → (V → Option (DInput V W)) → Option ℝ≥0∞ :=
  fun _ k => some (reconD k).mwc

/-- The flooding algorithm computes the exact MWC of every digraph of diameter `≤ 2` in `2`
rounds; in particular the hypothesis of `theorem_1_2_A` is satisfiable. -/
theorem gather_approx_directed {α : ℝ≥0∞} (hα : 1 ≤ α) (D : WDigraph V W)
    (hD : D.net.ediam ≤ 2) :
    ApproxOutput α D.mwc (outputs (gatherInputsAlg V (DInput V W)) estD D.net D.view 2) := by
  have hrun := gatherInputs_run_of_ediam (J := DInput V W) D.net D.view (D := 2)
    (by exact_mod_cast hD)
  have hrec : reconD (fun a => some (D.view a)) = D := by
    cases D; rfl
  have hout : ∀ v, outputs (gatherInputsAlg V (DInput V W)) estD D.net D.view 2 v =
      some D.mwc := fun v => by
    simp only [outputs, estD, hrun v, hrec]
  refine ⟨⟨Classical.arbitrary V, by simp [hout]⟩, fun v e he => ?_⟩
  rw [hout v, Option.some.injEq] at he
  subst he
  exact ⟨le_rfl, le_mul_of_one_le_left zero_le hα⟩

/-! ### Undirected graphs -/

/-- Rebuild an undirected graph from (gathered) local views (the empty graph if they are
inconsistent). -/
noncomputable def reconU (k : V → Option (V → Option (Fin (W + 1)))) : WGraph V W := by
  classical
  exact
    if h : (∀ u v, ((k u).map fun f => f v).join = ((k v).map fun f => f u).join) ∧
        ∀ v, ((k v).map fun f => f v).join = none then
      ⟨fun u v => ((k u).map fun f => f v).join, h.1, h.2⟩
    else ⟨fun _ _ => none, fun _ _ => rfl, fun _ => rfl⟩

/-- Output the exact MWC of the rebuilt graph. -/
noncomputable def estU : V → (V → Option (V → Option (Fin (W + 1)))) → Option ℝ≥0∞ :=
  fun _ k => some (reconU k).mwc

/-- The flooding algorithm computes the exact MWC of every weighted graph of diameter `≤ 2` in
`2` rounds; in particular the hypothesis of `theorem_1_4_A` is satisfiable. -/
theorem gather_approx_undirected {α : ℝ≥0∞} (hα : 1 ≤ α) (G : WGraph V W)
    (hG : G.net.ediam ≤ 2) :
    ApproxOutput α G.mwc
      (outputs (gatherInputsAlg V (V → Option (Fin (W + 1)))) estU G.net G.view 2) := by
  have hrun := gatherInputs_run_of_ediam (J := V → Option (Fin (W + 1))) G.net G.view (D := 2)
    (by exact_mod_cast hG)
  have hrec : reconU (fun a => some (G.view a)) = G := by
    unfold reconU
    split_ifs with h
    · cases G; rfl
    · exact absurd ⟨fun u v => by simpa [WGraph.view] using G.symm u v,
        fun v => by simpa [WGraph.view] using G.loopless v⟩ h
  have hout : ∀ v, outputs (gatherInputsAlg V (V → Option (Fin (W + 1)))) estU G.net G.view 2 v =
      some G.mwc := fun v => by
    simp only [outputs, estU, hrun v, hrec]
  refine ⟨⟨Classical.arbitrary V, by simp [hout]⟩, fun v e he => ?_⟩
  rw [hout v, Option.some.injEq] at he
  subst he
  exact ⟨le_rfl, le_mul_of_one_le_left zero_le hα⟩

end Podc.MinWeightCycleCongest
