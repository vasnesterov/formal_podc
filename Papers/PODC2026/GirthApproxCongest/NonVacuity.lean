import Papers.PODC2026.GirthApproxCongest.Theorems
import Papers.PODC2024.MinWeightCycleCongest.NonVacuity

/-!
# Non-vacuity of the algorithm hypotheses

On networks of diameter `≤ D`, full-information flooding (`gatherInputsAlg`, large messages) lets
every node learn the whole (weighted, directed) graph in `D` rounds and output its exact girth
(`estD`, `estU` from the companion formalization of Manoharan–Ramachandran). Hence the
hypotheses `hA` of `theorem_6_2_directed` / `theorem_6_2_weighted` (and of the fixed-parameter
theorems) are satisfiable for every `α ≥ 1`, with `T = 2 log₂ n + 4`.
-/

namespace Podc.GirthApproxCongest

open Cslib.Congest Podc.MinWeightCycleCongest

open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V] [Nonempty V] {W : ℕ}

/-- Flooding computes the exact girth of every digraph of diameter `≤ Dm` in `Dm` rounds. -/
theorem gather_approx_directed_diam {α : ℝ≥0∞} (hα : 1 ≤ α) (Dm : ℕ) (D : WDigraph V W)
    (hD : D.net.ediam ≤ Dm) :
    ApproxOutput α D.mwc (outputs (gatherInputsAlg V (DInput V W)) estD D.net D.view Dm) := by
  have hrun := gatherInputs_run_of_ediam (J := DInput V W) D.net D.view hD
  have hrec : reconD (fun a => some (D.view a)) = D := by
    cases D; rfl
  have hout : ∀ v, outputs (gatherInputsAlg V (DInput V W)) estD D.net D.view Dm v =
      some D.mwc := fun v => by
    simp only [outputs, estD, hrun v, hrec]
  refine ⟨⟨Classical.arbitrary V, by simp [hout]⟩, fun v e he => ?_⟩
  rw [hout v, Option.some.injEq] at he
  subst he
  exact ⟨le_rfl, le_mul_of_one_le_left zero_le hα⟩

/-- Flooding computes the exact girth of every weighted graph of diameter `≤ Dm` in `Dm`
rounds. -/
theorem gather_approx_undirected_diam {α : ℝ≥0∞} (hα : 1 ≤ α) (Dm : ℕ) (G : WGraph V W)
    (hG : G.net.ediam ≤ Dm) :
    ApproxOutput α G.mwc
      (outputs (gatherInputsAlg V (V → Option (Fin (W + 1)))) estU G.net G.view Dm) := by
  have hrun := gatherInputs_run_of_ediam (J := V → Option (Fin (W + 1))) G.net G.view hG
  have hrec : reconU (fun a => some (G.view a)) = G := by
    unfold reconU
    split_ifs with h
    · cases G; rfl
    · exact absurd ⟨fun u v => by simpa [WGraph.view] using G.symm u v,
        fun v => by simpa [WGraph.view] using G.loopless v⟩ h
  have hout : ∀ v, outputs (gatherInputsAlg V (V → Option (Fin (W + 1)))) estU G.net G.view Dm v =
      some G.mwc := fun v => by
    simp only [outputs, estU, hrun v, hrec]
  refine ⟨⟨Classical.arbitrary V, by simp [hout]⟩, fun v e he => ?_⟩
  rw [hout v, Option.some.injEq] at he
  subst he
  exact ⟨le_rfl, le_mul_of_one_le_left zero_le hα⟩

/-- The hypothesis of `theorem_6_2_directed` is satisfiable (flooding, `T = 2 log₂ n + 4`). -/
example {α : ℝ≥0∞} (hα : 1 ≤ α) :
    ∀ D : WDigraph V (W + 1), D.Unweighted →
      D.net.ediam ≤ 2 * ((Nat.log 2 (Fintype.card V) : ℕ∞) + 2) →
      ApproxOutput α D.mwc (outputs (gatherInputsAlg V (DInput V (W + 1))) estD D.net D.view
        (2 * (Nat.log 2 (Fintype.card V) + 2))) :=
  fun D _ hD => gather_approx_directed_diam hα _ D (by push_cast; exact hD)

/-- The hypothesis of `theorem_6_2_weighted` is satisfiable (flooding, `T = 2 log₂ n + 4`). -/
example {α : ℝ≥0∞} (hα : 1 ≤ α) {Wm : ℕ} :
    ∀ G : WGraph V Wm, (∀ u v c, G.wt u v = some c → 0 < c.val) →
      G.net.ediam ≤ 2 * ((Nat.log 2 (Fintype.card V) : ℕ∞) + 2) →
      ApproxOutput α G.mwc (outputs (gatherInputsAlg V (V → Option (Fin (Wm + 1)))) estU G.net
        G.view (2 * (Nat.log 2 (Fintype.card V) + 2))) :=
  fun G _ hG => gather_approx_undirected_diam hα _ G (by push_cast; exact hG)

end Podc.GirthApproxCongest
