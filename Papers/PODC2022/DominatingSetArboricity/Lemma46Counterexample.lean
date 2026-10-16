import Papers.PODC2022.DominatingSetArboricity.Randomized

/-!
# Lemma 4.6 fails for `λ = 1`

Lemma 4.6 is stated for every `λ > 0`. For `λ = 1` the number of phases `⌈log_γ λ⁻¹⌉` is `0`,
so `S' = ∅`, and `S ∪ S'` need not be dominating: a single vertex with `w = 1`, packing `x = 1`
(feasible, and `x ≥ λ τ`), `S = ∅`. (All applications in the paper have `λ < 1`.)
-/

namespace DominatingSetArboricity

open Finset SimpleGraph

/-- **Lemma 4.6 is false for `λ = 1`.** -/
theorem lemma_4_6_false_lam_one :
    let G : SimpleGraph (Fin 1) := ⊥
    IsPacking G 1 1 ∧ (∀ v ∉ dom G ∅, (1 : ℝ) * tau G 1 v ≤ 1) ∧
      ∀ cs, ¬ IsDominating G
        (runCoins (rstep G 1 2) cs 0 (numSteps G 2 1) (rinit ∅ 1)).T := by
  intro G
  have hτ : ∀ v, tau G 1 v = 1 := fun v => by
    unfold tau; exact le_antisymm (inf'_le _ (self_mem_cnbr v)) (le_inf' _ _ fun _ _ => le_rfl)
  refine ⟨⟨fun _ => zero_le_one, fun u => ?_⟩, fun v _ => by simp [hτ], fun cs h => ?_⟩
  · have : cnbr G u = {u} := by ext x; simp [cnbr, G]
    simp [this]
  · have h0 : numSteps G 2 1 = 0 := by simp [numSteps, numPhases]
    rw [h0] at h
    obtain ⟨u, hu, -⟩ := h 0
    simp [runCoins, rinit] at hu

end DominatingSetArboricity
