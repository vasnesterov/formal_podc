import Papers.PODC2025.RendezvousLabeledLine.ESColor
import Papers.PODC2025.RendezvousLabeledLine.Main

/-!
# Lemma 3.5 and the unconditional Theorem 1.1

`ES.rule : ColRuling 40001` packages Algorithm 3 (with the corrected colouring step): a node `u`
of label `ℓ(u)` knows its output — a ruling-set node within `R - 1` and its colour in `[17]` —
after `40001 R log* ℓ(u)` rounds. Plugging it into Algorithm 5 gives Theorem 1.1 with an explicit
constant.
-/

namespace Podc.RendezvousLabeledLine

open Function

namespace ES

/-- Membership in the ruling set: decided at the node's own level. -/
def inS (R : ℕ) (ℓ : ℤ → ℕ) (v : ℤ) : Prop := Sle R (lstar (ℓ v)) ℓ v

/-- Colour of a ruling-set node (capped at `16`, which changes nothing on ruling-set nodes). -/
noncomputable def col (R : ℕ) (ℓ : ℤ → ℕ) (v : ℤ) : ℕ := min (colLe R (lstar (ℓ v)) ℓ v) 16

/-- `u` knows `w`: `w` joined the ruling set at a level `≤` that of `u`, within `R - 1` of `u`. -/
def knows (R : ℕ) (ℓ : ℤ → ℕ) (u w : ℤ) : Prop :=
  Sle R (lstar (ℓ u)) ℓ w ∧ |w - u| ≤ (R : ℤ) - 1

variable {R : ℕ} (hR : 1 ≤ R) {ℓ : ℤ → ℕ} (hℓ : Injective ℓ)
include hR hℓ

lemma inS_iff {i : ℕ} {v : ℤ} (hv : lstar (ℓ v) ≤ i) : inS R ℓ v ↔ Sle R i ℓ v :=
  (Sle_stable R hR hℓ hv v le_rfl).symm.trans (Sle_stable R hR hℓ hv v le_rfl) |>.trans
    (Sle_stable R hR hℓ hv v le_rfl).symm

lemma col_eq {i : ℕ} {v : ℤ} (hv : lstar (ℓ v) ≤ i) (hS : Sle R i ℓ v) :
    col R ℓ v = colLe R i ℓ v := by
  simp only [col]
  rw [← colLe_stable R (i := lstar (ℓ v)) (j := i) hv le_rfl]
  exact min_eq_left ((colLe_spec R hR hℓ i).2 v hS)

end ES

/-- **Lemma 3.5.** Algorithm 3 (with the corrected colouring step) is an early-stopping coloured
`(R, R-1)`-ruling-set rule with commitment time `40001 R log* ℓ(u)`. -/
noncomputable def ES.rule : ColRuling 40001 where
  inS := ES.inS
  col := ES.col
  knows := ES.knows
  col_lt R ℓ w := by simp only [ES.col]; omega
  inS_frame R ℓ v ε i := by
    simp only [ES.inS, comp]
    rw [← ES.Sle_isEquivar R _ ℓ v ε i]
  col_frame R ℓ v ε i := by
    simp only [ES.col, comp]
    rw [← ES.colLe_isEquivar R _ ℓ v ε i]
  packing R hR ℓ hℓ w w' hw hw' hne := by
    set i := max (lstar (ℓ w)) (lstar (ℓ w'))
    rw [ES.inS_iff hR hℓ (le_max_left _ _ : _ ≤ i)] at hw
    rw [ES.inS_iff hR hℓ (le_max_right _ _ : _ ≤ i)] at hw'
    exact (ES.Sle_spec R hR hℓ i).1 w w' hw hw' hne
  proper R hR ℓ hℓ w w' hw hw' hne hd := by
    set i := max (lstar (ℓ w)) (lstar (ℓ w'))
    have h1 : lstar (ℓ w) ≤ i := le_max_left _ _
    have h2 : lstar (ℓ w') ≤ i := le_max_right _ _
    rw [ES.inS_iff hR hℓ h1] at hw
    rw [ES.inS_iff hR hℓ h2] at hw'
    rw [ES.col_eq hR hℓ h1 hw, ES.col_eq hR hℓ h2 hw']
    exact (ES.colLe_spec R hR hℓ i).1 w w' hw hw' hne hd
  knows_spec R hR ℓ hℓ u w h := by
    refine ⟨h.2, ?_⟩
    have hl := (ES.Sle_spec R hR hℓ _).2.1 w h.1
    exact (ES.inS_iff hR hℓ hl).2 h.1
  knows_exists R hR ℓ hℓ u := by
    obtain ⟨s, hs, hus⟩ := (ES.Sle_spec R hR hℓ (lstar (ℓ u))).2.2.1 u le_rfl
    exact ⟨s, hs, by rwa [abs_sub_comm]⟩
  local_ R hR ℓ ℓ' hℓ hℓ' u hag w := by
    set i := lstar (ℓ u)
    have hi : 1 ≤ i := one_le_lstar _
    have hRi : (0 : ℤ) ≤ R * i := by positivity
    have hu : ℓ' u = ℓ u := hag u (by simp; positivity)
    have hball : ∀ (ρ : ℕ), (ρ : ℤ) + R ≤ ((40001 * R * i : ℕ) : ℤ) → |w - u| ≤ (R : ℤ) - 1 →
        ∀ x, |x - w| ≤ ρ → ℓ' x = ℓ x := fun ρ hρ hw x hx => hag x (by
      calc |x - u| = |(x - w) + (w - u)| := by ring_nf
        _ ≤ |x - w| + |w - u| := abs_add_le _ _
        _ ≤ _ := by omega)
    simp only [ES.knows, hu]
    by_cases hw : |w - u| ≤ (R : ℤ) - 1
    · have hS : ES.Sle R i ℓ' w ↔ ES.Sle R i ℓ w := by
        rw [ES.Sle_isLocal R hR i ℓ ℓ' hℓ hℓ' w (hball _ (by push_cast; nlinarith) hw)]
      refine ⟨by rw [hS], fun hh => ?_⟩
      have h1 := hh.1
      have hl := (ES.Sle_spec R hR hℓ i).2.1 w h1
      have hlw : ℓ' w = ℓ w := hball 0 (by push_cast; nlinarith) hw w (by simp)
      have hl' : lstar (ℓ' w) ≤ i := by rwa [hlw]
      rw [ES.col_eq hR hℓ hl h1, ES.col_eq hR hℓ' hl' (hS.2 h1)]
      exact ES.colLe_isLocal R hR i ℓ ℓ' hℓ hℓ' w (hball _ (by push_cast; nlinarith) hw)
    · exact ⟨⟨fun h => absurd h.2 hw, fun h => absurd h.2 hw⟩, fun h => absurd h.2 hw⟩

/-- **Theorem 1.1** (unconditional). `care(Algorithm 5)` with the early-stopping ruling sets of
Algorithm 3 achieves rendezvous at a node within `4 C₁(40001) · D · log* ℓ(u₀)` rounds after the
first wake-up, for every node `u₀` within distance `D` of one of the two starting nodes (so in
`O(D log* ℓ_min)` rounds), for every injective labelling, wake-up delay and port orientations. -/
theorem thm_1_1_final {ℓ : ℤ → ℕ} (hℓ : Injective ℓ) (vα vβ : ℤ) (εα εβ : ℤˣ) (τ : ℕ) (u₀ : ℤ)
    (hu₀ : |u₀ - vα| ≤ (vα - vβ).natAbs ∨ |u₀ - vβ| ≤ (vα - vβ).natAbs) :
    ∃ t ≤ 4 * (C₁ 40001 * (vα - vβ).natAbs * lstar (ℓ u₀)),
      (algFinal ES.rule).traj ℓ vα εα t = delayed τ ((algFinal ES.rule).traj ℓ vβ εβ) t :=
  thm_1_1 ES.rule hℓ vα vβ εα εβ τ u₀ hu₀

end Podc.RendezvousLabeledLine
