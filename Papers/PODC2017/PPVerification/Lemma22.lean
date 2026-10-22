import Papers.PODC2017.PPVerification.Defs

/-!
# Lemma 22: checking condition (b) of LayeredTermination locally

A configuration is `U`-dead iff it is terminal for `U` (every enabled transition of `U` is
silent). Condition (b) of Definition 4 for a layer `S` with lower layers `U` says that `S`-steps
preserve `U`-deadness. Lemma 22 reduces this to a check on pairs of transitions: `S`-steps do
**not** preserve `U`-deadness iff there are `s ∈ S` and a non-silent `u ∈ U` such that no
non-silent `u' ∈ U` is enabled at `pre(s) + (pre(u) ⊖ post(s))`.

(The paper states Lemma 22 for `S = T \ U` inside one protocol, while Proposition 7 applies it to
`P[Tᵢ]` with `U = T₁ ∪ ⋯ ∪ Tᵢ₋₁`; we state it for arbitrary `S` and `U`.)
-/

namespace Podc.PPVerification

open Cslib.PopulationProtocol

variable {Q : Type*} [DecidableEq Q]

/-- `S`-steps preserve `U`-deadness (condition (b) of Definition 4). -/
def PreservesDead (S U : Set (Transition Q)) : Prop :=
  ∀ C C', MReach S C C' → Terminal U C → Terminal U C'

/-- **Lemma 22.** -/
theorem lemma_22 (S U : Set (Transition Q)) :
    ¬ PreservesDead S U ↔ ∃ s ∈ S, ∃ u ∈ U, ¬ u.Silent ∧
      ∀ u' ∈ U, ¬ u'.Silent → ¬ u'.pre ≤ s.pre + (u.pre - s.post) := by
  constructor
  · intro h
    simp only [PreservesDead, not_forall] at h
    obtain ⟨C, C', hreach, hC, hC'⟩ := h
    -- the last step from a `U`-dead to a non-`U`-dead configuration
    have : ∃ B D, Terminal U B ∧ ¬ Terminal U D ∧ MStep S B D := by
      induction hreach with
      | refl => exact absurd hC hC'
      | @tail B D _ hBD ih =>
        by_cases hB : Terminal U B
        · exact ⟨B, D, hB, hC', hBD⟩
        · exact ih hB
    obtain ⟨B, D, hB, hD, s, hs, hf⟩ := this
    rw [terminal_iff_forall_silent] at hD
    push Not at hD
    obtain ⟨u, hu, hle, hns⟩ := hD
    refine ⟨s, hs, u, hu, hns, fun u' hu' hns' hle' => hns' ?_⟩
    refine terminal_iff_forall_silent.1 hB u' hu' (hle'.trans ?_)
    have h1 : u.pre - s.post ≤ D - s.post := tsub_le_tsub_right hle _
    have h2 : D - s.post = B - s.pre := by rw [hf.2, add_tsub_cancel_right]
    calc s.pre + (u.pre - s.post) ≤ s.pre + (B - s.pre) := by
          rw [← h2]; exact add_le_add_right h1 _
      _ = B := add_tsub_cancel_of_le hf.1
  · rintro ⟨s, hs, u, hu, hns, h⟩ hpres
    let C₀ := s.pre + (u.pre - s.post)
    have hf : s.Fires C₀ (C₀ - s.pre + s.post) := ⟨le_add_right le_rfl, rfl⟩
    have hdead : Terminal U C₀ :=
      terminal_iff_forall_silent.2 fun u' hu' hle => by
        by_contra hns'; exact h u' hu' hns' hle
    have hC := hpres _ _ (.single ⟨s, hs, hf⟩) hdead
    refine hns (terminal_iff_forall_silent.1 hC u hu ?_)
    simp only [C₀, add_tsub_cancel_left]
    exact le_tsub_add

end Podc.PPVerification
