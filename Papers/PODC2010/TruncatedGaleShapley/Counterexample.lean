import Papers.PODC2010.TruncatedGaleShapley.Analysis

/-!
# Lemma 6 fails for `Δ = 1`, `i = 1`

Lemma 6 claims `f_i(R) ≤ γ w_i(B)` for all `γ > 0` and `i ≥ 1 + (Δ - 1)/γ`. For `Δ = 1` this
allows `i = 1`, but after round 1 nothing is matched (`w_1(B) = 0`) while every red node has a
pending proposal (`f_1(R) > 0`). The smallest instance is a single edge (`K₂`, no isolated nodes,
maximum degree `1`). Lemmas 4 and 5, on which the proof relies, are stated for `i ≥ 2`; with the
extra hypothesis `i ≥ 2` Lemma 6 holds (`Bicoloured.lemma_6`).
-/

namespace Podc.TruncatedGaleShapley

open Finset

/-- The single edge `{true, false}`; `true` is red. -/
def k2 : Bicoloured Bool where
  N v := {!v}
  symm := by intro u v h; simp at h ⊢; subst h; simp
  rank _ _ := 0
  rank_inj := by intro v u u' hu hu' _; simp at hu hu'; rw [hu, hu']
  red v := v
  red_ne := by intro u v h; simp at h; subst h; simp

lemma k2_degree (v : Bool) : (k2.N v).card ≤ 1 := by simp [k2]

/-- **Lemma 6 is false as stated** (with `Δ = 1`, `i = 1`, unit weights): for every `γ > 0`,
`1 ≥ 1 + (Δ - 1)/γ`, yet `f_1(R) = 1 > 0 = γ w_1(B)`. -/
theorem lemma_6_false_at_one {γ : ℝ} (_hγ : 0 < γ) :
    (1 + ((1 - 1 : ℕ) : ℝ) / γ ≤ ((1 : ℕ) : ℝ)) ∧
      γ * k2.blueW (k2.run 1) (fun _ => 1) < k2.potR (k2.run 1) (fun _ => 1) := by
  refine ⟨by simp, ?_⟩
  have hW : k2.blueW (k2.run 1) (fun _ => 1) = 0 := by
    refine sum_eq_zero fun b _ => ?_
    simp [Bicoloured.nodeW, Bicoloured.run_one_p]
  have hf : k2.potR (k2.run 1) (fun _ => 1) = 1 := by
    have hreds : k2.reds = {true} := by ext v; cases v <;> simp [Bicoloured.mem_reds, k2]
    rw [Bicoloured.potR, hreds, sum_singleton,
      Bicoloured.pot_of_unmatched (Bicoloured.run_one_p _ _)]
    obtain ⟨x, hx⟩ := k2.best_isSome (v := true) (S := (k2.run 1).C true)
      (by rw [Bicoloured.run_one_C]; simp [k2])
    rw [hx]
  rw [hW, hf]; simp

end Podc.TruncatedGaleShapley
