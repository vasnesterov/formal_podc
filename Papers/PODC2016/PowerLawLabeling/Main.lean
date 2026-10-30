import Papers.PODC2016.PowerLawLabeling.LowerBound
import Papers.PODC2016.PowerLawLabeling.Props
import Papers.PODC2016.PowerLawLabeling.Labeling

/-!
# Near-optimal adjacency labeling scheme for power-law graphs — main results

Petersen, Rotbart, Simonsen, Wulff-Nilsen, PODC 2016 (arXiv:1502.03971v1).

* `theorem1` (Labeling.lean): `√(2cn log n) + 2 log n + 1` labels for `c`-sparse graphs.
* `prop4` (Labeling.lean): `⌊√(cn)/2⌋` lower bound for `c`-sparse graphs (needs `c < n`;
  `prop4_false`).
* `prop1`, `prop2`, `prop3` (Props.lean): max degree, sparsity, `P'_α ⊆ P_α`.
* `theorem2` (Labeling.lean): `(C'n)^{1/α} (log n)^{1-1/α} + 2 log n + 1` labels for `P_α`.
* `theorem3` (here) / `theorem3_proper` (LowerBound.lean): `Ω(n^{1/α})` lower bound.
* Non-vacuity: `eventually_exists_isProperPowerLaw`, `eventually_exists_isPowerLaw`.
-/

namespace Podc.PowerLawLabeling

open Filter

variable {α : ℝ}

/-- A labeling scheme for a family is one for every subfamily. -/
theorem HasAdjLabeling.mono {n : ℕ} {F₁ F₂ : SimpleGraph (Fin n) → Prop} {X : ℝ}
    (h : HasAdjLabeling n F₂ X) (hF : ∀ G, F₁ G → F₂ G) : HasAdjLabeling n F₁ X := by
  obtain ⟨D, hD⟩ := h
  exact ⟨D, fun G hG => hD G (hF G hG)⟩

/-- **Theorem 3.** For `α > 2` there is `κ > 0` such that for all large `n`, any adjacency
labeling scheme for the `n`-vertex graphs of `P_α` (with any constant `C' ≥ C'₀ α`, so that
`P'_α ⊆ P_α` by Proposition 3) needs labels of `κ n^{1/α}` bits. -/
theorem theorem3 (hα : 2 < α) : ∃ κ > 0, ∀ᶠ n : ℕ in atTop, ∀ C' : ℝ, C'₀ α ≤ C' →
    ∀ X : ℝ, HasAdjLabeling n (IsPowerLaw α C') X → κ * (n : ℝ) ^ (1 / α) ≤ X := by
  obtain ⟨κ, hκ, hev⟩ := theorem3_proper hα
  refine ⟨κ, hκ, ?_⟩
  filter_upwards [hev] with n hn C' hC' X hX
  exact hn X (hX.mono fun G hG => prop3 (by linarith) hC' G hG)

/-- Non-vacuity: for `α > 2` and all large `n` there are `α`-proper power-law graphs on `n`
vertices. -/
theorem eventually_exists_isProperPowerLaw (hα : 2 < α) :
    ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n), IsProperPowerLaw α G := by
  filter_upwards [eventually_construct hα] with n ⟨hi3, hL, hB, _⟩
  obtain ⟨G, hG, _⟩ := construct hα hi3 hL hB ⊥
  exact ⟨G, hG⟩

/-- Non-vacuity of `P_α` (Definition 1), via Proposition 3. -/
theorem eventually_exists_isPowerLaw (hα : 2 < α) :
    ∀ᶠ n : ℕ in atTop, ∃ G : SimpleGraph (Fin n), IsPowerLaw α (C'₀ α) G := by
  filter_upwards [eventually_exists_isProperPowerLaw hα] with n ⟨G, hG⟩
  exact ⟨G, prop3 (by linarith) le_rfl G hG⟩

end Podc.PowerLawLabeling
