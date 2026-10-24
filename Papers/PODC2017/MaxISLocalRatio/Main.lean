import Papers.PODC2017.MaxISLocalRatio.Matching
import Papers.PODC2017.MaxISLocalRatio.Layers
import Papers.PODC2017.MaxISLocalRatio.LiteralLine11

/-!
# Main results of Section 2 (summary and non-vacuity)

Bar-Yehuda, Censor-Hillel, Ghaffari, Schwartzman, *Distributed Approximation of Maximum Independent
Set and Maximum Matching*, PODC 2017.

| Paper | Lean |
|---|---|
| Theorem 2.1 | `theorem_2_1`, `isApprox_add` |
| Lemma 2.2 | `lemma_2_2`, `lemma_2_2_total`, `localBound_of_degree_le` |
| Algorithm 1 (`Δ`-approx., any choice of `U`) | `seqLR`, `algorithm_1`, `seqLR_isApprox` |
| Lemma A.1 / Thm 2.3, deterministic part | `top_layer_drops`, `removal_stage` |
| Algorithm 3 / Section 2.3 | `alg3`, `algorithm_3` |
| Section 2.4 (bound `2` in `L(G)`) | `matching_localBound`, `seqLR_lineGraph_isApprox` |
| Theorem 2.10, deterministic half | `theorem_2_10_det`, `lineGraph_degree_le` |
| Line 11 of Algorithm 1 taken literally | `LiteralLine11.literal_line_11_fails` |
-/

set_option linter.unusedSectionVars false

namespace Podc.MaxISLocalRatio

open Cslib.LocallyIterative

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Non-vacuity of the colouring hypothesis of `algorithm_3`: every finite graph has a proper
colouring with `|V|` colours (a numbering of the vertices). -/
theorem exists_proper_coloring (G : SimpleGraph V) :
    ∃ c : V → ℕ, IsProper G c ∧ ∀ v, c v < Fintype.card V :=
  ⟨fun v => Fintype.equivFin V v,
    fun _ _ h e => G.ne_of_adj h ((Fintype.equivFin V).injective (Fin.ext e)),
    fun v => (Fintype.equivFin V v).isLt⟩

/-- Non-vacuity: `algorithm_3` applies to every finite graph with a degree bound `Δ ≥ 1`
and all real weights. -/
example (G : SimpleGraph V) [DecidableRel G.Adj] {Δ : ℕ} (hΔ : ∀ v, G.degree v ≤ Δ)
    (h1 : 1 ≤ Δ) (w : V → ℝ) : ∃ (c : V → ℕ) (S : Finset V), IsApprox G Δ w S ∧
      ∀ t, 3 * Fintype.card V ≤ t → ∀ v, output (cfg3 G c w t v) = some (decide (v ∈ S)) := by
  obtain ⟨c, hc, hk⟩ := exists_proper_coloring G
  obtain ⟨S, hS, ht, -⟩ := algorithm_3 hc hk hΔ h1 w
  exact ⟨c, S, hS, ht⟩

/-- Non-vacuity of `removal_stage`: the rule picking a maximal independent set of the top layer
satisfies its hypothesis. -/
example (G : SimpleGraph V) [DecidableRel G.Adj] (w : V → ℝ) (hint : ∀ v, ∃ n : ℤ, w v = n)
    {W : ℕ} (hW : ∀ v, w v ≤ W) : pos ((topMISRule G).iter w (Nat.clog 2 W + 1)) = ∅ :=
  removal_stage (topMISRule_isTopMIS G) hint hW

end Podc.MaxISLocalRatio
