import Cslib.Foundations.Combinatorics.SimpleGraph.WeightedSpanner
import Mathlib

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/Emulator.lean

/-!
# Near-additive emulators

An `(α, β)`-*emulator* of an unweighted graph `G = (V, E)` is a weighted graph `H` on (a superset
of) `V` with `d_G(u, v) ≤ d_H(u, v) ≤ α · d_G(u, v) + β` for all `u, v ∈ V`. Here `H` lives on the
same vertex type `V` (no Steiner vertices), and its weights are given by `w : Sym2 V → ℝ≥0`
(CSLib's `wdist`). Distances are extended: `d_G(u, v) = ⊤` for disconnected `u, v`.

Most emulator constructions weigh an emulator edge `{x, y}` by `d_G(x, y)`; this is `distW G`.

## Main definitions and results

* `SimpleGraph.distW G` — the weight `{x, y} ↦ d_G(x, y)`.
* `SimpleGraph.IsEmulator G H w α β` — `(H, w)` is an `(α, β)`-emulator of `G`.
* `SimpleGraph.edist_le_wdist_distW` — with weights `distW G`, `d_G ≤ d_H` holds as soon as every
  edge of `H` joins two vertices that are connected in `G` (triangle inequality).
* `SimpleGraph.wdist_distW_le_of_adj` — an emulator edge `{x, y}` gives `d_H(x, y) ≤ d_G(x, y)`.
-/

open scoped ENNReal NNReal

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- The edge weight `{x, y} ↦ d_G(x, y)` (the usual weight of emulator edges). -/
noncomputable def distW : Sym2 V → ℝ≥0 :=
  Sym2.lift ⟨fun x y => (G.dist x y : ℝ≥0), fun x y => by simp only [dist_comm]⟩

@[simp] lemma distW_mk (x y : V) : G.distW s(x, y) = (G.dist x y : ℝ≥0) := rfl

/-- `(H, w)` is an `(α, β)`-*emulator* of the unweighted graph `G`: for all `u, v`,
`d_G(u, v) ≤ d_H(u, v) ≤ α · d_G(u, v) + β` (with `d = ⊤` between disconnected vertices). -/
def IsEmulator (H : SimpleGraph V) (w : Sym2 V → ℝ≥0) (α β : ℝ) : Prop :=
  ∀ u v, (G.edist u v : ℝ≥0∞) ≤ H.wdist w u v ∧
    H.wdist w u v ≤ ENNReal.ofReal α * (G.edist u v : ℝ≥0∞) + ENNReal.ofReal β

variable {G}

/-- An edge `{x, y}` of `H` gives `d_H(x, y) ≤ d_G(x, y)` for the weights `distW G`. -/
lemma wdist_distW_le_of_adj {H : SimpleGraph V} {x y : V} (h : H.Adj x y) :
    H.wdist G.distW x y ≤ (G.dist x y : ℝ≥0∞) := by
  simpa using wdist_le_of_adj (w := G.distW) h

/-- **Lower bound of emulators.** If every edge of `H` joins two vertices connected in `G`, then
with the weights `distW G` we have `d_G(u, v) ≤ d_H(u, v)` for all `u, v`. -/
theorem edist_le_wdist_distW {H : SimpleGraph V} (hH : ∀ x y, H.Adj x y → G.Reachable x y)
    (u v : V) : (G.edist u v : ℝ≥0∞) ≤ H.wdist G.distW u v := by
  refine le_iInf fun p => ?_
  induction p with
  | nil => simp
  | @cons a b c hab q ih =>
    rw [Walk.wlength_cons]
    have h1 : G.edist a b = (G.dist a b : ℕ∞) := ((hH a b hab).coe_dist_eq_edist).symm
    calc (G.edist a c : ℝ≥0∞) ≤ (G.edist a b : ℝ≥0∞) + (G.edist b c : ℝ≥0∞) := by
          rw [← ENat.toENNReal_add]; exact ENat.toENNReal_le.mpr G.edist_triangle
      _ ≤ _ := by
          gcongr
          rw [h1, distW_mk]; simp

/-- Emulators are monotone in the stretch parameters. -/
lemma IsEmulator.mono {H : SimpleGraph V} {w : Sym2 V → ℝ≥0} {α β α' β' : ℝ}
    (h : G.IsEmulator H w α β) (hα : α ≤ α') (hβ : β ≤ β') : G.IsEmulator H w α' β' :=
  fun u v => ⟨(h u v).1, (h u v).2.trans (add_le_add
    (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal hα) bot_le)
    (ENNReal.ofReal_le_ofReal hβ))⟩

end SimpleGraph
