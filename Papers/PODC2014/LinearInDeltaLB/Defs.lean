import Cslib.Computability.Distributed.ColourSystem.Graph
import Cslib.Computability.Distributed.Local.Locality
import Mathlib

/-!
# Linear-in-Δ lower bounds in the LOCAL model: definitions

Definitions shared by the whole formalization of
[M. Göös, J. Hirvonen, J. Suomela, *Linear-in-Δ lower bounds in the LOCAL model*, PODC 2014]
(arXiv:1304.1007).

## Maximal fractional matchings in the EC model (Sections 3.3–3.5)

An *EC-graph* is a `ColouredGraph k α` (CSLib): every node has at most one incident edge of each
colour `c : Fin k`; half-loops (`step a c = some a`) are the paper's loops, contributing `+1` to the
degree. An *EC-algorithm* is a function of the view (universal cover, a colour system
`⊆ FreeCox k`), returning one weight per incident colour (`ECAlg`). Defining the algorithm on views
builds in the invariance under lifts (equation (2) of the paper). Run-time `t` (`ECAlg.HasRunTime`)
means that the output only depends on the radius-`t` ball of the view, which is the paper's
`τ_t` (nodes at distance `≤ t`; an edge `{u, w}` is at distance `min (d u) (d w) + 1`).

Outputs on a multigraph are interpreted through the universal cover, so a loop of colour `c` at
`a` is a single edge whose weight is `A (view a) c`; the fractional-matching constraints
(`IsMaxFM`) count it once, as in Section 3.5.

## Maximal fractional matchings in the ID model (Sections 1.4, 3.1–3.2)

An *ID-graph* is a `SimpleGraph ℕ` with finitely many edges (identifiers are the node names; nodes
not incident to an edge are isolated nodes and play no role). An ID-algorithm `A : IDAlg` maps a
graph `G`, a node `v` and a neighbour `u` to the weight that `v` outputs for the edge `{v, u}`.
Run-time `t` (`IDAlg.HasRunTime`) is CSLib's `GAgree`: the output of `v` only depends on the edges
incident to nodes at distance `< t` from `v` (this is again `τ_t`, with identifiers).
-/

namespace Podc.LinearInDeltaLB

open Cslib.ColourSystem

/-! ### The EC model -/

section EC

variable {k : ℕ} {α : Type*}

/-- An EC-algorithm: the weight that the root of a view assigns to its incident edge of each
colour. Only the colours present at the root matter. -/
abbrev ECAlg (k : ℕ) := Set (FreeCox k) → Fin k → ℝ

/-- `A` has run-time `t`: its output only depends on the radius-`t` ball of the view. -/
def ECAlg.HasRunTime (A : ECAlg k) (t : ℕ) : Prop :=
  ∀ U V : Set (FreeCox k), ball U t = ball V t → A U = A V

open Classical in
/-- `y[a]`: the total weight of the edges incident to `a` (a loop counts once). -/
noncomputable def load (G : ColouredGraph k α) (y : α → Fin k → ℝ) (a : α) : ℝ :=
  ∑ c ∈ Finset.univ.filter (fun c => (G.step a c).isSome), y a c

/-- `y` (given as the weight `y a c` that node `a` assigns to its incident `c`-edge) is a maximal
fractional matching of the multigraph `G`: both endpoints agree on the weight of every edge,
weights are nonnegative, every node has load `≤ 1`, and every edge has a saturated endpoint. -/
structure IsMaxFM (G : ColouredGraph k α) (y : α → Fin k → ℝ) : Prop where
  symm : ∀ a b c, G.step a c = some b → y a c = y b c
  nonneg : ∀ a c, (G.step a c).isSome → 0 ≤ y a c
  le_one : ∀ a, load G y a ≤ 1
  maximal : ∀ a b c, G.step a c = some b → load G y a = 1 ∨ load G y b = 1

/-- `G` is loopy: every node carries a loop (a half-loop of some colour). This is a sufficient
condition for the paper's Definition 1 (every node of the factor graph has a loop). -/
def IsLoopy (G : ColouredGraph k α) : Prop := ∀ a, ∃ c, G.step a c = some a

/-- `A` finds a maximal fractional matching on every finite loopy EC-graph (with `k` colours,
hence of maximum degree `≤ k`). -/
def ECAlg.SolvesLoopy (A : ECAlg k) : Prop :=
  ∀ (α : Type) [Finite α] (G : ColouredGraph k α), IsLoopy G →
    IsMaxFM G (fun a => A (G.view a))

end EC

/-! ### The ID model -/

section ID

/-- A deterministic algorithm in the ID model: `A G v u` is the weight that node `v` of the
ID-graph `G` outputs for its incident edge `{v, u}`. -/
abbrev IDAlg := SimpleGraph ℕ → ℕ → ℕ → ℝ

/-- `A` has run-time `t`: the output of `v` only depends on the radius-`t` neighbourhood `τ_t`
(edges incident to nodes at distance `< t` from `v`). -/
def IDAlg.HasRunTime (A : IDAlg) (t : ℕ) : Prop :=
  ∀ (G G' : SimpleGraph ℕ) (v : ℕ), Cslib.Local.GAgree G G' v t → A G v = A G' v

/-- `y` is a maximal fractional matching of the simple graph `G` (`y u v` is the weight of the edge
`{u, v}` as output by `u`). -/
structure IsMaxFMGraph (G : SimpleGraph ℕ) (y : ℕ → ℕ → ℝ) : Prop where
  symm : ∀ u v, G.Adj u v → y u v = y v u
  nonneg : ∀ u v, G.Adj u v → 0 ≤ y u v
  le_one : ∀ u, ∑ᶠ v ∈ G.neighborSet u, y u v ≤ 1
  maximal : ∀ u v, G.Adj u v →
    ∑ᶠ w ∈ G.neighborSet u, y u w = 1 ∨ ∑ᶠ w ∈ G.neighborSet v, y v w = 1

/-- `A` finds a maximal fractional matching on every finite ID-graph of maximum degree `≤ Δ`. -/
def IDAlg.Solves (A : IDAlg) (Δ : ℕ) : Prop :=
  ∀ G : SimpleGraph ℕ, G.edgeSet.Finite → (∀ v, (G.neighborSet v).ncard ≤ Δ) →
    IsMaxFMGraph G (A G)

end ID

end Podc.LinearInDeltaLB
