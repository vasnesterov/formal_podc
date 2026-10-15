import Mathlib

/-!
# List defective colouring: basic definitions

Fuchs, Kuhn. *Simpler and More General Distributed Coloring Based on Simple List Defective
Coloring Algorithms* (PODC 2024, brief announcement; full version arXiv:2405.04648). Cited as
[FK24].

We fix a vertex type `V` and a colour type `α` (the paper takes colours from `ℕ`).

* `ListInstance V α`: a colour list `L v` and a defect function `d v : α → ℕ` for every node
  (Section 1, "List Defective Coloring"). Only the values of `d v` on `L v` matter.
* `ListInstance.weight I v = ∑_{x ∈ L_v} (d_v(x) + 1)`: the quantity that all slack conditions of
  the paper bound from below.
* `beta out v = max 1 |out v|`: the paper's `β_v` (Section 2: "we define `β_v` as the maximum of
  `1` and the outdegree of `v`").
* `IsOLDC I out col`: `col` solves the *oriented* list defective colouring instance `I` with
  out-neighbourhoods `out` (every node `v` gets `col v ∈ L v` and at most `d_v(col v)`
  out-neighbours of the same colour).
* `IsListDefective G I col`: list defective colouring of the graph `G` (all neighbours count).
* `IsListArbdefective G I col O`: list arbdefective colouring, i.e. a colouring together with an
  orientation `O` of the monochromatic edges such that `v` has at most `d_v(col v)` out-neighbours
  (w.r.t. `O`) of its own colour.
* `HasSlack G I S` (Definition 1.1): `∑_{x ∈ L_v} (d_v(x) + 1) > S · deg(v)` for all `v`.

Out-neighbourhoods are given as an arbitrary function `out : V → Finset V`; the paper's
"edge orientation" is the special case where `out` comes from orienting every edge of `G` in one
direction. All results of Section 3 hold for arbitrary `out` (in particular for `out v = N(v)`,
which turns oriented list defective colouring into list defective colouring).
-/

open Finset

namespace FK24

variable {V α : Type*}

/-- A list (defective) colouring instance: every node `v` has a colour list `L v` and a defect
function `d v` (the paper's `d_v : L_v → ℕ₀`, extended arbitrarily outside `L_v`). -/
structure ListInstance (V α : Type*) where
  /-- The colour list of a node. -/
  L : V → Finset α
  /-- The allowed defect of each colour. -/
  d : V → α → ℕ

namespace ListInstance

/-- `∑_{x ∈ L_v} (d_v(x) + 1)`. -/
def weight (I : ListInstance V α) (v : V) : ℕ := ∑ x ∈ I.L v, (I.d v x + 1)

end ListInstance

/-- The paper's `β_v`: the maximum of `1` and the outdegree of `v` (Section 2). -/
def beta (out : V → Finset V) (v : V) : ℕ := max 1 (out v).card

theorem card_out_le_beta (out : V → Finset V) (v : V) : (out v).card ≤ beta out v :=
  le_max_right _ _

theorem one_le_beta (out : V → Finset V) (v : V) : 1 ≤ beta out v := le_max_left _ _

/-- `col` solves the oriented list defective colouring (OLDC) instance `I` with out-neighbourhoods
`out`: every node `v` picks a colour from `L v` and has at most `d_v(col v)` out-neighbours with
the same colour. -/
def IsOLDC [DecidableEq α] (I : ListInstance V α) (out : V → Finset V) (col : V → α) : Prop :=
  ∀ v, col v ∈ I.L v ∧ #{u ∈ out v | col u = col v} ≤ I.d v (col v)

section Graph

variable (G : SimpleGraph V) [G.LocallyFinite]

/-- `col` is a list defective colouring of `G` for the instance `I`: every node `v` picks a colour
from `L v` and has at most `d_v(col v)` neighbours of the same colour. -/
def IsListDefective [DecidableEq α] (I : ListInstance V α) (col : V → α) : Prop :=
  ∀ v, col v ∈ I.L v ∧ #{u ∈ G.neighborFinset v | col u = col v} ≤ I.d v (col v)

open Classical in
/-- `(col, O)` is a list arbdefective colouring of `G` for the instance `I`: every node picks a
colour from its list, every monochromatic edge is oriented by `O` (in at least one direction), and
every node `v` has at most `d_v(col v)` out-neighbours (w.r.t. `O`) of its own colour. -/
def IsListArbdefective (I : ListInstance V α) (col : V → α) (O : V → V → Prop) : Prop :=
  (∀ v, col v ∈ I.L v) ∧ (∀ ⦃u v⦄, G.Adj u v → col u = col v → O u v ∨ O v u) ∧
    ∀ v, #{u ∈ G.neighborFinset v | O v u ∧ col u = col v} ≤ I.d v (col v)

/-- Definition 1.1 (slack): the instance `I` has slack `S` on `G` if
`∑_{x ∈ L_v} (d_v(x) + 1) > S · deg(v)` for every node `v`. -/
def HasSlack (I : ListInstance V α) (S : ℝ) : Prop :=
  ∀ v, S * (G.degree v : ℝ) < (I.weight v : ℝ)

end Graph

end FK24
