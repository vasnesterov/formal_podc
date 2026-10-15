import Cslib.Foundations.Combinatorics.SimpleGraph.RandomGreedyMIS
import Mathlib

/-!
# Optimal Dynamic Distributed MIS — definitions (Section 3)

Censor-Hillel, Haramaty, Karnin, *Optimal Dynamic Distributed MIS*, PODC 2016
(arXiv:1507.04330).

## Modelling

* A **configuration** is a graph `G` on a fixed finite vertex type `V` together with the set `A` of
  present nodes; the network is `G[A]`. Graphs that differ by one node are modelled by the same `G`
  and node sets `A`, `A ∪ {x}` (so `V` is the union of the node sets of `G_old` and `G_new`).
* The random order `π` is a rank function `r : V → ℕ` (later `r = orderRank π` for a uniformly
  random
  bijection `π : V ≃ Fin |V|`).
* The MIS maintained is the greedy MIS for the order (`SimpleGraph.greedyMIS`); this is exactly the
  paper's "MIS invariant".
* `Change` lists the four topology changes of Section 3; `Change.vStar` is the paper's `v*`
  (the later endpoint of the changed edge, or the changed node) and `Change.vStarStar` its `v**`.
* `Influenced G A r s x` is the paper's recursion (1) for the influenced sets `S_i`, read as the
  least set closed under the two rules (equivalently `⋃ S_i`, see `mem_layers_iff`), where `s` are
  the states (`M` = `s`, `M̄` = complement) *before* the change.
* `infl c cfg r` is the paper's `S(G_old, G_new, π)`: empty if the MIS invariant still holds at `v*`
  after the change, otherwise the closure from `v*` in `G_new` (in `G_old` for a node deletion).

We prove that `Influenced` coincides with the three-valued influenced set
`SimpleGraph.influenced` (`influenced_iff`), the key to the rigorous proof of Theorem 1.
-/

open Finset

namespace DynamicMIS

variable {V : Type*}

/-- A configuration of the dynamic network: a graph on `V` and the set of present nodes. -/
structure Config (V : Type*) where
  /-- The graph (only edges between present nodes matter). -/
  graph : SimpleGraph V
  /-- The present nodes. -/
  nodes : Set V

/-- The four topology changes of Section 3 (graceful/abrupt and insertion/unmuting variants only
differ in the distributed implementation, Section 4). -/
inductive Change (V : Type*)
  | insertEdge (a b : V)
  | deleteEdge (a b : V)
  | insertNode (x : V)
  | deleteNode (x : V)

namespace Change

/-- The configuration after the change. -/
def apply [DecidableEq V] : Change V → Config V → Config V
  | insertEdge a b, c => ⟨c.graph ⊔ SimpleGraph.edge a b, c.nodes⟩
  | deleteEdge a b, c => ⟨c.graph.deleteEdges {s(a, b)}, c.nodes⟩
  | insertNode x, c => ⟨c.graph, insert x c.nodes⟩
  | deleteNode x, c => ⟨c.graph, c.nodes \ {x}⟩

/-- The node `v*` at which the MIS invariant may break: the endpoint of the changed edge that comes
later in the order, or the changed node. -/
def vStar (r : V → ℕ) : Change V → V
  | insertEdge a b | deleteEdge a b => if r a < r b then b else a
  | insertNode x | deleteNode x => x

/-- The node `v**`: the other endpoint of the changed edge (`v*` itself for node changes). -/
def vStarStar (r : V → ℕ) : Change V → V
  | insertEdge a b | deleteEdge a b => if r a < r b then a else b
  | insertNode x | deleteNode x => x

end Change

/-- The MIS invariant at `v` for states `s` (`s` = the set of nodes in state `M`). -/
def InvariantAt (G : SimpleGraph V) (A : Set V) (r : V → ℕ) (s : Set V) (v : V) : Prop :=
  v ∈ s ↔ v ∈ A ∧ ∀ w, G.Adj w v → r w < r v → w ∉ s

/-- The influenced nodes of recursion (1) of the paper, as the least set containing `x` and closed
under: (a) a node in `M` with an earlier neighbour in the set; (b) a node in `M̄` all of whose
earlier `M`-neighbours are in the set. Here `s` is the set of nodes in state `M`. -/
inductive Influenced (G : SimpleGraph V) (A : Set V) (r : V → ℕ) (s : Set V) (x : V) : V → Prop
  | base : Influenced G A r s x x
  | inM {u w : V} : u ∈ A → u ∈ s → G.Adj w u → r w < r u → Influenced G A r s x w →
      Influenced G A r s x u
  | inMbar {u : V} : u ∈ A → u ∉ s →
      (∀ w, G.Adj w u → r w < r u → w ∈ s → Influenced G A r s x w) → Influenced G A r s x u

/-- The layers `S_i` of recursion (1), literally: `S_0 = {x}`,
`S_i = {u ∈ M | S_{i-1} ∩ I(u) ≠ ∅} ∪ {u ∈ M̄ | I(u) ∩ M ⊆ S_0 ∪ … ∪ S_{i-1}}`. -/
def layer (G : SimpleGraph V) (A : Set V) (r : V → ℕ) (s : Set V) (x : V) : ℕ → Set V
  | 0 => {x}
  | i + 1 => {u | u ∈ A ∧ u ∈ s ∧ ∃ w ∈ layer G A r s x i, G.Adj w u ∧ r w < r u} ∪
      {u | u ∈ A ∧ u ∉ s ∧ ∀ w, G.Adj w u → r w < r u → w ∈ s →
        ∃ j : Fin (i + 1), w ∈ layer G A r s x j}
decreasing_by all_goals omega

open Classical in
/-- The paper's set `S(G_old, G_new, π)` of influenced nodes: empty if the MIS invariant still
holds at `v*` right after the change (with the old states), otherwise the closure of recursion (1)
from `v*`, in `G_new` (in `G_old` for a node deletion; we use the union of the two node sets, which
only differs at `v*`). -/
def infl [DecidableEq V] (c : Change V) (cfg : Config V) (r : V → ℕ) : Set V :=
  let new := c.apply cfg
  let s := cfg.graph.greedyMIS cfg.nodes r
  if InvariantAt new.graph new.nodes r s (c.vStar r) then ∅
  else {u | Influenced new.graph (cfg.nodes ∪ new.nodes) r s (c.vStar r) u}

/-! ### The layers and the closure -/

section Layers

variable {G : SimpleGraph V} {A : Set V} {r : V → ℕ} {s : Set V} {x : V}

theorem mem_layer_zero {u : V} : u ∈ layer G A r s x 0 ↔ u = x := by
  rw [layer]; rfl

theorem mem_layer_succ {u : V} {i : ℕ} : u ∈ layer G A r s x (i + 1) ↔
    (u ∈ A ∧ u ∈ s ∧ ∃ w ∈ layer G A r s x i, G.Adj w u ∧ r w < r u) ∨
    (u ∈ A ∧ u ∉ s ∧ ∀ w, G.Adj w u → r w < r u → w ∈ s →
      ∃ j : Fin (i + 1), w ∈ layer G A r s x j) := by
  rw [layer]; rfl

/-- Nodes entering a layer by rule (b) stay in all later layers: with formula (1) taken literally,
the layers never become empty once such a node appears, so `i_u = max {i | u ∈ S_i}` is undefined
and the loop of Algorithm 1 ("until `S_i = ∅`") need not terminate. -/
theorem mem_layer_of_inMbar {u : V} {i : ℕ}
    (hu : u ∈ A ∧ u ∉ s ∧ ∀ w, G.Adj w u → r w < r u → w ∈ s →
      ∃ j : Fin (i + 1), w ∈ layer G A r s x j) {k : ℕ} (hk : i ≤ k) :
    u ∈ layer G A r s x (k + 1) := by
  refine mem_layer_succ.2 (Or.inr ⟨hu.1, hu.2.1, fun w hw hr hws => ?_⟩)
  obtain ⟨j, hjw⟩ := hu.2.2 w hw hr hws
  exact ⟨⟨j, by omega⟩, hjw⟩

/-- `⋃ S_i` is the closure `Influenced`. -/
theorem mem_layers_iff [Fintype V] {u : V} :
    (∃ i, u ∈ layer G A r s x i) ↔ Influenced G A r s x u := by
  constructor
  · rintro ⟨i, hi⟩
    induction i using Nat.strong_induction_on generalizing u with
    | _ i ih =>
    cases i with
    | zero => rw [mem_layer_zero.1 hi]; exact .base
    | succ i =>
      rcases mem_layer_succ.1 hi with ⟨huA, hus, w, hw, hwu, hr⟩ | ⟨huA, hus, h⟩
      · exact .inM huA hus hwu hr (ih i (Nat.lt_succ_self i) hw)
      · refine .inMbar huA hus fun w hwu hr hws => ?_
        obtain ⟨j, hjw⟩ := h w hwu hr hws
        exact ih j j.isLt hjw
  · intro h
    induction h with
    | base => exact ⟨0, mem_layer_zero.2 rfl⟩
    | @inM u w huA hus hwu hr _ ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i + 1, mem_layer_succ.2 (Or.inl ⟨huA, hus, w, hi, hwu, hr⟩)⟩
    | @inMbar u huA hus _ ih =>
      have : ∀ w, ∃ j, G.Adj w u → r w < r u → w ∈ s → w ∈ layer G A r s x j := by
        intro w
        by_cases hw : G.Adj w u ∧ r w < r u ∧ w ∈ s
        · obtain ⟨j, hj⟩ := ih w hw.1 hw.2.1 hw.2.2
          exact ⟨j, fun _ _ _ => hj⟩
        · exact ⟨0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ hw⟩
      choose f hf using this
      refine ⟨univ.sup f + 1, mem_layer_succ.2 (Or.inr ⟨huA, hus, fun w hwu hr hws =>
        ⟨⟨f w, Nat.lt_succ_of_le (le_sup (mem_univ w))⟩, hf w hwu hr hws⟩⟩)⟩

end Layers

/-! ### The closure is the three-valued influenced set -/

section Closure

open SimpleGraph

variable {G : SimpleGraph V} {A : Set V} {r : V → ℕ} {s : Set V} {x : V}

/-- For states `s` satisfying the MIS invariant at all nodes other than `x`, the closure of
recursion (1) from `x` is exactly the set of nodes whose greedy state is undetermined when the
state of `x` is unknown. In particular it does not depend on `s`. -/
theorem influenced_iff (hs : G.IsGreedyExcept A r x s) {u : V} :
    Influenced G A r s x u ↔ u ∈ G.influenced A r x := by
  constructor
  · intro h
    induction h with
    | base => exact self_mem_influenced x
    | @inM u w huA hus hwu hr _ ih =>
      change G.partialGreedy A r x u = none
      rcases hval : G.partialGreedy A r x u with _ | b
      · rfl
      · exfalso
        have hb := (mem_iff_of_partialGreedy_eq_some hs u b hval).1 hus
        subst hb
        obtain ⟨-, -, hpred⟩ := partialGreedy_eq_some_true_iff.1 hval
        have := hpred w hwu hr
        change G.partialGreedy A r x w = none at ih
        rw [ih] at this; cases this
    | @inMbar u huA hus _ ih =>
      change G.partialGreedy A r x u = none
      rcases hval : G.partialGreedy A r x u with _ | b
      · rfl
      · exfalso
        cases b with
        | true => exact hus ((mem_iff_of_partialGreedy_eq_some hs u true hval).2 rfl)
        | false =>
          obtain ⟨-, h | ⟨w, hwu, hr, hwt⟩⟩ := partialGreedy_eq_some_false_iff.1 hval
          · exact h huA
          · have hws := (mem_iff_of_partialGreedy_eq_some hs w true hwt).2 rfl
            have := ih w hwu hr hws
            change G.partialGreedy A r x w = none at this
            rw [this] at hwt; cases hwt
  · intro h
    induction u using rank_induction r with
    | h u ih =>
    rcases partialGreedy_eq_none_iff.1 h with rfl | ⟨huA, hnt, w, hwu, hr, hwn⟩
    · exact .base
    by_cases hus : u ∈ s
    · exact .inM huA hus hwu hr (ih w hr hwn)
    · refine .inMbar huA hus fun z hzu hz hzs => ih z hz ?_
      change G.partialGreedy A r x z = none
      rcases hval : G.partialGreedy A r x z with _ | b
      · rfl
      · cases b with
        | true => exact absurd hval (hnt z hzu hz)
        | false =>
          exact absurd ((mem_iff_of_partialGreedy_eq_some hs z false hval).1 hzs) (by simp)

end Closure

end DynamicMIS
