import Mathlib
import Podc.Digraph.Walk

/-!
# Atomic cross-chain swaps (Herlihy, PODC 2018): digraph vocabulary

Swap digraphs are Mathlib `Digraph`s (arcs `D.Adj u v`: a proposed transfer from `u` to `v`).
This file fixes the paper's §2.1 notions: paths (in the paper's lax sense), reachability,
strong connectivity, feedback vertex sets and the "diameter" (length of a longest path).
Reachability, strong connectivity and the follower subgraph are the shared notions
`Digraph.Reachable`, `Digraph.StronglyConnected` and `Digraph.deleteVerts` of
`Podc.Digraph.Walk`.
-/

namespace AtomicSwap

variable {V : Type*}

/-- A *path* in the sense of §2.1 of the paper: a nonempty vertex sequence `(u₀, …, u_ℓ)` along
arcs such that `u₀, …, u_{ℓ-1}` are distinct. The last vertex may repeat an earlier one (so cycles
`u₀ = u_ℓ`, and also "lassos", are paths). Its length is `ℓ = p.length - 1`. -/
def IsPath (D : Digraph V) (p : List V) : Prop :=
  p ≠ [] ∧ p.IsChain D.Adj ∧ p.dropLast.Nodup

instance [DecidableEq V] (D : Digraph V) [DecidableRel D.Adj] : DecidablePred (IsPath D) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- Reachability (`v` is reachable from `u` by a directed walk, possibly empty). -/
abbrev Reach (D : Digraph V) (u v : V) : Prop := D.Reachable u v

/-- `D` is strongly connected: every vertex is reachable from every vertex. -/
abbrev StronglyConnected (D : Digraph V) : Prop := D.StronglyConnected

/-- `D` is (weakly) connected: its underlying undirected graph is connected. -/
def WeaklyConnected (D : Digraph V) : Prop :=
  ∀ u v, Relation.ReflTransGen (fun a b => D.Adj a b ∨ D.Adj b a) u v

/-- The arcs among followers (vertices outside `L`): `FollowerAdj D L a b ↔ D.Adj a b ∧ a ∉ L ∧
b ∉ L`. -/
abbrev FollowerAdj (D : Digraph V) (L : Set V) : V → V → Prop := (D.deleteVerts L).Adj

/-- `L` is a *feedback vertex set*: deleting `L` leaves `D` acyclic, i.e. there is no closed
walk (of positive length) among the vertices outside `L`. -/
def IsFVS (D : Digraph V) (L : Set V) : Prop :=
  ∀ v, ¬ Relation.TransGen (FollowerAdj D L) v v

/-- The paper's `diam(D)`: the length of a longest path (§2.1). We take the supremum over all
paths in the paper's sense, including cycles; this is the reading under which the paper's own
three-party example has `diam = 3` (timeouts `6Δ, 5Δ, 4Δ` = `(diam + D(v, v̂) + 1)Δ`). -/
noncomputable def diam (D : Digraph V) : ℕ :=
  sSup {n | ∃ p, IsPath D p ∧ p.length = n + 1}

lemma IsPath.length_le [Fintype V] {D : Digraph V} {p : List V} (hp : IsPath D p) :
    p.length ≤ Fintype.card V + 1 := by
  have h1 := hp.2.2.length_le_card
  rw [List.length_dropLast] at h1
  omega

lemma diam_set_bdd [Fintype V] (D : Digraph V) :
    BddAbove {n | ∃ p, IsPath D p ∧ p.length = n + 1} :=
  ⟨Fintype.card V, fun n ⟨p, hp, hl⟩ => by have := hp.length_le; omega⟩

lemma le_diam [Fintype V] {D : Digraph V} {p : List V} (hp : IsPath D p) :
    p.length - 1 ≤ diam D := by
  apply le_csSup (diam_set_bdd D)
  refine ⟨p, hp, ?_⟩
  have : p ≠ [] := hp.1
  have : 0 < p.length := List.length_pos_iff.mpr this
  omega

lemma diam_le [Fintype V] {D : Digraph V} {n : ℕ}
    (h : ∀ p, IsPath D p → p.length ≤ n + 1) : diam D ≤ n := by
  by_cases hne : ({n | ∃ p, IsPath D p ∧ p.length = n + 1} : Set ℕ).Nonempty
  · apply csSup_le hne
    rintro m ⟨p, hp, hl⟩
    have := h p hp; omega
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    simp [diam, hne]

lemma diam_eq [Fintype V] {D : Digraph V} {n : ℕ} {p : List V} (hp : IsPath D p)
    (hl : p.length = n + 1) (h : ∀ p, IsPath D p → p.length ≤ n + 1) : diam D = n :=
  le_antisymm (diam_le h) (by have := le_diam hp; omega)

end AtomicSwap
