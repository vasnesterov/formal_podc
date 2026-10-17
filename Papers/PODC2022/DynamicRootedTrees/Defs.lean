import Cslib.Computability.Distributed.DynamicNetworks.Product
import Cslib.Foundations.Combinatorics.SimpleGraph.RootedTree
import Mathlib

/-!
# Broadcasting in dynamic rooted trees: the model

El-Hayek, Henzinger, Schmid, *Brief Announcement: Broadcasting Time in Dynamic Rooted Trees is
Linear*, PODC 2022 (full version: *Asymptotically Tight Bounds on the Time Complexity of Broadcast
and its Variants in Dynamic Networks*, arXiv:2211.10151, ITCS 2023).

Processes are `Fin n`. In every round `t = 1, 2, …` an adversary picks a rooted tree on `Fin n`,
to which a self-loop is added at every node (the set `𝒯ₙ`, `treesWithLoops n`). The product graph
`G₁ ∘ ⋯ ∘ Gₜ` (`Cslib.DynNet.prod G 1 t`) records who has heard of whom; the broadcast time is the first
round after which some process has reached everybody (`Cslib.DynNet.broadcastTime`), and `t*(𝒯ₙ)` is the
worst case over all adversarial sequences (`Cslib.DynNet.advBroadcastTime`).
-/

namespace DynamicRootedTrees

open Cslib.DynNet Relation

/-- A rooted (out-)tree on the vertex set `Fin n`: a root and a parent function such that every
vertex reaches the root by following parents. (The parent of the root is irrelevant.) -/
structure RootedTree (n : ℕ) where
  /-- The root. -/
  root : Fin n
  /-- The parent of each non-root vertex. -/
  parent : Fin n → Fin n
  /-- Following parents leads to the root (so the parent relation is acyclic). -/
  reach_root : ∀ v, ∃ k, parent^[k] v = root

namespace RootedTree

variable {n : ℕ} (T : RootedTree n)

/-- The communication graph of the tree with a self-loop at every node: `x → y` iff `x = y` or `x`
is the parent of the non-root vertex `y` (edges are directed away from the root). -/
def adj (x y : Fin n) : Prop := x = y ∨ (y ≠ T.root ∧ T.parent y = x)

theorem adj_refl (x : Fin n) : T.adj x x := Or.inl rfl

/-- Every vertex is reachable from the root along tree edges. -/
theorem isRoot : IsRoot T.adj T.root := by
  intro v
  obtain ⟨k, hk⟩ := T.reach_root v
  induction k generalizing v with
  | zero => simp only [Function.iterate_zero, id_eq] at hk; subst hk; exact ReflTransGen.refl
  | succ k ih =>
    rw [Function.iterate_succ_apply] at hk
    by_cases hv : v = T.root
    · subst hv; exact ReflTransGen.refl
    · exact (ih _ hk).tail (Or.inr ⟨hv, rfl⟩)

/-- Every rooted spanning tree of a graph on `Fin n` in the sense of CSLib
(`SimpleGraph.RootedTree`: parent pointers with depths) is a rooted tree in the above sense. Our
trees carry no graph and no depth function, since the adversary may pick any rooted tree. -/
def ofGraphRootedTree {G : SimpleGraph (Fin n)} (T : G.RootedTree) : RootedTree n :=
  ⟨T.root, T.parent, fun v => ⟨T.depth v, T.iterate_depth v⟩⟩

end RootedTree

/-- `𝒯ₙ`: the set of all rooted trees on `n` nodes with a self-loop added at every node
(Definition 1.2 of the full version). -/
def treesWithLoops (n : ℕ) : Set (Fin n → Fin n → Prop) := Set.range RootedTree.adj

theorem refl_of_mem_treesWithLoops {n : ℕ} {E : Fin n → Fin n → Prop}
    (h : E ∈ treesWithLoops n) (x : Fin n) : E x x := by
  obtain ⟨T, rfl⟩ := h; exact T.adj_refl x

theorem exists_root_of_mem_treesWithLoops {n : ℕ} {E : Fin n → Fin n → Prop}
    (h : E ∈ treesWithLoops n) : ∃ r, IsRoot E r := by
  obtain ⟨T, rfl⟩ := h; exact ⟨T.root, T.isRoot⟩

end DynamicRootedTrees
