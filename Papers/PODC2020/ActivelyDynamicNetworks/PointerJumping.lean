import Podc.Computability.Distributed.DynamicNetworks.ActivelyDynamic
import Podc.Foundations.Combinatorics.SimpleGraph.ParentGraph

/-!
# Pointer jumping as rounds of an actively dynamic network

Both basic subroutines of Michail–Skretas–Spirakis (PODC 2020, §2.3), TreeToStar and
LineToCompleteBinaryTree, have the same per-node rule: a node of the current rooted tree that
decides to move activates the edge to its grandparent (a potential neighbour) and deactivates the
edge to its parent. If the set of moving nodes is `S` (non-root children only), the new parent map
is `jump P S`.

* `jumpAct P S` / `jumpDeact P S`: the edges activated / deactivated by the moving nodes.
* `parentGraph_jump`: the snapshot after the round is `(E ∪ jumpAct) \ jumpDeact`, i.e. exactly
  the graph of the new parent map.
* `validRound_jump`: this is a valid round of the model (`Cslib.DynNet.Active.ValidRound`): every
  activated edge joins two potential neighbours (common neighbour: the old parent).
* `ncard_jumpAct_le`: at most `|S|` edges are activated.
-/

namespace Podc.ActivelyDynamicNetworks

open SimpleGraph Cslib.DynNet.Active

variable {V : Type*} {P : V → V} {r : V} {rk : V → ℕ} {S : V → Prop} [DecidablePred S]

/-- Edges activated by the moving nodes: each `u ∈ S` connects to its grandparent. -/
def jumpAct (P : V → V) (S : V → Prop) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => S u ∧ v = P (P u)

/-- Edges deactivated by the moving nodes: each `u ∈ S` drops the edge to its parent. -/
def jumpDeact (P : V → V) (S : V → Prop) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => S u ∧ v = P u

theorem parentGraph_jump (h : IsRootedMap P r rk) (hS : ∀ u, S u → P u ≠ r) :
    parentGraph (jump P S) = (parentGraph P ⊔ jumpAct P S) \ jumpDeact P S := by
  have key : ∀ u, S u → u ≠ r ∧ P u ≠ r ∧ P u ≠ u ∧ P (P u) ≠ u ∧ P (P u) ≠ P u ∧
      P (P (P u)) ≠ u := fun u hu =>
    have hu' := h.ne_root_of_map_ne_root (hS u hu)
    ⟨hu', hS u hu, h.map_ne_self hu', h.map_map_ne_self hu', h.map_ne_self (hS u hu),
      h.map_map_map_ne_self hu'⟩
  have key2 : ∀ u, u ≠ r → P u ≠ u ∧ P (P u) ≠ u := fun u hu =>
    ⟨h.map_ne_self hu, h.map_map_ne_self hu⟩
  ext x y
  simp only [parentGraph_adj, sdiff_adj, sup_adj, jumpAct, jumpDeact, fromRel_adj, jump]
  by_cases hx : S x <;> by_cases hy : S y <;> simp only [hx, hy, ite_true, ite_false]
  · obtain ⟨-, -, a1, a2, a3, a4⟩ := key x hx
    obtain ⟨-, -, b1, b2, b3, b4⟩ := key y hy
    grind
  · obtain ⟨-, -, a1, a2, a3, a4⟩ := key x hx
    by_cases hyr : y = r
    · subst hyr; grind [h.map_root]
    · obtain ⟨b1, b2⟩ := key2 y hyr
      grind
  · obtain ⟨-, -, b1, b2, b3, b4⟩ := key y hy
    by_cases hxr : x = r
    · subst hxr; grind [h.map_root]
    · obtain ⟨a1, a2⟩ := key2 x hxr
      grind
  · grind

theorem jumpAct_potentialNbr (h : IsRootedMap P r rk) (hS : ∀ u, S u → P u ≠ r) {u v : V}
    (huv : (jumpAct P S).Adj u v) : PotentialNbr (parentGraph P) u v := by
  have aux : ∀ u, S u → PotentialNbr (parentGraph P) u (P (P u)) := by
    intro u hu
    have hu' := h.ne_root_of_map_ne_root (hS u hu)
    have a1 := h.map_ne_self hu'
    have a2 := h.map_map_ne_self hu'
    have a3 := h.map_ne_self (hS u hu)
    have a4 := h.map_map_map_ne_self hu'
    refine ⟨a2.symm, ?_, P u, ?_, ?_⟩
    · rw [parentGraph_adj]; rintro ⟨-, h1 | h1⟩
      · exact a3 h1.symm
      · exact a4 h1
    · exact parentGraph_adj.2 ⟨a1.symm, Or.inl rfl⟩
    · exact parentGraph_adj.2 ⟨a3.symm, Or.inl rfl⟩
  have symm : ∀ {a b}, PotentialNbr (parentGraph P) a b → PotentialNbr (parentGraph P) b a := by
    rintro a b ⟨h1, h2, w, h3, h4⟩
    exact ⟨h1.symm, fun h5 => h2 h5.symm, w, h4.symm, h3.symm⟩
  rw [jumpAct, fromRel_adj] at huv
  rcases huv.2 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
  · exact aux u h1
  · exact symm (aux v h1)

theorem jumpDeact_le : jumpDeact P S ≤ parentGraph P := by
  intro u v huv
  rw [jumpDeact, fromRel_adj] at huv
  rw [parentGraph_adj]
  rcases huv with ⟨hne, ⟨-, rfl⟩ | ⟨-, rfl⟩⟩
  · exact ⟨hne, Or.inl rfl⟩
  · exact ⟨hne, Or.inr rfl⟩

/-- A jump round is a valid round of the actively dynamic model. -/
theorem validRound_jump (h : IsRootedMap P r rk) (hS : ∀ u, S u → P u ≠ r) :
    ValidRound (parentGraph P) (parentGraph (jump P S)) :=
  validRound_iff.2 ⟨jumpAct P S, jumpDeact P S, fun _ _ huv => jumpAct_potentialNbr h hS huv,
    jumpDeact_le, parentGraph_jump h hS⟩

/-- The edges activated in a jump round are among `jumpAct`. -/
theorem activated_le (h : IsRootedMap P r rk) (hS : ∀ u, S u → P u ≠ r) :
    parentGraph (jump P S) \ parentGraph P ≤ jumpAct P S := by
  rw [parentGraph_jump h hS]
  intro u v huv
  simp only [sdiff_adj, sup_adj] at huv
  tauto

/-- At most `|S|` edges are activated. -/
theorem ncard_jumpAct_le [Finite V] : (jumpAct P S).edgeSet.ncard ≤ {u | S u}.ncard := by
  have : (jumpAct P S).edgeSet ⊆ (fun u => s(u, P (P u))) '' {u | S u} := by
    intro e he
    induction e using Sym2.ind with
    | _ u v =>
      rw [mem_edgeSet, jumpAct, fromRel_adj] at he
      rcases he.2 with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
      · exact ⟨u, h1, rfl⟩
      · exact ⟨v, h1, Sym2.eq_swap⟩
  exact (Set.ncard_le_ncard this (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))

theorem numActivated_jump_le [Finite V] (h : IsRootedMap P r rk) (hS : ∀ u, S u → P u ≠ r) :
    (parentGraph (jump P S) \ parentGraph P).edgeSet.ncard ≤ {u | S u}.ncard :=
  (Set.ncard_le_ncard (edgeSet_mono (activated_le h hS)) (Set.toFinite _)).trans
    ncard_jumpAct_le

end Podc.ActivelyDynamicNetworks
