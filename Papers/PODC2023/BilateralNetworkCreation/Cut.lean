import Papers.PODC2023.BilateralNetworkCreation.Removal
import Cslib.Foundations.Combinatorics.SimpleGraph.ShortestWalks

/-!
# Distances after adding or swapping one edge (lower bounds)

* `d_add_ge`: after adding the edge `uv`, `dist'(u, x) ≥ min(dist(u, x), 1 + dist(v, x))`.
* `d_swap_ge`: let `A` be a vertex set such that the only edge of `G` leaving `A` is `a₀b₀`
  (`a₀ ∈ A`). In `G' = G - a₀b₀ + a₁b₁` (`a₁ ∈ A`, `b₁ ∉ A`) the distance from `a₁` to `y` is at
  least `dist(a₁, y)` for `y ∈ A` and at least `1 + dist(b₁, y)` for `y ∉ A`.
* `not_reachable_cut`: if both endpoints of the new edge lie in `A`, then `A` is cut off.

These are the only facts about the modified graphs used in the analysis of swaps and additions in
trees.
-/

-- CSLib candidate (the whole file is general graph theory)
namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {M : ℕ}

lemma dist_lt_card' [Nonempty V] (u v : V) : G.dist u v < Fintype.card V := by
  by_cases h : G.Reachable u v
  · exact dist_lt_card h
  · rw [dist_eq_zero_of_not_reachable h]; exact Fintype.card_pos

/-- A walk of `G'` that avoids the edge `e` and whose other edges lie in `G`, read in `G`. -/
lemma dist_le_of_walk_avoid {G' : SimpleGraph V} {a b x y : V} (hG' : ∀ e ∈ G'.edgeSet,
    e ≠ s(a, b) → e ∈ G.edgeSet) (Q : G'.Walk x y) (hQ : s(a, b) ∉ Q.edges) :
    G.dist x y ≤ Q.length := by
  have : ∀ e ∈ Q.edges, e ∈ G.edgeSet := fun e he =>
    hG' e (Q.edges_subset_edgeSet he) (fun h => hQ (h ▸ he))
  have := dist_le (Q.transfer G this)
  rwa [Walk.length_transfer] at this

lemma edgeSet_add_sub {a b : V} : ∀ e ∈ (G ⊔ edge a b).edgeSet, e ≠ s(a, b) → e ∈ G.edgeSet := by
  intro e he hne
  induction e using Sym2.ind with
  | _ x y =>
    rw [mem_edgeSet, sup_adj, edge_adj] at he
    rcases he with h | ⟨h, -⟩
    · exact h
    · exfalso; apply hne
      rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap

lemma edgeSet_swap_sub {a₀ b₀ a b : V} :
    ∀ e ∈ (G.deleteEdges {s(a₀, b₀)} ⊔ edge a b).edgeSet, e ≠ s(a, b) → e ∈ G.edgeSet := by
  intro e he hne
  have := edgeSet_add_sub (G := G.deleteEdges {s(a₀, b₀)}) e he hne
  exact (deleteEdges_le _) |> fun h => edgeSet_mono h this

/-- In a path from `u`, an edge `uc` must be the first edge. -/
lemma first_edge_eq {u c x : V} {G' : SimpleGraph V} (h : G'.Adj u c) (Q : G'.Walk c x)
    (hQ : (Walk.cons h Q).IsPath) {b : V} (hb : s(u, b) ∈ (Walk.cons h Q).edges) : b = c :=
  isPath_eq_of_mem_edges_start hQ hb (by simp)

/-- Distances after adding an edge `uv`, seen from `u`. -/
theorem d_add_ge [DecidableEq V] (hM : Fintype.card V ≤ M) (u v x : V) :
    min (G.dist u x) (1 + G.dist v x) ≤ d M (G ⊔ edge u v) u x := by
  haveI : Nonempty V := ⟨u⟩
  by_cases hr : (G ⊔ edge u v).Reachable u x
  · rw [d_of_reachable hr]
    obtain ⟨Q, hQ, hl⟩ := hr.exists_path_of_dist
    rw [← hl]
    by_cases he : s(u, v) ∈ Q.edges
    · cases Q with
      | nil => simp at he
      | @cons _ c _ h Q2 =>
        have hc := first_edge_eq h Q2 hQ he
        subst hc
        have hu : u ∉ Q2.support := (Walk.cons_isPath_iff h Q2).1 hQ |>.2
        have hQ2 : s(u, v) ∉ Q2.edges := fun h' => hu (Walk.fst_mem_support_of_mem_edges _ h')
        have := dist_le_of_walk_avoid edgeSet_add_sub Q2 hQ2
        simp only [Walk.length_cons]; omega
    · have := dist_le_of_walk_avoid edgeSet_add_sub Q he
      omega
  · rw [d_of_not_reachable hr]
    have := dist_lt_card' (G := G) v x
    omega

variable [DecidableEq V] {A : Finset V} {a₀ b₀ a₁ b₁ : V}

/-- The crossing edges of the swapped graph. -/
lemma swap_cross (hcut : ∀ x y, G.Adj x y → x ∈ A → y ∉ A → x = a₀ ∧ y = b₀) (hb₁ : b₁ ∉ A)
    {x y : V} (h : (G.deleteEdges {s(a₀, b₀)} ⊔ edge a₁ b₁).Adj x y) (hx : x ∈ A) (hy : y ∉ A) :
    x = a₁ ∧ y = b₁ := by
  rw [sup_adj, deleteEdges_adj, edge_adj] at h
  rcases h with ⟨h, hne⟩ | ⟨h, -⟩
  · obtain ⟨rfl, rfl⟩ := hcut x y h hx hy; simp at hne
  · rcases h with h | ⟨rfl, rfl⟩
    · exact h
    · exact absurd hx hb₁

/-- Distances in `G - a₀b₀ + a₁b₁` from `a₁`, when `a₀b₀` is the only edge leaving `A`. -/
theorem d_swap_ge (hM : Fintype.card V ≤ M)
    (hcut : ∀ x y, G.Adj x y → x ∈ A → y ∉ A → x = a₀ ∧ y = b₀)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∉ A) (y : V) :
    (if y ∈ A then G.dist a₁ y else 1 + G.dist b₁ y) ≤
      d M (G.deleteEdges {s(a₀, b₀)} ⊔ edge a₁ b₁) a₁ y := by
  haveI : Nonempty V := ⟨y⟩
  set G' := G.deleteEdges {s(a₀, b₀)} ⊔ edge a₁ b₁
  by_cases hr : G'.Reachable a₁ y
  · rw [d_of_reachable hr]
    obtain ⟨Q, hQ, hl⟩ := hr.exists_path_of_dist
    rw [← hl]
    split_ifs with hy
    · -- `Q` does not use the new edge
      have he : s(a₁, b₁) ∉ Q.edges := by
        intro he
        cases Q with
        | nil => simp at he
        | @cons _ c _ h Q2 =>
          have hc := first_edge_eq h Q2 hQ he
          subst hc
          have hu : a₁ ∉ Q2.support := (Walk.cons_isPath_iff h Q2).1 hQ |>.2
          obtain ⟨x', y', h', p1, p2, hQ2, hx', hy'⟩ :=
            Walk.exists_dart_of_pred (fun z => z ∉ A) Q2 hb₁ (by simpa using hy)
          simp only [not_not] at hy'
          have := swap_cross hcut hb₁ h'.symm hy' hx'
          apply hu
          rw [hQ2, Walk.support_append, Walk.support_cons, List.tail_cons]
          exact List.mem_append_right _ (this.1 ▸ p2.start_mem_support)
      exact dist_le_of_walk_avoid edgeSet_swap_sub Q he
    · obtain ⟨x', y', h', p1, p2, hQe, hx', hy'⟩ :=
        Walk.exists_dart_of_pred (fun z => z ∈ A) Q ha₁ hy
      obtain ⟨rfl, rfl⟩ := swap_cross hcut hb₁ h' hx' hy'
      have hnd := hQ.support_nodup
      rw [hQe, Walk.support_append, Walk.support_cons, List.tail_cons] at hnd
      have hu : x' ∉ p2.support := by
        intro hmem
        exact List.disjoint_of_nodup_append hnd (Walk.end_mem_support p1) hmem
      have hp2 : s(x', y') ∉ p2.edges := fun h'' => hu (Walk.fst_mem_support_of_mem_edges _ h'')
      have := dist_le_of_walk_avoid edgeSet_swap_sub p2 hp2
      rw [hQe, Walk.length_append, Walk.length_cons]
      omega
  · rw [d_of_not_reachable hr]
    have := dist_lt_card' (G := G) a₁ y
    have := dist_lt_card' (G := G) b₁ y
    split_ifs <;> omega

/-- If both endpoints of the new edge lie in `A`, nothing leaves `A` any more. -/
theorem not_reachable_cut (hcut : ∀ x y, G.Adj x y → x ∈ A → y ∉ A → x = a₀ ∧ y = b₀)
    (ha₁ : a₁ ∈ A) (hb₁ : b₁ ∈ A) {a b : V} (ha : a ∈ A) (hb : b ∉ A) :
    ¬ (G.deleteEdges {s(a₀, b₀)} ⊔ edge a₁ b₁).Reachable a b := by
  rintro ⟨Q⟩
  obtain ⟨x', y', h', -, -, -, hx', hy'⟩ := Walk.exists_dart_of_pred (fun z => z ∈ A) Q ha hb
  rw [sup_adj, deleteEdges_adj, edge_adj] at h'
  rcases h' with ⟨h, hne⟩ | ⟨h, -⟩
  · obtain ⟨rfl, rfl⟩ := hcut x' y' h hx' hy'; simp at hne
  · rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
    · exact hy' hb₁
    · exact hy' ha₁

end Podc.BilateralNetworkCreation
