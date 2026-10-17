import Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree
import Cslib.Foundations.Combinatorics.SimpleGraph.Ball

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/BFSTree.lean (append to the existing file)

/-!
# BFS parent pointers without connectivity

`Connected.bfsTree` needs a connected graph. Here the parent pointers of a BFS forest towards a
root `r` are defined for an arbitrary graph: `bfsParent G r x` is a neighbour of `x` one step closer
to `r` (and `r` for `x = r`). On the component of `r` this is a BFS tree; elsewhere it is
unspecified.

The parent is chosen by `Classical.epsilon` from a predicate that only involves the neighbours of
`x` and the distances to `r` of `x` and of these neighbours. Hence it only depends on the local
structure (`bfsParent_congr`), which is what locality proofs of distributed algorithms need.

## Main definitions

* `SimpleGraph.bfsParent G r x`: the BFS parent of `x` towards `r`.
* `SimpleGraph.bfsAncestor G r x i`: the `i`-th ancestor `(bfsParent G r)^[i] x`.

## Main statements

* `SimpleGraph.Reachable.adj_bfsParent`, `SimpleGraph.Reachable.dist_bfsParent_add_one`: the parent
  of `x ≠ r` is a neighbour one step closer to `r`.
* `SimpleGraph.bfsParent_congr`: two graphs with the same parent predicate at `x` have the same
  parent of `x`.
* `SimpleGraph.Reachable.dist_bfsAncestor`, `SimpleGraph.Reachable.bfsAncestor_eq_root`,
  `SimpleGraph.Reachable.adj_bfsAncestor`, `SimpleGraph.edist_bfsAncestor_le`: the ancestors of `x`
  form a shortest path from `x` to `r`.
-/

namespace SimpleGraph

variable {V : Type*}

section Def

variable (G : SimpleGraph V) (r : V)

/-- The parent of `x` in the BFS forest towards `r`: a neighbour of `x` one step closer to `r`
(and `r` itself for `x = r`), chosen by `Classical.epsilon` from a predicate that only involves the
neighbours of `x` (see `bfsParent_congr`). Unspecified if `x` is not connected to `r`. -/
noncomputable def bfsParent (x : V) : V :=
  @Classical.epsilon V ⟨x⟩ fun y =>
    (x = r → y = r) ∧ (x ≠ r → G.Adj x y ∧ G.dist r y + 1 = G.dist r x)

/-- The `i`-th ancestor of `x` in the BFS forest towards `r`. -/
noncomputable def bfsAncestor (x : V) (i : ℕ) : V := (G.bfsParent r)^[i] x

end Def

variable {G G' : SimpleGraph V} {r x : V}

/-- A vertex connected to `r` has a BFS parent: `r` itself if `x = r`, otherwise a neighbour one
step closer to `r`. -/
theorem Reachable.exists_bfsParent (hr : G.Reachable r x) :
    ∃ y, (x = r → y = r) ∧ (x ≠ r → G.Adj x y ∧ G.dist r y + 1 = G.dist r x) := by
  by_cases hx : x = r
  · exact ⟨r, fun _ => rfl, fun h => absurd hx h⟩
  · obtain ⟨n, hn⟩ : ∃ n, G.dist r x = n + 1 :=
      Nat.exists_eq_succ_of_ne_zero ((hr.pos_dist_of_ne (Ne.symm hx)).ne')
    have he : G.edist r x = ((n + 1 : ℕ) : ℕ∞) := by rw [← hr.coe_dist_eq_edist, hn]
    obtain ⟨y, hy, hyx⟩ := exists_adj_of_edist_eq_succ he
    refine ⟨y, fun h => absurd h hx, fun _ => ⟨hyx.symm, ?_⟩⟩
    have := (hr.trans hyx.symm.reachable).coe_dist_eq_edist
    rw [hy] at this
    have : G.dist r y = n := by exact_mod_cast this
    omega

/-- Specification of the BFS parent of a vertex connected to `r`. -/
theorem Reachable.bfsParent_spec (hr : G.Reachable r x) :
    (x = r → G.bfsParent r x = r) ∧
      (x ≠ r → G.Adj x (G.bfsParent r x) ∧ G.dist r (G.bfsParent r x) + 1 = G.dist r x) :=
  @Classical.epsilon_spec V _ hr.exists_bfsParent

/-- The root is its own parent. -/
@[simp] theorem bfsParent_root : G.bfsParent r r = r :=
  (Reachable.refl r).bfsParent_spec.1 rfl

/-- The parent of `x ≠ r` is a neighbour of `x`. -/
theorem Reachable.adj_bfsParent (hr : G.Reachable r x) (hx : x ≠ r) : G.Adj x (G.bfsParent r x) :=
  (hr.bfsParent_spec.2 hx).1

/-- The parent of `x ≠ r` is one step closer to `r`. -/
theorem Reachable.dist_bfsParent_add_one (hr : G.Reachable r x) (hx : x ≠ r) :
    G.dist r (G.bfsParent r x) + 1 = G.dist r x :=
  (hr.bfsParent_spec.2 hx).2

/-- The parent of a vertex connected to `r` is connected to `r`. -/
theorem Reachable.reachable_bfsParent (hr : G.Reachable r x) : G.Reachable r (G.bfsParent r x) := by
  by_cases hx : x = r
  · rw [hx, bfsParent_root]
  · exact hr.trans (hr.adj_bfsParent hx).reachable

/-- The distance of the parent to the root is one less. -/
theorem Reachable.dist_bfsParent (hr : G.Reachable r x) :
    G.dist r (G.bfsParent r x) = G.dist r x - 1 := by
  by_cases hx : x = r
  · subst hx; simp
  · have := hr.dist_bfsParent_add_one hx; omega

/-- Locality of the BFS parent: if two graphs agree, at `x`, on which vertices are neighbours one
step closer to `r`, then `x` has the same parent in both. -/
theorem bfsParent_congr
    (h : ∀ y, x ≠ r → (G.Adj x y ∧ G.dist r y + 1 = G.dist r x ↔
      G'.Adj x y ∧ G'.dist r y + 1 = G'.dist r x)) :
    G.bfsParent r x = G'.bfsParent r x := by
  unfold bfsParent
  congr 1
  funext y
  exact propext (and_congr_right fun _ => imp_congr_right fun hx => h y hx)

/-! ### Ancestors -/

/-- The `0`-th ancestor of `x` is `x` itself. -/
@[simp] theorem bfsAncestor_zero (x : V) : G.bfsAncestor r x 0 = x := rfl

/-- The `(i + 1)`-th ancestor is the parent of the `i`-th ancestor. -/
theorem bfsAncestor_succ (x : V) (i : ℕ) :
    G.bfsAncestor r x (i + 1) = G.bfsParent r (G.bfsAncestor r x i) :=
  Function.iterate_succ_apply' _ _ _

/-- The ancestors of a vertex connected to `r` are connected to `r`. -/
theorem Reachable.reachable_bfsAncestor (hr : G.Reachable r x) (i : ℕ) :
    G.Reachable r (G.bfsAncestor r x i) := by
  induction i with
  | zero => exact hr
  | succ i ih => rw [bfsAncestor_succ]; exact ih.reachable_bfsParent

/-- The `i`-th ancestor is `i` steps closer to the root (until it reaches the root). -/
theorem Reachable.dist_bfsAncestor (hr : G.Reachable r x) (i : ℕ) :
    G.dist r (G.bfsAncestor r x i) = G.dist r x - i := by
  induction i with
  | zero => rfl
  | succ i ih => rw [bfsAncestor_succ, (hr.reachable_bfsAncestor i).dist_bfsParent, ih]; omega

/-- After `d(r, x)` steps the ancestors reach the root. -/
theorem Reachable.bfsAncestor_eq_root (hr : G.Reachable r x) {i : ℕ} (hi : G.dist r x ≤ i) :
    G.bfsAncestor r x i = r := by
  have h := hr.dist_bfsAncestor i
  rw [Nat.sub_eq_zero_of_le hi, (hr.reachable_bfsAncestor i).dist_eq_zero_iff] at h
  exact h.symm

/-- Consecutive ancestors below the root are adjacent. -/
theorem Reachable.adj_bfsAncestor (hr : G.Reachable r x) {i : ℕ} (hi : i < G.dist r x) :
    G.Adj (G.bfsAncestor r x i) (G.bfsAncestor r x (i + 1)) := by
  have hne : G.bfsAncestor r x i ≠ r := by
    intro h
    have := hr.dist_bfsAncestor i
    rw [h, dist_self] at this
    omega
  rw [bfsAncestor_succ]
  exact (hr.reachable_bfsAncestor i).adj_bfsParent hne

/-- The ancestors of a vertex of the closed ball of radius `h` around `r` stay in that ball. -/
theorem edist_bfsAncestor_le {h : ℕ} (hx : G.edist r x ≤ h) (i : ℕ) :
    G.edist r (G.bfsAncestor r x i) ≤ h := by
  have hr := reachable_of_edist_le_natCast hx
  apply (hr.reachable_bfsAncestor i).edist_le_natCast
  rw [hr.dist_bfsAncestor]
  have := dist_le_of_edist_le_natCast hx
  omega

end SimpleGraph
