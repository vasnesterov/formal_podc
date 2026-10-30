import Papers.PODC2023.BilateralNetworkCreation.Model
import Cslib.Foundations.Combinatorics.SimpleGraph.ShortestWalks
import Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree

/-!
# Rooted trees via the metric

For a tree `G` rooted at `r`, the layer of `x` is `dist(r, x)` and the subtree `T_u` is
`sub G r u = {x | dist(r,x) = dist(r,u) + dist(u,x)}` (the `x` whose path to `r` passes `u`). This
metric description makes containment of subtrees and "ancestors" purely metric facts; the tree
structure is used only for:

* uniqueness of ancestors at a given layer (`anc_unique`), via uniqueness of paths;
* the component description: for `u ≠ r` with parent `p`, `T_u` is the component of `u` in
  `G - up` (`mem_sub_iff_reachable`), and the rest is the component of `p`;
* the bridge formula `dist(x, y) = dist(x, u) + 1 + dist(p, y)` for `x ∈ T_u`, `y ∉ T_u`
  (`dist_cross`), and its corollary, the "moving along an edge" formula `sum_move`;
* `d_le_dist_of_reachable`: two vertices on the same side of the edge `up` keep (at most) their
  distance in any graph containing `G - up`.

CSLib candidate (rooted-tree metric API), but kept paper-local for now.
-/

-- CSLib candidate (the whole file is general graph theory)
namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

/-- The subtree `T_u` of a tree rooted at `r`. -/
noncomputable def sub (G : SimpleGraph V) (r u : V) : Finset V :=
  univ.filter fun x => G.dist r x = G.dist r u + G.dist u x

variable {r u v w x y a b p c : V}

lemma mem_sub : x ∈ sub G r u ↔ G.dist r x = G.dist r u + G.dist u x := by simp [sub]

lemma self_mem_sub : u ∈ sub G r u := by simp [sub]

lemma sub_root : sub G r r = univ := by ext; simp [sub]

lemma layer_le_of_mem_sub (hx : x ∈ sub G r u) : G.dist r u ≤ G.dist r x := by
  rw [mem_sub] at hx; omega

lemma sub_trans (hG : G.Connected) (hw : w ∈ sub G r u) (hx : x ∈ sub G r w) :
    x ∈ sub G r u := by
  rw [mem_sub] at *
  have h1 := hG.dist_triangle (u := u) (v := w) (w := x)
  have h2 := hG.dist_triangle (u := r) (v := u) (w := x)
  omega

lemma sub_subset (hG : G.Connected) (hw : w ∈ sub G r u) : sub G r w ⊆ sub G r u :=
  fun _ hx => sub_trans hG hw hx

/-- Vertices on a shortest walk split its length. -/
lemma dist_add_dist_of_mem_support (hG : G.Connected) (P : G.Walk a b)
    (hP : P.length = G.dist a b) (hw : w ∈ P.support) :
    G.dist a w + G.dist w b = G.dist a b := by
  have h1 := dist_le (P.takeUntil w hw)
  have h2 := dist_le (P.dropUntil w hw)
  have h3 := congrArg Walk.length (P.take_spec hw)
  rw [Walk.length_append] at h3
  have h4 := hG.dist_triangle (u := a) (v := w) (w := b)
  omega

/-- Ancestors: if `x ∈ T_u`, every layer between `u` and `x` contains an ancestor of `x` in `T_u`. -/
lemma exists_anc (hG : G.Connected) (hx : x ∈ sub G r u) (j : ℕ) (h1 : G.dist r u ≤ j)
    (h2 : j ≤ G.dist r x) : ∃ w ∈ sub G r u, G.dist r w = j ∧ x ∈ sub G r w := by
  obtain ⟨P, hP⟩ := hG.exists_walk_length_eq_dist u x
  rw [mem_sub] at hx
  set k := j - G.dist r u
  refine ⟨P.getVert k, ?_⟩
  have ht := dist_le (P.take k)
  have hd := dist_le (P.drop k)
  rw [Walk.take_length] at ht
  rw [Walk.drop_length] at hd
  have t1 := hG.dist_triangle (u := r) (v := u) (w := P.getVert k)
  have t2 := hG.dist_triangle (u := r) (v := P.getVert k) (w := x)
  have hk : k ≤ P.length := by omega
  rw [Nat.min_eq_left hk] at ht
  simp only [mem_sub]
  omega

lemma mem_sub_of_adj (hadj : G.Adj u p) (hp : G.dist r p + 1 = G.dist r u) : u ∈ sub G r p := by
  rw [mem_sub, dist_eq_one_iff_adj.2 hadj.symm]; omega

lemma parent_not_mem_sub (hp : G.dist r p + 1 = G.dist r u) : p ∉ sub G r u := by
  rw [mem_sub]; omega

/-! ### Tree facts -/

variable (hT : G.IsTree)
include hT

lemma path_length_eq_dist {P : G.Walk a b} (hP : P.IsPath) : P.length = G.dist a b := by
  obtain ⟨Q, hQ, hl⟩ := hT.connected.exists_path_of_dist a b
  have := hT.isAcyclic.path_unique ⟨P, hP⟩ ⟨Q, hQ⟩
  have := congrArg (fun q : G.Path a b => q.1.length) this
  simp only at this
  omega

/-- Two ancestors of `x` in the same layer coincide. -/
lemma anc_unique (ha : x ∈ sub G r a) (hb : x ∈ sub G r b) (hab : G.dist r a = G.dist r b) :
    a = b := by
  have hG := hT.connected
  obtain ⟨P1, hP1⟩ := hG.exists_walk_length_eq_dist r a
  obtain ⟨P2, hP2⟩ := hG.exists_walk_length_eq_dist a x
  obtain ⟨Q1, hQ1⟩ := hG.exists_walk_length_eq_dist r b
  obtain ⟨Q2, hQ2⟩ := hG.exists_walk_length_eq_dist b x
  rw [mem_sub] at ha hb
  have hW : (P1.append P2).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by rw [Walk.length_append]; omega)
  have hW' : (Q1.append Q2).IsPath :=
    Walk.isPath_of_length_eq_dist _ (by rw [Walk.length_append]; omega)
  have he := hT.isAcyclic.path_unique ⟨_, hW⟩ ⟨_, hW'⟩
  have he' : P1.append P2 = Q1.append Q2 := congrArg Subtype.val he
  have g1 := Walk.getVert_append P1 P2 (G.dist r a)
  have g2 := Walk.getVert_append Q1 Q2 (G.dist r b)
  rw [if_neg (by omega), show G.dist r a - P1.length = 0 by omega, Walk.getVert_zero] at g1
  rw [if_neg (by omega), show G.dist r b - Q1.length = 0 by omega, Walk.getVert_zero] at g2
  rw [← g1, ← g2, he', hab]

/-- Ancestors of `x` are nested. -/
lemma mem_sub_of_mem_sub_of_le (ha : x ∈ sub G r a) (hb : x ∈ sub G r b)
    (hab : G.dist r a ≤ G.dist r b) : b ∈ sub G r a := by
  obtain ⟨w, hw, hlw, hxw⟩ := exists_anc hT.connected ha (G.dist r b) hab (layer_le_of_mem_sub hb)
  rwa [anc_unique hT hxw hb hlw] at hw

section Edge

variable (hadj : G.Adj u p) (hp : G.dist r p + 1 = G.dist r u)
include hadj hp

lemma reachable_of_mem_sub (hx : x ∈ sub G r u) : (G.deleteEdges {s(u, p)}).Reachable u x := by
  have hG := hT.connected
  obtain ⟨P, hP⟩ := hG.exists_walk_length_eq_dist u x
  have hsupp : ∀ w ∈ P.support, w ∈ sub G r u := by
    intro w hw
    have := dist_add_dist_of_mem_support hG P hP hw
    rw [mem_sub] at hx ⊢
    have t1 := hG.dist_triangle (u := r) (v := u) (w := w)
    have t2 := hG.dist_triangle (u := r) (v := w) (w := x)
    omega
  have hpe : s(u, p) ∉ P.edges := fun h =>
    parent_not_mem_sub hp (hsupp p (Walk.snd_mem_support_of_mem_edges P h))
  exact ⟨P.toDeleteEdge _ hpe⟩

lemma reachable_parent_of_not_mem_sub (hx : x ∉ sub G r u) :
    (G.deleteEdges {s(u, p)}).Reachable p x := by
  have hG := hT.connected
  obtain ⟨R, hR⟩ := hG.exists_walk_length_eq_dist r x
  have hRe : s(u, p) ∉ R.edges := by
    intro h
    have hu := Walk.fst_mem_support_of_mem_edges R h
    have := dist_add_dist_of_mem_support hG R hR hu
    exact hx (by rw [mem_sub]; omega)
  obtain ⟨R', hR'⟩ := hG.exists_walk_length_eq_dist r p
  have hR'e : s(u, p) ∉ R'.edges := by
    intro h
    have hu := Walk.fst_mem_support_of_mem_edges R' h
    have := dist_add_dist_of_mem_support hG R' hR' hu
    omega
  have h1 : (G.deleteEdges {s(u, p)}).Reachable r p := ⟨R'.toDeleteEdge _ hR'e⟩
  exact h1.symm.trans ⟨R.toDeleteEdge _ hRe⟩

/-- `T_u` is the component of `u` in `G - up`. -/
lemma mem_sub_iff_reachable : x ∈ sub G r u ↔ (G.deleteEdges {s(u, p)}).Reachable u x := by
  refine ⟨reachable_of_mem_sub hT hadj hp, fun h => ?_⟩
  by_contra hx
  have h2 := reachable_parent_of_not_mem_sub hT hadj hp hx
  have hbr : G.IsBridge s(u, p) :=
    isAcyclic_iff_forall_isBridge.1 hT.isAcyclic ((mem_edgeSet G).2 hadj)
  exact (isBridge_iff.1 hbr) (h.trans h2.symm)

/-- The only edge leaving `T_u` is `up`. -/
lemma eq_of_adj_cross (hab : G.Adj a b) (ha : a ∈ sub G r u) (hb : b ∉ sub G r u) :
    a = u ∧ b = p := by
  by_cases he : s(a, b) = s(u, p)
  · rcases Sym2.eq_iff.1 he with h | ⟨rfl, rfl⟩
    · exact h
    · exact absurd ha (parent_not_mem_sub hp)
  · exfalso
    have hH : (G.deleteEdges {s(u, p)}).Adj a b := by
      rw [deleteEdges_adj]; exact ⟨hab, by simpa using he⟩
    have := (reachable_of_mem_sub hT hadj hp ha).trans hH.reachable
    exact hb ((mem_sub_iff_reachable hT hadj hp).2 this)

/-- The bridge formula. -/
lemma dist_cross (hx : x ∈ sub G r u) (hy : y ∉ sub G r u) :
    G.dist x y = G.dist x u + 1 + G.dist p y := by
  have hG := hT.connected
  apply le_antisymm
  · have t1 := hG.dist_triangle (u := x) (v := u) (w := y)
    have t2 := hG.dist_triangle (u := u) (v := p) (w := y)
    rw [dist_eq_one_iff_adj.2 hadj] at t2
    omega
  · obtain ⟨Q, hQ⟩ := hG.exists_walk_length_eq_dist x y
    obtain ⟨a', b', h, Q1, Q2, hQe, ha, hb⟩ :=
      Walk.exists_dart_of_pred (· ∈ sub G r u) Q hx hy
    obtain ⟨rfl, rfl⟩ := eq_of_adj_cross hT hadj hp h ha hb
    have := congrArg Walk.length hQe
    rw [Walk.length_append, Walk.length_cons] at this
    have := dist_le Q1
    have := dist_le Q2
    omega

lemma dist_parent_of_mem (hy : y ∈ sub G r u) : G.dist p y = G.dist u y + 1 := by
  have := dist_cross hT hadj hp hy (parent_not_mem_sub hp)
  rw [dist_self, dist_comm, dist_comm (u := y)] at this; omega

lemma dist_child_of_not_mem (hy : y ∉ sub G r u) : G.dist u y = G.dist p y + 1 := by
  have := dist_cross hT hadj hp self_mem_sub hy
  rw [dist_self] at this; omega

/-- Moving from the child `u` to its parent `p`. -/
lemma sum_move (S : Finset V) :
    ∑ y ∈ S, G.dist p y + (S.filter (· ∉ sub G r u)).card =
      ∑ y ∈ S, G.dist u y + (S.filter (· ∈ sub G r u)).card := by
  rw [← Finset.sum_filter_add_sum_filter_not S (· ∈ sub G r u) (fun y => G.dist p y),
    ← Finset.sum_filter_add_sum_filter_not S (· ∈ sub G r u) (fun y => G.dist u y)]
  rw [Finset.sum_congr rfl fun y hy => dist_parent_of_mem hT hadj hp (Finset.mem_filter.1 hy).2,
    Finset.sum_congr rfl (g := fun y => G.dist p y + 1)
      fun y hy => dist_child_of_not_mem hT hadj hp (Finset.mem_filter.1 hy).2]
  simp only [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one]
  omega

end Edge

/-- Two vertices joined in `H ≤ G` have, in any `G' ≥ H`, distance at most their tree distance. -/
lemma d_le_dist_of_reachable {M : ℕ} {H G' : SimpleGraph V} (hHG : H ≤ G) (hHG' : H ≤ G')
    (h : H.Reachable x y) : d M G' x y ≤ G.dist x y := by
  obtain ⟨P, hP, -⟩ := h.exists_path_of_dist
  have := path_length_eq_dist hT (hP.mapLe hHG)
  rw [Walk.length_mapLe] at this
  have h2 := d_le_of_walk (M := M) (P.mapLe hHG')
  rw [Walk.length_mapLe] at h2
  omega

end Podc.BilateralNetworkCreation
