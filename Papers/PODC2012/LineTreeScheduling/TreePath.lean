import Papers.PODC2026.TreeAA.TreeGeom

/-!
# Paths in tree networks (Section 4 of Chakaravarthy–Roy–Sabharwal, PODC 2012)

Tree geometry for the tree decompositions of Section 4, stated with the distance-based
betweenness `TreeAA.Btw T a w b` (`w` lies on the unique path between `a` and `b`).

* `pathEdges T a b` — the edges of `path(a, b)`; `mem_pathEdges_iff_edges` shows that it is the edge
  set of the unique path `TreeAA.tpath hT a b`.
* `wings T a b y` — the wings of `y` on `path(a, b)` (path edges incident to `y`); at most two
  (`card_wings_le`).
* `nbhd T C` — the neighbourhood `Γ[C]` of a vertex set.
* `exists_nbhd_btw` — a path from inside `C` to outside `C` passes through `Γ[C]` (for any `C`).
* `exists_gate` — the bending point of a path (more generally: gate of a convex set).
* `wings_inter_nonempty` — two overlapping paths both passing through `z` share a wing of `z`.
* `exists_median`, `eq_of_adj_of_adj` (a vertex outside a convex set has at most one neighbour in it).

These are generic tree lemmas (CSLib candidates).
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open SimpleGraph Finset TreeAA

variable {V : Type*} [Fintype V] [DecidableEq V]

section Defs

variable (T : SimpleGraph V)

open Classical in
/-- The edges of the unique path between `a` and `b` in the tree `T`: the tree edges both of whose
endpoints lie between `a` and `b`. See `mem_pathEdges_iff_edges` for faithfulness. -/
noncomputable def pathEdges (a b : V) : Finset (Sym2 V) :=
  univ.filter fun e => e ∈ T.edgeSet ∧ ∀ x ∈ e, Btw T a x b

/-- The wings of `y` on `path(a, b)`: the edges of `path(a, b)` incident to `y`. -/
noncomputable def wings (a b y : V) : Finset (Sym2 V) :=
  (pathEdges T a b).filter fun e => y ∈ e

open Classical in
/-- The neighbourhood `Γ[C]` of a vertex set `C`: the vertices outside `C` adjacent to some vertex of
`C`. -/
noncomputable def nbhd (C : Finset V) : Finset V :=
  univ.filter fun u => u ∉ C ∧ ∃ x ∈ C, T.Adj x u

end Defs

variable {T : SimpleGraph V}

lemma mem_pathEdges {a b : V} {e : Sym2 V} :
    e ∈ pathEdges T a b ↔ e ∈ T.edgeSet ∧ ∀ x ∈ e, Btw T a x b := by
  unfold pathEdges; simp

lemma mk_mem_pathEdges {a b x y : V} :
    s(x, y) ∈ pathEdges T a b ↔ T.Adj x y ∧ Btw T a x b ∧ Btw T a y b := by
  simp [mem_pathEdges]

lemma mem_wings {a b y : V} {e : Sym2 V} : e ∈ wings T a b y ↔ e ∈ pathEdges T a b ∧ y ∈ e := by
  simp [wings]

lemma wings_subset (a b y : V) : wings T a b y ⊆ pathEdges T a b := filter_subset _ _

lemma mem_nbhd {C : Finset V} {u : V} : u ∈ nbhd T C ↔ u ∉ C ∧ ∃ x ∈ C, T.Adj x u := by
  simp [nbhd]

lemma pathEdges_comm (a b : V) : pathEdges T a b = pathEdges T b a := by
  ext e; simp only [mem_pathEdges, btw_comm (a := a)]

/-! ### Generic facts on trees (CSLib candidates) -/

omit [Fintype V] [DecidableEq V] in
lemma dist_eq_add_one_of_adj {g x y : V} (hxy : T.Adj x y) (h : Btw T g x y) :
    T.dist g y = T.dist g x + 1 := by
  unfold TreeAA.Btw at h; rw [dist_eq_one_iff_adj.2 hxy] at h; omega

omit [Fintype V] [DecidableEq V] in
/-- For an edge `xy`, `x` is not between `g` and `y` when `y` is between `g` and `x`. -/
lemma not_btw_of_adj {g x y : V} (hxy : T.Adj x y) (h : Btw T g x y) : ¬ Btw T g y x := by
  intro h'
  have := dist_eq_add_one_of_adj hxy h
  have := dist_eq_add_one_of_adj hxy.symm h'
  omega

section Tree

variable (hT : T.IsTree)
include hT

lemma eq_of_btw_self {a w : V} (h : Btw T a w a) : w = a := by
  have h0 : T.dist a w = 0 := by unfold TreeAA.Btw at h; rw [SimpleGraph.dist_self] at h; omega
  exact ((hT.connected.dist_eq_zero_iff).1 h0).symm

lemma eq_of_btw_btw {a x y : V} (h₁ : Btw T a x y) (h₂ : Btw T a y x) : x = y := by
  unfold TreeAA.Btw at h₁ h₂
  rw [dist_comm (u := y)] at h₂
  exact (hT.connected.dist_eq_zero_iff).1 (by omega)

-- CSLib candidate
/-- In a tree, for an edge `xy` and any vertex `g`, either `x` lies on the path from `g` to `y` or
`y` lies on the path from `g` to `x`. -/
lemma btw_or_of_adj {x y : V} (hxy : T.Adj x y) (g : V) : Btw T g x y ∨ Btw T g y x := by
  by_cases hy : y ∈ (tpath hT g x).support
  · exact Or.inr ((mem_tpath_iff hT).1 hy)
  · left
    have hp := eq_tpath hT _ ((tpath_isPath hT g x).concat hy hxy)
    rw [← mem_tpath_iff hT, ← hp, Walk.support_concat]
    simp

-- CSLib candidate
/-- The predecessor of `v` on the path from `x` to `v`. -/
lemma exists_pred {x v : V} (hne : x ≠ v) : ∃ w, T.Adj w v ∧ Btw T x w v := by
  set p := tpath hT x v
  have hlen : 0 < p.length := by
    rw [length_tpath]
    exact (hT.connected.pos_dist_of_ne hne)
  refine ⟨p.getVert (p.length - 1), ?_, (mem_tpath_iff hT).1 (p.getVert_mem_support _)⟩
  have := p.adj_getVert_succ (i := p.length - 1) (by omega)
  rwa [Nat.sub_add_cancel hlen, Walk.getVert_length] at this

/-- The successor of `x` on the path from `x` to `v`. -/
lemma exists_succ {x v : V} (hne : x ≠ v) : ∃ w, T.Adj x w ∧ Btw T x w v := by
  obtain ⟨w, hw, hb⟩ := exists_pred hT (Ne.symm hne)
  exact ⟨w, hw.symm, hb.symm⟩

/-- Two vertices of `path(a, y)` at the same distance from `a` coincide. -/
lemma eq_of_btw_of_dist_eq' {a x x' y : V} (h : Btw T a x y) (h' : Btw T a x' y)
    (hd : T.dist a x = T.dist a x') : x = x' := by
  have hG := hT.connected
  rcases btw_or hT h x' with h1 | h1
  · unfold TreeAA.Btw at h1; exact (hG.dist_eq_zero_iff).1 (by omega)
  · unfold TreeAA.Btw at h1 h h'
    exact ((hG.dist_eq_zero_iff).1 (by omega : T.dist x' x = 0)).symm

-- CSLib candidate
/-- `pathEdges` is the edge set of the unique tree path. -/
lemma mem_pathEdges_iff_edges {a b : V} {e : Sym2 V} :
    e ∈ pathEdges T a b ↔ e ∈ (tpath hT a b).edges := by
  induction e using Sym2.ind with
  | _ x y =>
  rw [mk_mem_pathEdges]
  constructor
  · rintro ⟨hxy, hx, hy⟩
    -- wlog `x` comes first
    have key : ∀ x y, T.Adj x y → Btw T a x b → Btw T a y b → Btw T a x y →
        s(x, y) ∈ (tpath hT a b).edges := by
      intro x y hxy hx hy hxy'
      set q := ((tpath hT a x).concat hxy).append (tpath hT y b)
      have hq : q.IsPath := by
        apply Walk.isPath_of_length_eq_dist
        rw [Walk.length_append, Walk.length_concat, length_tpath, length_tpath]
        have := dist_eq_add_one_of_adj hxy hxy'
        unfold TreeAA.Btw at hy; omega
      rw [← eq_tpath hT q hq, Walk.edges_append, Walk.edges_concat]
      simp
    rcases btw_or hT hx y with h | h
    · exact key x y hxy hx hy h
    · rcases btw_or hT hy x with h' | h'
      · rw [Sym2.eq_swap]; exact key y x hxy.symm hy hx h'
      · exfalso
        unfold TreeAA.Btw at h h'
        rw [dist_eq_one_iff_adj.2 hxy.symm] at h
        rw [dist_eq_one_iff_adj.2 hxy] at h'
        omega
  · intro he
    exact ⟨(tpath hT a b).edges_subset_edgeSet he,
      (mem_tpath_iff hT).1 ((tpath hT a b).fst_mem_support_of_mem_edges he),
      (mem_tpath_iff hT).1 ((tpath hT a b).snd_mem_support_of_mem_edges he)⟩

open Classical in
/-- The neighbours of `y` on `path(a, b)` lie in a set of at most two vertices. -/
lemma card_nbrs_on_path_le (a b y : V) :
    (univ.filter fun x => T.Adj y x ∧ Btw T a x b).card ≤ 2 := by
  classical
  have hsub : (univ.filter fun x => T.Adj y x ∧ Btw T a x b) ⊆
      (univ.filter fun x => T.Adj y x ∧ Btw T a x y) ∪
        (univ.filter fun x => T.Adj y x ∧ Btw T y x b) := by
    intro x hx
    simp only [mem_filter, mem_univ, true_and, mem_union] at hx ⊢
    rcases btw_or hT hx.2 y with h | h
    · exact Or.inl ⟨hx.1, h⟩
    · exact Or.inr ⟨hx.1, h⟩
  refine (card_le_card hsub).trans ((card_union_le _ _).trans ?_)
  have h1 : (univ.filter fun x => T.Adj y x ∧ Btw T a x y).card ≤ 1 := by
    rw [card_le_one]
    intro x hx x' hx'
    simp only [mem_filter, mem_univ, true_and] at hx hx'
    have e1 := dist_eq_add_one_of_adj hx.1.symm hx.2
    have e2 := dist_eq_add_one_of_adj hx'.1.symm hx'.2
    exact eq_of_btw_of_dist_eq' hT hx.2 hx'.2 (by omega)
  have h2 : (univ.filter fun x => T.Adj y x ∧ Btw T y x b).card ≤ 1 := by
    rw [card_le_one]
    intro x hx x' hx'
    simp only [mem_filter, mem_univ, true_and] at hx hx'
    have e1 := dist_eq_one_iff_adj.2 hx.1
    have e2 := dist_eq_one_iff_adj.2 hx'.1
    exact eq_of_btw_of_dist_eq' hT hx.2 hx'.2 (by omega)
  omega

-- CSLib candidate
/-- A vertex has at most two wings on a path. -/
lemma card_wings_le (a b y : V) : (wings T a b y).card ≤ 2 := by
  classical
  have hsub : wings T a b y ⊆
      (univ.filter fun x => T.Adj y x ∧ Btw T a x b).image fun x => s(y, x) := by
    intro e he
    rw [mem_wings] at he
    obtain ⟨he, hy⟩ := he
    induction e using Sym2.ind with
    | _ p q =>
    rw [mk_mem_pathEdges] at he
    simp only [mem_image, mem_filter, mem_univ, true_and]
    rcases Sym2.mem_iff.1 hy with rfl | rfl
    · exact ⟨q, ⟨he.1, he.2.2⟩, rfl⟩
    · exact ⟨p, ⟨he.1.symm, he.2.1⟩, Sym2.eq_swap⟩
  exact (card_le_card hsub).trans (card_image_le.trans (card_nbrs_on_path_le hT a b y))

/-- The vertex set of a path is convex. -/
lemma convex_path (a b : V) : TreeAA.Convex (T := T) {w | Btw T a w b} := convex_btw hT a b

-- CSLib candidate
/-- **Gate** of a nonempty convex set `K` with respect to `u`: a vertex `y ∈ K` lying on the path
from `u` to every vertex of `K`. For `K = path(d)` this is the bending point of `d` w.r.t. `u`. -/
lemma exists_gate {K : Set V} (hK : TreeAA.Convex (T := T) K) {k₀ : V} (hk₀ : k₀ ∈ K) (u : V) :
    ∃ y ∈ K, ∀ x ∈ K, Btw T u y x := by
  classical
  obtain ⟨y, hy, hmin⟩ := (univ.filter (· ∈ K)).exists_min_image (T.dist u)
    ⟨k₀, by simpa using hk₀⟩
  simp only [mem_filter, mem_univ, true_and] at hy hmin
  exact ⟨y, hy, fun x hx => btw_of_isMin hT hK hy hmin hx⟩

-- CSLib candidate
/-- A path from a vertex of `C` to a vertex outside `C` passes through the neighbourhood `Γ[C]`
(this holds for every vertex set `C`). -/
lemma exists_nbhd_btw {C : Finset V} {x y : V} (hx : x ∈ C) (hy : y ∉ C) :
    ∃ u ∈ nbhd T C, Btw T x u y := by
  classical
  obtain ⟨w, hw, hmin⟩ := (univ.filter fun w => Btw T x w y ∧ w ∉ C).exists_min_image
    (T.dist x) ⟨y, by simpa using ⟨btw_right x y, hy⟩⟩
  simp only [mem_filter, mem_univ, true_and, and_imp] at hw hmin
  have hne : x ≠ w := by rintro rfl; exact hw.2 hx
  obtain ⟨v, hvw, hv⟩ := exists_pred hT hne
  refine ⟨w, mem_nbhd.2 ⟨hw.2, v, ?_, hvw⟩, hw.1⟩
  by_contra hvC
  have := hmin v (hw.1.trans hT.connected hv) hvC
  have := dist_eq_add_one_of_adj hvw hv
  omega

-- CSLib candidate
/-- Two paths sharing an edge and both passing through `z` share an edge incident to `z`, i.e. the
second path contains a wing of `z` on the first. -/
lemma wings_inter_nonempty {a₁ b₁ a₂ b₂ z : V}
    (hov : (pathEdges T a₁ b₁ ∩ pathEdges T a₂ b₂).Nonempty)
    (hz₁ : Btw T a₁ z b₁) (hz₂ : Btw T a₂ z b₂) :
    (wings T a₁ b₁ z ∩ pathEdges T a₂ b₂).Nonempty := by
  obtain ⟨e, he⟩ := hov
  rw [mem_inter] at he
  induction e using Sym2.ind with
  | _ p q =>
  rw [mk_mem_pathEdges, mk_mem_pathEdges] at he
  obtain ⟨⟨hpq, hp₁, hq₁⟩, -, hp₂, hq₂⟩ := he
  by_cases hzp : z = p
  · subst hzp
    exact ⟨s(z, q), mem_inter.2 ⟨mem_wings.2 ⟨mk_mem_pathEdges.2 ⟨hpq, hp₁, hq₁⟩, Sym2.mem_mk_left _ _⟩,
      mk_mem_pathEdges.2 ⟨hpq, hp₂, hq₂⟩⟩⟩
  · obtain ⟨x, hzx, hx⟩ := exists_succ hT hzp
    have h₁ : Btw T a₁ x b₁ := convex_path hT a₁ b₁ z hz₁ p hp₁ x hx
    have h₂ : Btw T a₂ x b₂ := convex_path hT a₂ b₂ z hz₂ p hp₂ x hx
    exact ⟨s(z, x), mem_inter.2 ⟨mem_wings.2 ⟨mk_mem_pathEdges.2 ⟨hzx, hz₁, h₁⟩, Sym2.mem_mk_left _ _⟩,
      mk_mem_pathEdges.2 ⟨hzx, hz₂, h₂⟩⟩⟩

-- CSLib candidate
/-- A vertex outside a convex set has at most one neighbour in it. -/
lemma eq_of_adj_of_adj {C : Set V} (hC : TreeAA.Convex (T := T) C) {u x y : V} (hu : u ∉ C)
    (hx : x ∈ C) (hy : y ∈ C) (hux : T.Adj u x) (huy : T.Adj u y) : x = y := by
  by_contra hxy
  apply hu
  refine hC x hx y hy u ?_
  have hd : T.dist x y = 2 := by
    have h1 := hT.connected.dist_triangle (u := x) (v := u) (w := y)
    rw [dist_eq_one_iff_adj.2 hux.symm, dist_eq_one_iff_adj.2 huy] at h1
    have h2 : T.dist x y ≠ 0 := fun h => hxy ((hT.connected.dist_eq_zero_iff).1 h)
    have h3 : T.dist x y ≠ 1 := by
      intro h
      have hxy' := dist_eq_one_iff_adj.1 h
      rcases btw_or_of_adj hT hxy' u with h | h
      · have := dist_eq_add_one_of_adj hxy' h
        rw [dist_eq_one_iff_adj.2 hux, dist_eq_one_iff_adj.2 huy] at this; omega
      · have := dist_eq_add_one_of_adj hxy'.symm h
        rw [dist_eq_one_iff_adj.2 hux, dist_eq_one_iff_adj.2 huy] at this; omega
    omega
  unfold TreeAA.Btw
  rw [dist_eq_one_iff_adj.2 hux.symm, dist_eq_one_iff_adj.2 huy, hd]

-- CSLib candidate
/-- **Median** of three vertices of a tree. -/
lemma exists_median (a b c : V) : ∃ m, Btw T a m b ∧ Btw T a m c ∧ Btw T b m c := by
  obtain ⟨m, hm, hg⟩ := exists_gate hT (convex_path hT a b) (btw_left a b) c
  exact ⟨m, hm, (hg a (btw_left a b)).symm, (hg b (btw_right a b)).symm⟩

end Tree

end Podc.LineTreeScheduling
