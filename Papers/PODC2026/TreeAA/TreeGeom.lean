import Mathlib

/-!
# Geodesic geometry of graphs and trees

* `Btw G a w b`: `w` lies on a shortest path between `a` and `b` (`d(a,w) + d(w,b) = d(a,b)`).
* `hull G S`: the shortest-path convex hull of the paper (Section 2): the union of all shortest
  paths between pairs of vertices of `S`.
* For a tree `T` (`hT : T.IsTree`): the unique path `tpath hT a b`, with
  `mem_tpath_iff` (its vertices are exactly the `w` with `Btw T a w b`), the "tripod" property
  `btw_or`, convexity of hulls (`hull_convex`) and the **gate lemma** `btw_of_isMin` (the vertex
  of a convex set closest to `v` lies on the path from `v` to every vertex of the set).
* Root paths `rpath hT r u` (the vertex list of the path from the root `r` to `u`): prefixes,
  indices (`dist_rpath_getElem`), and the betweenness of their entries.

CSLib candidates (generic tree geometry).
-/

namespace TreeAA

open SimpleGraph

variable {V : Type*}

/-! ### Betweenness and hulls in a graph -/

section General

variable (G : SimpleGraph V)

/-- `w` lies on a shortest path between `a` and `b`. -/
def Btw (a w b : V) : Prop := G.dist a w + G.dist w b = G.dist a b

/-- The (shortest-path) convex hull `⟨S⟩` of a vertex set: the union of all shortest paths
between pairs of vertices of `S`. -/
def hull (S : Set V) : Set V := {w | ∃ a ∈ S, ∃ b ∈ S, Btw G a w b}

variable {G}

lemma Btw.symm {a w b : V} (h : Btw G a w b) : Btw G b w a := by
  unfold Btw at *; rw [dist_comm, add_comm, dist_comm (u := w)]; rwa [dist_comm (u := b)]

lemma btw_comm {a w b : V} : Btw G a w b ↔ Btw G b w a := ⟨Btw.symm, Btw.symm⟩

lemma btw_left (a b : V) : Btw G a a b := by simp [Btw]

lemma btw_right (a b : V) : Btw G a b b := by simp [Btw]

lemma subset_hull (S : Set V) : S ⊆ hull G S := fun a ha => ⟨a, ha, a, ha, btw_left a a⟩

lemma hull_mono {S S' : Set V} (h : S ⊆ S') : hull G S ⊆ hull G S' := by
  rintro w ⟨a, ha, b, hb, hw⟩; exact ⟨a, h ha, b, h hb, hw⟩

variable (hG : G.Connected)
include hG

/-- If `x` is between `a` and `b` and `w` between `a` and `x`, then `w` is between `a` and `b`. -/
lemma Btw.trans {a x b w : V} (hx : Btw G a x b) (hw : Btw G a w x) : Btw G a w b := by
  unfold Btw at *
  have h1 := hG.dist_triangle (u := w) (v := x) (w := b)
  have h2 := hG.dist_triangle (u := a) (v := w) (w := b)
  omega

/-- If `x` is between `a` and `b` and `w` between `x` and `b`, then `x` is between `a` and `w`
and `w` between `a` and `b`. -/
lemma Btw.trans' {a x b w : V} (hx : Btw G a x b) (hw : Btw G x w b) : Btw G a w b := by
  unfold Btw at *
  have h1 := hG.dist_triangle (u := a) (v := x) (w := w)
  have h2 := hG.dist_triangle (u := a) (v := w) (w := b)
  omega

lemma Btw.left_of_trans' {a x b w : V} (hx : Btw G a x b) (hw : Btw G x w b) : Btw G a x w := by
  unfold Btw at *
  have h1 := hG.dist_triangle (u := a) (v := x) (w := w)
  have h2 := hG.dist_triangle (u := a) (v := w) (w := b)
  omega

lemma dist_le_of_btw {a w b : V} (h : Btw G a w b) : G.dist a w ≤ G.dist a b := by
  unfold Btw at h; omega

lemma eq_of_btw_of_dist_eq {a w b : V} (h : Btw G a w b) (hd : G.dist a w = G.dist a b) : w = b := by
  unfold Btw at h
  exact (hG.dist_eq_zero_iff).1 (by omega)

end General

/-! ### Lists whose consecutive entries are adjacent -/

lemma dist_getElem_le {G : SimpleGraph V} (hG : G.Connected) {L : List V} (hL : L.IsChain G.Adj)
    {i j : ℕ} (hij : i ≤ j) (hj : j < L.length) :
    G.dist L[i] L[j] ≤ j - i := by
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j hij ih =>
    have hj' : j < L.length := by omega
    have hadj : G.Adj L[j] L[j + 1] := List.isChain_iff_getElem.1 hL j hj
    have h1 := hG.dist_triangle (u := L[i]) (v := L[j]) (w := L[j + 1])
    have h2 : G.dist L[j] L[j + 1] = 1 := dist_eq_one_iff_adj.2 hadj
    have := ih hj'
    omega

lemma dist_getElem_le' {G : SimpleGraph V} (hG : G.Connected) {L : List V} (hL : L.IsChain G.Adj)
    {i j : ℕ} (hi : i < L.length) (hj : j < L.length) (hij : j ≤ i + 1) (hji : i ≤ j + 1) :
    G.dist L[i] L[j] ≤ 1 := by
  rcases le_total i j with h | h
  · have := dist_getElem_le hG hL h hj; omega
  · have := dist_getElem_le hG hL h hi; rw [dist_comm]; omega

/-! ### Trees -/

section Tree

variable {T : SimpleGraph V} (hT : T.IsTree)
include hT

/-- The unique path between two vertices of a tree. -/
noncomputable def tpath (a b : V) : T.Walk a b := (hT.existsUnique_path a b).exists.choose

lemma tpath_isPath (a b : V) : (tpath hT a b).IsPath := (hT.existsUnique_path a b).exists.choose_spec

lemma eq_tpath {a b : V} (p : T.Walk a b) (hp : p.IsPath) : p = tpath hT a b :=
  (hT.existsUnique_path a b).unique hp (tpath_isPath hT a b)

lemma length_tpath (a b : V) : (tpath hT a b).length = T.dist a b := by
  obtain ⟨q, hq⟩ := hT.connected.exists_walk_length_eq_dist a b
  rw [← eq_tpath hT q (q.isPath_of_length_eq_dist hq), hq]

variable [DecidableEq V]

/-- The vertices of the path between `a` and `b` are exactly the vertices between `a` and `b`. -/
lemma mem_tpath_iff {a b w : V} : w ∈ (tpath hT a b).support ↔ Btw T a w b := by
  constructor
  · intro hw
    set p := tpath hT a b
    have hp := tpath_isPath hT a b
    have h1 := eq_tpath hT _ (hp.takeUntil hw)
    have h2 := eq_tpath hT _ (hp.dropUntil hw)
    have := congrArg Walk.length (p.take_spec hw)
    rw [Walk.length_append, h1, h2, length_tpath, length_tpath, length_tpath] at this
    exact this
  · intro hw
    have hq : ((tpath hT a w).append (tpath hT w b)).IsPath := by
      apply Walk.isPath_of_length_eq_dist
      rw [Walk.length_append, length_tpath, length_tpath]
      exact hw
    rw [← eq_tpath hT _ hq, Walk.mem_support_append_iff]
    exact Or.inl (Walk.end_mem_support _)

/-- **Tripod property** of trees: the path from `a` to `b` is covered by the paths from `a` to
`c` and from `c` to `b`. -/
lemma btw_or {a w b : V} (h : Btw T a w b) (c : V) : Btw T a w c ∨ Btw T c w b := by
  rw [← mem_tpath_iff hT] at h
  set q := (tpath hT a c).append (tpath hT c b)
  rw [← eq_tpath hT _ q.bypass_isPath] at h
  rcases (Walk.mem_support_append_iff _ _).1 (q.support_bypass_subset_support h) with h | h
  · exact Or.inl ((mem_tpath_iff hT).1 h)
  · exact Or.inr ((mem_tpath_iff hT).1 h)

lemma btw_of_hull {S : Set V} {x : V} (hx : x ∈ hull T S) (s₀ : V) :
    ∃ s ∈ S, Btw T s₀ x s := by
  obtain ⟨a, ha, b, hb, hab⟩ := hx
  rcases btw_or hT hab s₀ with h | h
  · exact ⟨a, ha, h.symm⟩
  · exact ⟨b, hb, h⟩

/-- Hulls in trees are (geodesically) convex. -/
lemma hull_convex {S : Set V} {x y w : V} (hx : x ∈ hull T S) (hy : y ∈ hull T S)
    (hw : Btw T x w y) : w ∈ hull T S := by
  obtain ⟨s₀, hs₀, -⟩ := id hx
  obtain ⟨s₁, hs₁, h₁⟩ := btw_of_hull hT hx s₀
  obtain ⟨s₂, hs₂, h₂⟩ := btw_of_hull hT hy s₀
  rcases btw_or hT hw s₀ with h | h
  · exact ⟨s₀, hs₀, s₁, hs₁, h₁.trans hT.connected h.symm⟩
  · exact ⟨s₀, hs₀, s₂, hs₂, h₂.trans hT.connected h⟩

/-- A vertex set is (geodesically) convex. -/
def Convex (K : Set V) : Prop := ∀ x ∈ K, ∀ y ∈ K, ∀ w, Btw T x w y → w ∈ K

lemma convex_hull (S : Set V) : Convex (T := T) (hull T S) :=
  fun _ hx _ hy _ hw => hull_convex hT hx hy hw

/-- **Gate lemma**: in a tree, if `g` is a vertex of the convex set `K` closest to `v`, then `g`
lies on the path from `v` to every vertex of `K`. -/
lemma btw_of_isMin {K : Set V} (hK : Convex (T := T) K) {v g : V} (hg : g ∈ K)
    (hmin : ∀ k ∈ K, T.dist v g ≤ T.dist v k) {x : V} (hx : x ∈ K) : Btw T v g x := by
  set q := (tpath hT v g).append (tpath hT g x)
  have hq : q.IsPath := by
    rw [Walk.isPath_def, Walk.support_append, List.nodup_append]
    refine ⟨(Walk.isPath_def _).1 (tpath_isPath hT v g),
      ((Walk.isPath_def _).1 (tpath_isPath hT g x)).sublist (List.tail_sublist _), ?_⟩
    rintro z hz z' hz' rfl
    have hz'' : z ∈ (tpath hT g x).support := List.mem_of_mem_tail hz'
    have hzK : z ∈ K := hK g hg x hx z ((mem_tpath_iff hT).1 hz'')
    have hbtw := (mem_tpath_iff hT).1 hz
    have := hmin z hzK
    have hzg : z = g := by
      have h0 : T.dist z g = 0 := by unfold Btw at hbtw; omega
      exact (hT.connected.dist_eq_zero_iff).1 h0
    subst hzg
    -- `z` is the start of a path, so it is not in the tail of its support
    have hnd := (Walk.isPath_def _).1 (tpath_isPath hT z x)
    rw [← Walk.cons_tail_support (tpath hT z x)] at hnd
    exact (List.nodup_cons.1 hnd).1 hz'
  have := congrArg Walk.length (eq_tpath hT q hq)
  rw [Walk.length_append, length_tpath, length_tpath, length_tpath] at this
  exact this

lemma convex_btw_aux {r u x y w : V} (hx : Btw T r x u) (hy : Btw T r y u)
    (hw : Btw T x w y) (hxy : T.dist r x ≤ T.dist r y) : Btw T r w u := by
  have hG := hT.connected
  have hrxy : Btw T r x y := by
    rcases btw_or hT hx y with h | h
    · exact h
    · -- `x` between `y` and `u`, and closer to `r` than `y`: then `x = y`
      unfold Btw at h hx hy
      have hxy0 : T.dist y x = 0 := by omega
      rw [(hG.dist_eq_zero_iff).1 hxy0]
      exact btw_right r x
  exact hy.trans hG (hrxy.trans' hG hw)

/-- The vertex set of a path from a fixed vertex is convex. -/
lemma convex_btw (r u : V) : Convex (T := T) {w | Btw T r w u} := by
  intro x hx y hy w hw
  rcases le_total (T.dist r x) (T.dist r y) with h | h
  · exact convex_btw_aux hT hx hy hw h
  · exact convex_btw_aux hT hy hx hw.symm h

/-! ### Root paths -/

/-- The vertex list of the path from the root `r` to `u`. -/
noncomputable def rpath (r u : V) : List V := (tpath hT r u).support

lemma mem_rpath {r u w : V} : w ∈ rpath hT r u ↔ Btw T r w u := mem_tpath_iff hT

lemma length_rpath (r u : V) : (rpath hT r u).length = T.dist r u + 1 := by
  rw [rpath, Walk.length_support, length_tpath]

lemma rpath_ne_nil (r u : V) : rpath hT r u ≠ [] := Walk.support_ne_nil _

lemma rpath_isChain (r u : V) : (rpath hT r u).IsChain T.Adj := Walk.isChain_adj_support _

lemma rpath_nodup (r u : V) : (rpath hT r u).Nodup := (Walk.isPath_def _).1 (tpath_isPath hT r u)

lemma getLast_rpath (r u : V) : (rpath hT r u).getLast (rpath_ne_nil hT r u) = u :=
  Walk.getLast_support _

lemma head_rpath (r u : V) : (rpath hT r u).head (rpath_ne_nil hT r u) = r :=
  Walk.head_support _

lemma rpath_getElem_zero (r u : V) : (rpath hT r u)[0]'(by rw [length_rpath]; omega) = r := by
  have := head_rpath hT r u
  rw [List.head_eq_getElem] at this
  exact this

lemma mem_rpath_self (r u : V) : u ∈ rpath hT r u := (mem_rpath hT).2 (btw_right r u)

lemma root_mem_rpath (r u : V) : r ∈ rpath hT r u := (mem_rpath hT).2 (btw_left r u)

/-- The `i`-th vertex of a root path is at distance `i` from the root. -/
lemma dist_rpath_getElem (r u : V) {i : ℕ} (hi : i < (rpath hT r u).length) :
    T.dist r (rpath hT r u)[i] = i := by
  have hG := hT.connected
  have hL := length_rpath hT r u
  have h1 := dist_getElem_le hG (rpath_isChain hT r u) (Nat.zero_le i) hi
  have h2 := dist_getElem_le hG (rpath_isChain hT r u) (i := i) (j := (rpath hT r u).length - 1)
    (by omega) (by omega)
  rw [rpath_getElem_zero] at h1
  have hlast : (rpath hT r u)[(rpath hT r u).length - 1] = u := by
    rw [← List.getLast_eq_getElem]; exact getLast_rpath hT r u
  have hmem : Btw T r (rpath hT r u)[i] u := (mem_rpath hT).1 (List.getElem_mem _)
  rw [hlast] at h2
  unfold Btw at hmem
  omega

/-- If `w` is on the root path of `u`, then the root path of `w` is a prefix of it. -/
lemma rpath_prefix {r u w : V} (hw : w ∈ rpath hT r u) : rpath hT r w <+: rpath hT r u := by
  have hp := tpath_isPath hT r u
  have h1 := eq_tpath hT _ (hp.takeUntil hw)
  have := congrArg Walk.support ((tpath hT r u).take_spec hw)
  rw [Walk.support_append, h1] at this
  exact ⟨_, this⟩

/-- A non-empty prefix of a root path is the root path of its last vertex. -/
lemma eq_rpath_of_prefix {r u : V} {L : List V} (hL : L <+: rpath hT r u) (hne : L ≠ []) :
    L = rpath hT r (L.getLast hne) := by
  set w := L.getLast hne
  have hlen := hL.length_le
  have hw : w = (rpath hT r u)[L.length - 1]'(by
      have := List.length_pos_of_ne_nil hne; omega) := by
    simp only [w]; rw [List.getLast_eq_getElem]; exact hL.getElem _
  have hwmem : w ∈ rpath hT r u := by rw [hw]; exact List.getElem_mem _
  have hd := dist_rpath_getElem hT r u (i := L.length - 1) (by
      have := List.length_pos_of_ne_nil hne; omega)
  rw [← hw] at hd
  have hpre := rpath_prefix hT hwmem
  have hlen' : (rpath hT r w).length = L.length := by
    rw [length_rpath, hd]; have := List.length_pos_of_ne_nil hne; omega
  rw [List.prefix_iff_eq_take] at hL hpre
  rw [hL, hpre, hlen']

/-- Entries of a root path in index order are in betweenness order. -/
lemma btw_rpath_getElem (r u : V) {i k l : ℕ} (hik : i ≤ k) (hkl : k ≤ l)
    (hl : l < (rpath hT r u).length) :
    Btw T (rpath hT r u)[i] (rpath hT r u)[k] (rpath hT r u)[l] := by
  have hG := hT.connected
  have h1 := dist_getElem_le hG (rpath_isChain hT r u) hik (by omega)
  have h2 := dist_getElem_le hG (rpath_isChain hT r u) hkl hl
  have hi := dist_rpath_getElem hT r u (i := i) (by omega)
  have hl' := dist_rpath_getElem hT r u hl
  have h3 := hG.dist_triangle (u := r) (v := (rpath hT r u)[i]) (w := (rpath hT r u)[l])
  have h4 := hG.dist_triangle (u := (rpath hT r u)[i]) (v := (rpath hT r u)[k])
    (w := (rpath hT r u)[l])
  unfold Btw
  omega

end Tree

end TreeAA
