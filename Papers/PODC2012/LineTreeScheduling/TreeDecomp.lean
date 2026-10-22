import Papers.PODC2012.LineTreeScheduling.TreePath

/-!
# Tree decompositions and layered decompositions (Sections 4.1, 4.2, 4.4 and Appendix A)

Chakaravarthy, Roy, Sabharwal, *Distributed algorithms for scheduling on line and tree networks*,
PODC 2012 (arXiv:1205.1924v2).

* `RootedTree V` — a rooted tree `H` on the vertex set `V`, represented by the sets
  `sub z = C(z)` (`z` together with its descendants); `depth`, `IsLCA`, `lca`.
* `TreeDecomp T` — a tree decomposition of the tree network `T` (Section 4.1): the LCA property and
  connectivity (convexity) of every `C(z)`. The pivot set `χ(z) = Γ[C(z)]` is `nbhd T (H.sub z)`.
* `TreeDecomp.ofAdj` — a sufficient criterion: all `C(z)` convex and every edge of `T` joins an
  ancestor–descendant pair of `H` imply the LCA property.
* `LayeredDecomp T Δ ℓ` — layered decompositions (Section 4.4), for all demand pairs at once.
* `lemma_4_2` — Lemma 4.2: a tree decomposition of pivot size `θ` and depth `ℓ` yields a layered
  decomposition with critical set size `2(θ + 1)` and length `ℓ` (with the paper's construction).
* `rootFixing` — the root-fixing decomposition (Section 4.2) with pivot size 1
  (`card_nbhd_rootFixing_le`); `observation_A_1` — Observation A.1 (Appendix A).
-/

set_option linter.unusedSectionVars false

namespace Podc.LineTreeScheduling

open SimpleGraph Finset TreeAA

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ### Rooted trees -/

/-- A rooted tree `H` on the vertex set `V`, given by the sets `sub z = C(z)` consisting of `z` and
its descendants. The axioms say: `z ∈ C(z)`; the root is an ancestor-or-self of every node; the
ancestor-or-self relation `y ≼ x :↔ x ∈ C(y)` is a partial order (transitive, antisymmetric) whose
down-sets `{y | y ≼ x}` are chains. For finite `V` this is exactly a rooted tree on `V` (the parent of
`x ≠ root` is its deepest strict ancestor). -/
structure RootedTree (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The root `g`. -/
  root : V
  /-- `sub z = C(z)`: `z` and its descendants. -/
  sub : V → Finset V
  mem_sub_self : ∀ z, z ∈ sub z
  mem_sub_root : ∀ x, x ∈ sub root
  sub_subset_sub : ∀ {x y}, x ∈ sub y → sub x ⊆ sub y
  eq_of_mem_sub : ∀ {x y}, x ∈ sub y → y ∈ sub x → x = y
  mem_sub_or : ∀ {x y w}, w ∈ sub x → w ∈ sub y → x ∈ sub y ∨ y ∈ sub x

namespace RootedTree

variable (H : RootedTree V)

/-- The depth of `x`: the number of nodes on the path from the root to `x` (the root has depth 1),
i.e. the number of ancestors-or-self of `x`. -/
def depth (x : V) : ℕ := (univ.filter fun z => x ∈ H.sub z).card

lemma one_le_depth (x : V) : 1 ≤ H.depth x :=
  card_pos.2 ⟨x, by simp [H.mem_sub_self]⟩

lemma depth_le_of_mem_sub {x y : V} (h : x ∈ H.sub y) : H.depth y ≤ H.depth x :=
  card_le_card fun z hz => by
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact H.sub_subset_sub hz h

lemma depth_lt_of_mem_sub {x y : V} (h : x ∈ H.sub y) (hne : x ≠ y) : H.depth y < H.depth x := by
  refine card_lt_card ⟨fun z hz => ?_, fun hsub => ?_⟩
  · simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact H.sub_subset_sub hz h
  · have : x ∈ univ.filter fun z => y ∈ H.sub z := hsub (by simp [H.mem_sub_self])
    simp only [mem_filter, mem_univ, true_and] at this
    exact hne (H.eq_of_mem_sub h this)

lemma eq_of_mem_sub_of_depth_le {x y : V} (h : x ∈ H.sub y) (hd : H.depth x ≤ H.depth y) :
    x = y := by
  by_contra hne; have := H.depth_lt_of_mem_sub h hne; omega

/-- `l` is the least common ancestor(-or-self) of `x` and `y`. -/
def IsLCA (x y l : V) : Prop :=
  x ∈ H.sub l ∧ y ∈ H.sub l ∧ ∀ z, x ∈ H.sub z → y ∈ H.sub z → l ∈ H.sub z

lemma exists_isLCA (x y : V) : ∃ l, H.IsLCA x y l := by
  classical
  obtain ⟨l, hl, hmax⟩ := (univ.filter fun z => x ∈ H.sub z ∧ y ∈ H.sub z).exists_max_image
    H.depth ⟨H.root, by simp [H.mem_sub_root]⟩
  simp only [mem_filter, mem_univ, true_and, and_imp] at hl hmax
  refine ⟨l, hl.1, hl.2, fun z hx hy => ?_⟩
  rcases H.mem_sub_or hl.1 hx with h | h
  · exact h
  · rw [H.eq_of_mem_sub_of_depth_le h (hmax z hx hy)]; exact H.mem_sub_self l

lemma IsLCA.unique {H : RootedTree V} {x y l l' : V} (h : H.IsLCA x y l) (h' : H.IsLCA x y l') :
    l = l' :=
  H.eq_of_mem_sub (h.2.2 l' h'.1 h'.2.1) (h'.2.2 l h.1 h.2.1)

/-- The least common ancestor `LCA(x, y)` in `H`. -/
noncomputable def lca (x y : V) : V := (H.exists_isLCA x y).choose

lemma isLCA_lca (x y : V) : H.IsLCA x y (H.lca x y) := (H.exists_isLCA x y).choose_spec

end RootedTree

/-! ### Tree decompositions (Section 4.1) -/

/-- A **tree decomposition** of the tree network `T` (Section 4.1): a rooted tree `H` on `V` such
that (i) (LCA property) whenever the path between `a` and `b` passes through `x` and `y`, it also
passes through `LCA(x, y)`; (ii) every `C(z)` induces a connected subtree of `T` (in a tree:
`C(z)` is convex).

The paper requires (i) only for demand paths; we require it for the paths between all pairs of
vertices (every pair may carry a demand). -/
structure TreeDecomp (T : SimpleGraph V) where
  /-- The rooted tree `H`. -/
  H : RootedTree V
  lca_btw : ∀ a b x y, Btw T a x b → Btw T a y b → Btw T a (H.lca x y) b
  convex : ∀ z, TreeAA.Convex (T := T) (H.sub z : Set V)

variable {T : SimpleGraph V}

/-! ### Bending points -/

open Classical in
/-- The bending point of `path(a, b)` with respect to `u`: the vertex `y` of `path(a, b)` lying on the
path from `u` to every vertex of `path(a, b)` (see `bend_spec`, `bend_spec'` for the paper's
definition: the path from `u` to `y` meets `path(a, b)` only in `y`). -/
noncomputable def bend (T : SimpleGraph V) (a b u : V) : V :=
  haveI : Nonempty V := ⟨a⟩
  Classical.epsilon fun y => Btw T a y b ∧ ∀ x, Btw T a x b → Btw T u y x

lemma bend_spec (hT : T.IsTree) (a b u : V) :
    Btw T a (bend T a b u) b ∧ ∀ x, Btw T a x b → Btw T u (bend T a b u) x := by
  obtain ⟨y, hy, hg⟩ := exists_gate hT (convex_path hT a b) (btw_left a b) u
  have : Nonempty V := ⟨a⟩
  exact Classical.epsilon_spec (p := fun y => Btw T a y b ∧ ∀ x, Btw T a x b → Btw T u y x)
    ⟨y, hy, fun x hx => hg x hx⟩

/-- The paper's definition of the bending point: the path from `u` to `y` does not pass through any
other node of `path(a, b)`. -/
lemma bend_spec' (hT : T.IsTree) {a b u x : V} (hx : Btw T a x b)
    (hxu : Btw T u x (bend T a b u)) : x = bend T a b u :=
  eq_of_btw_btw hT hxu ((bend_spec hT a b u).2 x hx)

namespace TreeDecomp

variable (D : TreeDecomp T)

/-- The pivot set `χ(z) = Γ[C(z)]`. -/
noncomputable def pivot (z : V) : Finset V := nbhd T (D.H.sub z)

lemma exists_capture (a b : V) : ∃ z, Btw T a z b ∧ ∀ x, Btw T a x b → x ∈ D.H.sub z := by
  classical
  obtain ⟨w, hw, hmin⟩ := (univ.filter fun w => Btw T a w b).exists_min_image D.H.depth
    ⟨a, by simp [btw_left]⟩
  simp only [mem_filter, mem_univ, true_and] at hw hmin
  refine ⟨w, hw, fun x hx => ?_⟩
  have hl := D.H.isLCA_lca w x
  have hlb := D.lca_btw a b w x hw hx
  have := D.H.eq_of_mem_sub_of_depth_le hl.1 (hmin _ hlb)
  rw [this]; exact hl.2.1

/-- The capture node `µ(d)` of the demand path `d = path(a, b)`: the node of least depth in `H` among
the nodes of `path(d)` (see `depth_capture_le`, `eq_capture_of_depth_le`); equivalently, the node of
`path(d)` with `path(d) ⊆ C(µ(d))`. -/
noncomputable def capture (a b : V) : V := (D.exists_capture a b).choose

lemma capture_btw (a b : V) : Btw T a (D.capture a b) b := (D.exists_capture a b).choose_spec.1

lemma mem_sub_capture {a b x : V} (hx : Btw T a x b) : x ∈ D.H.sub (D.capture a b) :=
  (D.exists_capture a b).choose_spec.2 x hx

lemma depth_capture_le {a b x : V} (hx : Btw T a x b) :
    D.H.depth (D.capture a b) ≤ D.H.depth x :=
  D.H.depth_le_of_mem_sub (D.mem_sub_capture hx)

/-- The capture node is the *unique* node of least depth on the path. -/
lemma eq_capture_of_depth_le {a b x : V} (hx : Btw T a x b)
    (hd : D.H.depth x ≤ D.H.depth (D.capture a b)) : x = D.capture a b :=
  D.H.eq_of_mem_sub_of_depth_le (D.mem_sub_capture hx) hd

/-- The group index of `d = (a, b)` (0-based): `ℓ - depth(µ(d))`, so demands captured at the deepest
nodes come first and demands captured at the root (depth 1) come last (index `ℓ - 1`, the paper's
`G_ℓ`). -/
noncomputable def grp (ℓ : ℕ) (a b : V) : ℕ := ℓ - D.H.depth (D.capture a b)

/-- The critical set `π(d)` of Lemma 4.2: the wings of `z = µ(d)` on `path(d)`, together with, for
each pivot `u ∈ χ(z)`, the wings of the bending point of `d` with respect to `u`. -/
noncomputable def crit (a b : V) : Finset (Sym2 V) :=
  wings T a b (D.capture a b) ∪
    (nbhd T (D.H.sub (D.capture a b))).biUnion fun u => wings T a b (bend T a b u)

end TreeDecomp

/-! ### Layered decompositions (Section 4.4) -/

/-- Layered decomposition of a tree network (Section 4.4), for all demand pairs `(a, b)` at once.
Groups are 0-based: group 0 is processed first (the paper's `G_1`). `crit a b` is the critical set
`π(d)` (a subset of `path(d)` of size `≤ Δ`); `prop` is the defining property: if `d₁ ∈ G_i`,
`d₂ ∈ G_j`, `i ≤ j` overlap, then `path(d₂)` contains a critical edge of `d₁`. -/
structure LayeredDecomp (T : SimpleGraph V) (Δ ℓ : ℕ) where
  grp : V → V → ℕ
  crit : V → V → Finset (Sym2 V)
  grp_lt : ∀ a b, grp a b < ℓ
  crit_subset : ∀ a b, crit a b ⊆ pathEdges T a b
  card_crit : ∀ a b, (crit a b).card ≤ Δ
  prop : ∀ a₁ b₁ a₂ b₂, grp a₁ b₁ ≤ grp a₂ b₂ →
    (pathEdges T a₁ b₁ ∩ pathEdges T a₂ b₂).Nonempty → (crit a₁ b₁ ∩ pathEdges T a₂ b₂).Nonempty

namespace TreeDecomp

variable (hT : T.IsTree) (D : TreeDecomp T) {θ ℓ : ℕ}

lemma crit_subset (a b : V) : D.crit a b ⊆ pathEdges T a b :=
  union_subset (wings_subset a b _) (biUnion_subset.2 fun _ _ => wings_subset a b _)

include hT in
lemma card_crit_le (hθ : ∀ z, (nbhd T (D.H.sub z)).card ≤ θ) (a b : V) :
    (D.crit a b).card ≤ 2 * (θ + 1) := by
  refine (card_union_le _ _).trans ?_
  have h1 := card_wings_le hT a b (D.capture a b)
  have h2 : ((nbhd T (D.H.sub (D.capture a b))).biUnion
      fun u => wings T a b (bend T a b u)).card ≤ 2 * θ := by
    refine card_biUnion_le.trans ?_
    calc ∑ u ∈ nbhd T (D.H.sub (D.capture a b)), (wings T a b (bend T a b u)).card
        ≤ ∑ _u ∈ nbhd T (D.H.sub (D.capture a b)), 2 :=
          sum_le_sum fun u _ => card_wings_le hT a b _
      _ = 2 * (nbhd T (D.H.sub (D.capture a b))).card := by rw [sum_const, smul_eq_mul, mul_comm]
      _ ≤ 2 * θ := Nat.mul_le_mul_left 2 (hθ _)
  omega

include hT in
/-- The key property of the critical sets (the two cases of the proof of Lemma 4.2): if `d₁` and
`d₂` overlap and `µ(d₂)` is not deeper than `µ(d₁)`, then `path(d₂)` contains a critical edge of
`d₁`. -/
lemma crit_prop {a₁ b₁ a₂ b₂ : V}
    (hd : D.H.depth (D.capture a₂ b₂) ≤ D.H.depth (D.capture a₁ b₁))
    (hov : (pathEdges T a₁ b₁ ∩ pathEdges T a₂ b₂).Nonempty) :
    (D.crit a₁ b₁ ∩ pathEdges T a₂ b₂).Nonempty := by
  set z₁ := D.capture a₁ b₁
  set z₂ := D.capture a₂ b₂
  by_cases hz : z₂ ∈ D.H.sub z₁
  · -- Case 1: `z₂ = z₁`, and `path(d₂)` contains a wing of `z₁`.
    have hzz : z₂ = z₁ := D.H.eq_of_mem_sub_of_depth_le hz hd
    have h₂ : Btw T a₂ z₁ b₂ := hzz ▸ D.capture_btw a₂ b₂
    exact (wings_inter_nonempty hT hov (D.capture_btw a₁ b₁) h₂).mono
      (inter_subset_inter_right subset_union_left)
  · -- Case 2: `path(d₂)` leaves `C(z₁)` through a pivot `u`, hence passes through the bending point.
    obtain ⟨e, he⟩ := hov
    obtain ⟨p, hp⟩ : ∃ p, p ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
    rw [mem_inter, mem_pathEdges, mem_pathEdges] at he
    have hp₁ := he.1.2 p hp
    have hp₂ := he.2.2 p hp
    obtain ⟨u, hu, hpu⟩ := exists_nbhd_btw hT (D.mem_sub_capture hp₁) hz
    have hu₂ : Btw T a₂ u b₂ := convex_path hT a₂ b₂ p hp₂ z₂ (D.capture_btw a₂ b₂) u hpu
    set y := bend T a₁ b₁ u
    have hy₁ : Btw T a₁ y b₁ := (bend_spec hT a₁ b₁ u).1
    have hy₂ : Btw T a₂ y b₂ :=
      convex_path hT a₂ b₂ u hu₂ p hp₂ y ((bend_spec hT a₁ b₁ u).2 p hp₁)
    have hov' : (pathEdges T a₁ b₁ ∩ pathEdges T a₂ b₂).Nonempty :=
      ⟨e, mem_inter.2 ⟨mem_pathEdges.2 he.1, mem_pathEdges.2 he.2⟩⟩
    refine (wings_inter_nonempty hT hov' hy₁ hy₂).mono (inter_subset_inter_right ?_)
    exact (subset_biUnion_of_mem (fun u => wings T a₁ b₁ (bend T a₁ b₁ u)) hu).trans
      subset_union_right

/-- The layered decomposition built from a tree decomposition in the proof of Lemma 4.2. -/
noncomputable def toLayered (hθ : ∀ z, (nbhd T (D.H.sub z)).card ≤ θ)
    (hℓ : ∀ x, D.H.depth x ≤ ℓ) : LayeredDecomp T (2 * (θ + 1)) ℓ where
  grp := D.grp ℓ
  crit := D.crit
  grp_lt a b := by
    have h1 := D.H.one_le_depth (D.capture a b)
    have h2 := hℓ (D.capture a b)
    unfold grp; omega
  crit_subset := D.crit_subset
  card_crit := D.card_crit_le hT hθ
  prop a₁ b₁ a₂ b₂ hg hov := by
    have h1 := hℓ (D.capture a₁ b₁)
    have h2 := hℓ (D.capture a₂ b₂)
    unfold grp at hg
    exact D.crit_prop hT (by omega) hov

end TreeDecomp

/-- **Lemma 4.2.** A tree decomposition `H` of a tree network `T` with pivot size `θ` and depth `ℓ`
can be transformed into a layered decomposition with critical set size `Δ = 2(θ + 1)` and length `ℓ`:
group `d` by the (reversed) depth of its capture node `µ(d)` and take `π(d)` = the wings of `µ(d)`
and of the bending points of `d` w.r.t. the pivots of `µ(d)`. -/
theorem lemma_4_2 (hT : T.IsTree) (D : TreeDecomp T) {θ ℓ : ℕ}
    (hθ : ∀ z, (nbhd T (D.H.sub z)).card ≤ θ) (hℓ : ∀ x, D.H.depth x ≤ ℓ) :
    ∃ L : LayeredDecomp T (2 * (θ + 1)) ℓ, L.grp = D.grp ℓ ∧ L.crit = D.crit :=
  ⟨D.toLayered hT hθ hℓ, rfl, rfl⟩

/-! ### A sufficient criterion for the LCA property -/

namespace TreeDecomp

-- CSLib candidate
/-- If every `C(z)` is convex in `T` and every edge of `T` joins an ancestor–descendant pair of `H`,
then the LCA property holds: the path between two nodes `x`, `y` passes through `LCA(x, y)`. -/
lemma btw_lca_of_adj (hT : T.IsTree) (H : RootedTree V)
    (hconv : ∀ z, TreeAA.Convex (T := T) (H.sub z : Set V))
    (hadj : ∀ x y, T.Adj x y → x ∈ H.sub y ∨ y ∈ H.sub x) (x y : V) :
    Btw T x (H.lca x y) y := by
  set l := H.lca x y
  have hl := H.isLCA_lca x y
  by_contra hn
  -- every vertex `v` of `path(x, y)` lies with `x` in some `C(c)`, `c ≠ l` a descendant of `l`
  have key : ∀ n, ∀ v, Btw T x v y → T.dist x v = n →
      ∃ c ∈ H.sub l, c ≠ l ∧ x ∈ H.sub c ∧ v ∈ H.sub c := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro v hv hn'
    have hvl : v ≠ l := by rintro rfl; exact hn hv
    have hvsub : v ∈ H.sub l := hconv l x hl.1 y hl.2.1 v hv
    by_cases hxv : x = v
    · subst hxv; exact ⟨x, hl.1, hvl, H.mem_sub_self x, H.mem_sub_self x⟩
    obtain ⟨w, hwv, hw⟩ := exists_pred hT hxv
    have hwy : Btw T x w y := hv.trans hT.connected hw
    have hd := dist_eq_add_one_of_adj hwv hw
    obtain ⟨c, hcl, hcne, hxc, hwc⟩ := ih _ (by omega) w hwy rfl
    rcases hadj w v hwv with h | h
    · rcases H.mem_sub_or hwc h with h' | h'
      · exact ⟨v, hvsub, hvl, H.sub_subset_sub h' hxc, H.mem_sub_self v⟩
      · exact ⟨c, hcl, hcne, hxc, H.sub_subset_sub h' (H.mem_sub_self v)⟩
    · exact ⟨c, hcl, hcne, hxc, H.sub_subset_sub hwc h⟩
  obtain ⟨c, hcl, hcne, hxc, hyc⟩ := key _ y (btw_right x y) rfl
  exact hcne (H.eq_of_mem_sub hcl (hl.2.2 c hxc hyc))

/-- A rooted tree whose sets `C(z)` are convex and in which every edge of `T` joins an
ancestor–descendant pair is a tree decomposition of `T`. -/
noncomputable def ofAdj (hT : T.IsTree) (H : RootedTree V)
    (hconv : ∀ z, TreeAA.Convex (T := T) (H.sub z : Set V))
    (hadj : ∀ x y, T.Adj x y → x ∈ H.sub y ∨ y ∈ H.sub x) : TreeDecomp T where
  H := H
  lca_btw a b x y hx hy := convex_path hT a b x hx y hy _ (btw_lca_of_adj hT H hconv hadj x y)
  convex := hconv

end TreeDecomp

/-! ### The root-fixing decomposition (Section 4.2) and Observation A.1 (Appendix A) -/

section RootFixing

variable (hT : T.IsTree)
include hT

lemma btw_or_btw_of_btw {g x y w : V} (hx : Btw T g x w) (hy : Btw T g y w) :
    Btw T g x y ∨ Btw T g y x := by
  rcases btw_or hT hx y with h | h
  · exact Or.inl h
  · exact Or.inr (hy.left_of_trans' hT.connected h)

/-- The rooted tree obtained by rooting `T` at `g`: `C(z) = {x | z lies on the path from g to x}`. -/
noncomputable def rootFixingTree (g : V) : RootedTree V where
  root := g
  sub z := by classical exact univ.filter fun x => Btw T g z x
  mem_sub_self z := by simp [btw_right]
  mem_sub_root x := by simp [btw_left]
  sub_subset_sub {x y} h w hw := by
    simp only [mem_filter, mem_univ, true_and] at h hw ⊢
    exact hw.trans hT.connected h
  eq_of_mem_sub {x y} h h' := by
    simp only [mem_filter, mem_univ, true_and] at h h'
    exact eq_of_btw_btw hT h' h
  mem_sub_or {x y w} hx hy := by
    simp only [mem_filter, mem_univ, true_and] at hx hy ⊢
    exact (btw_or_btw_of_btw hT hx hy).symm

lemma mem_rootFixingTree_sub {g z x : V} : x ∈ (rootFixingTree hT g).sub z ↔ Btw T g z x := by
  simp [rootFixingTree]

lemma convex_rootFixing_aux {g z x y w : V} (hx : Btw T g z x) (hy : Btw T g z y)
    (hw : Btw T x w y) (hwy : Btw T g w y) : Btw T g z w := by
  rcases btw_or_btw_of_btw hT hy hwy with h | h
  · exact h
  · have hG := hT.connected
    have t1 := hG.dist_triangle (u := x) (v := z) (w := y)
    have t2 := hG.dist_triangle (u := g) (v := w) (w := x)
    have c1 := dist_comm (G := T) (u := w) (v := x)
    have c2 := dist_comm (G := T) (u := x) (v := z)
    unfold TreeAA.Btw at hx hy hw hwy h
    have : T.dist w z = 0 := by omega
    rw [(hG.dist_eq_zero_iff).1 this]; exact btw_right g z

/-- The **root-fixing decomposition** (Section 4.2): `T` rooted at an arbitrary node `g`. -/
noncomputable def rootFixing (g : V) : TreeDecomp T :=
  TreeDecomp.ofAdj hT (rootFixingTree hT g)
    (fun z x hx y hy w hw => by
      simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq, rootFixingTree] at hx hy ⊢
      rcases btw_or hT hw g with h | h
      · exact convex_rootFixing_aux hT hy hx hw.symm h.symm
      · exact convex_rootFixing_aux hT hx hy hw h)
    (fun x y hxy => by
      simp only [mem_rootFixingTree_sub]
      exact (btw_or_of_adj hT hxy g).symm)

/-- The root-fixing decomposition has pivot size `θ = 1`: `Γ[C(z)]` consists at most of the parent
of `z`. -/
lemma card_nbhd_rootFixing_le (g z : V) : (nbhd T ((rootFixing hT g).H.sub z)).card ≤ 1 := by
  classical
  have hsub : nbhd T ((rootFixing hT g).H.sub z) ⊆
      univ.filter fun u => T.Adj u z ∧ Btw T g u z := by
    intro u hu
    rw [mem_nbhd] at hu
    obtain ⟨hu, x, hx, hxu⟩ := hu
    simp only [rootFixing, TreeDecomp.ofAdj, mem_rootFixingTree_sub] at hu hx
    simp only [mem_filter, mem_univ, true_and]
    rcases btw_or_of_adj hT hxu g with h | h
    · exact absurd (h.trans hT.connected hx) hu
    · rcases btw_or_btw_of_btw hT hx h with h' | h'
      · exact absurd h' hu
      · have hd := dist_eq_add_one_of_adj hxu.symm h
        have hzu : u ≠ z := by rintro rfl; exact hu (btw_right g u)
        unfold TreeAA.Btw at hx h'
        have hdz : T.dist u z ≠ 0 := fun h0 => hzu ((hT.connected.dist_eq_zero_iff).1 h0)
        have : T.dist u z = 1 := by omega
        exact ⟨dist_eq_one_iff_adj.1 this, h'⟩
  refine (card_le_card hsub).trans (card_le_one.2 fun u hu u' hu' => ?_)
  simp only [mem_filter, mem_univ, true_and] at hu hu'
  have e1 := dist_eq_add_one_of_adj hu.1 hu.2
  have e2 := dist_eq_add_one_of_adj hu'.1 hu'.2
  exact eq_of_btw_of_dist_eq' hT hu.2 hu'.2 (by omega)

omit hT in
/-- The capture node `µ(d)` in the root-fixing decomposition rooted at `g` (Appendix A): the node of
`path(d)` closest to `g` (= of least depth), i.e. the bending point of `d` w.r.t. `g`. -/
noncomputable def rfCapture (T : SimpleGraph V) (g a b : V) : V := bend T a b g

omit hT in
/-- The critical set of Appendix A: the wings of `µ(d)` on `path(d)` (at most two edges). -/
noncomputable def rfCrit (T : SimpleGraph V) (g a b : V) : Finset (Sym2 V) :=
  wings T a b (rfCapture T g a b)

lemma rfCapture_btw (g a b : V) : Btw T a (rfCapture T g a b) b := (bend_spec hT a b g).1

/-- `µ(d)` is the node of `path(d)` of least depth: it is an ancestor-or-self of every node of
`path(d)`. -/
lemma btw_rfCapture {g a b x : V} (hx : Btw T a x b) : Btw T g (rfCapture T g a b) x :=
  (bend_spec hT a b g).2 x hx

/-- The capture node of the root-fixing decomposition (Lemma 4.2's `µ`) is `rfCapture`. -/
lemma rootFixing_capture (g a b : V) : (rootFixing hT g).capture a b = rfCapture T g a b := by
  set D := rootFixing hT g
  have h1 : rfCapture T g a b ∈ D.H.sub (D.capture a b) := D.mem_sub_capture (rfCapture_btw hT g a b)
  have h2 : D.capture a b ∈ D.H.sub (rfCapture T g a b) := by
    simp only [D, rootFixing, TreeDecomp.ofAdj, mem_rootFixingTree_sub]
    exact btw_rfCapture hT (D.capture_btw a b)
  exact D.H.eq_of_mem_sub h2 h1

lemma card_rfCrit_le (g a b : V) : (rfCrit T g a b).card ≤ 2 := card_wings_le hT a b _

/-- **Observation A.1.** Let `T` be rooted at `g`, and let `d₁ = (a₁, b₁)`, `d₂ = (a₂, b₂)` be
overlapping demand paths. If `d₂` is captured at the capture node `z` of `d₁` or at an ancestor of `z`
(i.e. `µ(d₂)` lies on the path from `g` to `µ(d₁)`), then `path(d₂)` contains an edge of `π(d₁)`. -/
theorem observation_A_1 {g a₁ b₁ a₂ b₂ : V}
    (hov : (pathEdges T a₁ b₁ ∩ pathEdges T a₂ b₂).Nonempty)
    (hanc : Btw T g (rfCapture T g a₂ b₂) (rfCapture T g a₁ b₁)) :
    (rfCrit T g a₁ b₁ ∩ pathEdges T a₂ b₂).Nonempty := by
  obtain ⟨e, he⟩ := id hov
  obtain ⟨p, hp⟩ : ∃ p, p ∈ e := ⟨e.out.1, Sym2.out_fst_mem e⟩
  rw [mem_inter, mem_pathEdges, mem_pathEdges] at he
  have hp₁ := he.1.2 p hp
  have hp₂ := he.2.2 p hp
  set z₁ := rfCapture T g a₁ b₁
  set z₂ := rfCapture T g a₂ b₂
  -- `z₁` lies on the path from `z₂` to `p`, hence on `path(d₂)`
  have h1 : Btw T g z₁ p := btw_rfCapture hT hp₁
  have h12 : Btw T z₂ z₁ p := by
    have t1 := hT.connected.dist_triangle (u := z₂) (v := z₁) (w := p)
    have t2 := hT.connected.dist_triangle (u := g) (v := z₂) (w := p)
    unfold TreeAA.Btw at h1 hanc ⊢
    omega
  have hz₁ : Btw T a₂ z₁ b₂ := convex_path hT a₂ b₂ z₂ (rfCapture_btw hT g a₂ b₂) p hp₂ z₁ h12
  exact wings_inter_nonempty hT hov (rfCapture_btw hT g a₁ b₁) hz₁

end RootFixing

end Podc.LineTreeScheduling
