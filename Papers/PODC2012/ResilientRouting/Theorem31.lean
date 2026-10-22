import Papers.PODC2012.ResilientRouting.Model
import Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree

/-!
# Theorem 3.1: every connected network has a 1-resilient forwarding pattern

The paper's algorithm (Section 3.2.1) is not specified precisely enough to be formalized (see
`differencies.md`). We prove Theorem 3.1 with a different, simple construction based on any
rooted spanning tree `T` of `G` with root `d` (e.g. a BFS tree).

For a vertex `v` let `Sub v` be its subtree. An *exit* of `Sub v` is a non-tree edge `zw` with
`z ∈ Sub v`; its *value* is the depth of the lowest common ancestor of `z` and `w` (`cd z w`).
The edge `zw` leaves `Sub u` (for an ancestor `u` of `z`) iff its value is `< depth u`
(`desc_iff_le_cd`). Every vertex `v` fixes an exit `X v` of minimum value `low v`, and its
*escape hop* `esc v`: the other endpoint of `X v` if `X v` starts at `v`, otherwise the child of `v`
towards the start of `X v`.

Forwarding at `v ≠ d` (`next`):
* packet from the parent (*down mode*): to `esc v` if `v` has an exit and that link is up, else
  back to the parent;
* any other packet (*up mode*): to the parent if that link is up; otherwise to `esc v` if
  `low v < depth v` (the parent link is not a bridge); otherwise drop it.

With at most one failed link, up-mode packets climb to `d`; if the failed link is the parent link
of `u`, a packet climbing into `u` follows escape hops down `Sub u` (all minimal exits have the
same value `low u`, so the descent ends at an exit leaving `Sub u`) and then climbs to `d` on a
path that avoids `Sub u`. If the parent link of `u` is a bridge, `Sub u` is cut off and packets
there are dropped at `u`. Down-mode packets descend and then switch to up mode. All trajectories
terminate, so there are no forwarding loops.
-/

namespace Podc.ResilientRouting.OneResilient

open SimpleGraph Classical

variable {V : Type*} {G : SimpleGraph V} (T : G.RootedTree)

/-! ### Subtrees -/

/-- `z` lies in the subtree of `a` (`a` is an ancestor of `z`, or `z` itself). -/
def Desc (a z : V) : Prop := ∃ k, T.parent^[k] z = a

variable {T}

theorem desc_refl (a : V) : Desc T a a := ⟨0, rfl⟩

theorem desc_parent (z : V) : Desc T (T.parent z) z := ⟨1, rfl⟩

theorem Desc.trans {u a z : V} (h1 : Desc T u a) (h2 : Desc T a z) : Desc T u z := by
  obtain ⟨m, rfl⟩ := h1
  obtain ⟨k, rfl⟩ := h2
  exact ⟨m + k, Function.iterate_add_apply _ _ _ _⟩

theorem Desc.depth_le {a z : V} (h : Desc T a z) : T.depth a ≤ T.depth z := by
  obtain ⟨k, rfl⟩ := h
  rw [RootedTree.depth_iterate]; omega

theorem Desc.eq_iterate {a z : V} (h : Desc T a z) :
    T.parent^[T.depth z - T.depth a] z = a := by
  obtain ⟨k, hk⟩ := h
  by_cases ha : a = T.root
  · subst ha
    rw [T.depth_root, Nat.sub_zero, RootedTree.iterate_depth]
  · have := RootedTree.depth_of_iterate_eq hk ha
    rw [show T.depth z - T.depth a = k by omega, hk]

theorem desc_root (z : V) : Desc T T.root z := ⟨T.depth z, RootedTree.iterate_depth z⟩

theorem eq_root_of_desc_root {a : V} (h : Desc T a T.root) : a = T.root := by
  have := h.depth_le
  rw [T.depth_root] at this
  exact RootedTree.depth_eq_zero_iff.1 (by omega)

/-- Ancestors of a vertex are totally ordered by depth. -/
theorem desc_of_desc {u a z : V} (ha : Desc T a z) (hu : Desc T u z)
    (h : T.depth u ≤ T.depth a) : Desc T u a := by
  have h1 := ha.eq_iterate
  have h2 := hu.eq_iterate
  have hle := ha.depth_le
  have hu' := hu.depth_le
  refine ⟨T.depth a - T.depth u, ?_⟩
  have e : T.parent^[T.depth a - T.depth u] a =
      T.parent^[T.depth a - T.depth u] (T.parent^[T.depth z - T.depth a] z) := by rw [h1]
  rw [e, ← Function.iterate_add_apply, show T.depth a - T.depth u + (T.depth z - T.depth a) =
    T.depth z - T.depth u by omega, h2]

theorem Desc.parent_of_ne {u z : V} (h : Desc T u z) (hz : z ≠ u) : Desc T u (T.parent z) := by
  have h1 := h.eq_iterate
  have hk : T.depth z - T.depth u ≠ 0 := by
    intro h0; rw [h0] at h1; exact hz h1
  refine ⟨T.depth z - T.depth u - 1, ?_⟩
  rw [← Function.iterate_succ_apply, show (T.depth z - T.depth u - 1).succ =
    T.depth z - T.depth u by omega, h1]

theorem ne_parent_parent {v : V} (hv : v ≠ T.root) : v ≠ T.parent (T.parent v) := by
  intro h
  have h1 := RootedTree.depth_parent_lt hv
  by_cases hp : T.parent v = T.root
  · rw [hp, T.parent_root] at h; exact hv h
  · have h2 := RootedTree.depth_parent_lt hp
    rw [← h] at h2; omega

theorem not_desc_of_depth_lt {a z : V} (h : T.depth z < T.depth a) : ¬ Desc T a z :=
  fun h' => absurd h'.depth_le (by omega)

/-! ### Exits -/

variable [Fintype V] (T)

/-- A link that is not a tree edge. -/
def NonTree (z w : V) : Prop := G.Adj z w ∧ w ≠ T.parent z ∧ z ≠ T.parent w

/-- The depth of the lowest common ancestor of `z` and `w`. -/
noncomputable def cd (z w : V) : ℕ :=
  (Finset.univ.filter fun a => Desc T a z ∧ Desc T a w).sup T.depth

/-- The exits of the subtree of `v`: non-tree links `zw` with `z` in the subtree. -/
noncomputable def exits (v : V) : Finset (V × V) :=
  Finset.univ.filter fun p => Desc T v p.1 ∧ NonTree T p.1 p.2

/-- The subtree of `v` has an exit. -/
def HasExit (v : V) : Prop := (exits T v).Nonempty

/-- A minimum-value exit of the subtree of `v`. -/
noncomputable def X (v : V) : V × V :=
  if h : HasExit T v then (Finset.exists_min_image _ (fun p => cd T p.1 p.2) h).choose else (v, v)

/-- The minimum value of an exit of the subtree of `v`. -/
noncomputable def low (v : V) : ℕ := cd T (X T v).1 (X T v).2

/-- The escape hop of `v`. -/
noncomputable def esc (v : V) : V :=
  if (X T v).1 = v then (X T v).2 else T.parent^[T.depth (X T v).1 - T.depth v - 1] (X T v).1

variable {T}

theorem desc_iff_le_cd {u z w : V} (hz : Desc T u z) : Desc T u w ↔ T.depth u ≤ cd T z w := by
  constructor
  · intro hw
    exact Finset.le_sup (f := T.depth) (Finset.mem_filter.2 ⟨Finset.mem_univ _, hz, hw⟩)
  · intro h
    obtain ⟨a, ha, he⟩ := Finset.exists_mem_eq_sup
      (Finset.univ.filter fun a => Desc T a z ∧ Desc T a w)
      ⟨T.root, Finset.mem_filter.2 ⟨Finset.mem_univ _, desc_root z, desc_root w⟩⟩ T.depth
    obtain ⟨-, haz, haw⟩ := Finset.mem_filter.1 ha
    rw [cd, he] at h
    exact (desc_of_desc haz hz h).trans haw

theorem X_spec {v : V} (h : HasExit T v) :
    X T v ∈ exits T v ∧ ∀ p ∈ exits T v, low T v ≤ cd T p.1 p.2 := by
  have hs := (Finset.exists_min_image _ (fun p => cd T p.1 p.2) h).choose_spec
  simp only [low, X, dite_eq_left_of_eq_true (eq_true h)]
  exact hs

theorem X_mem {v : V} (h : HasExit T v) : Desc T v (X T v).1 ∧ NonTree T (X T v).1 (X T v).2 := by
  have := (X_spec h).1
  simp only [exits, Finset.mem_filter] at this
  exact this.2

theorem esc_of_eq {v : V} (h : HasExit T v) (he : (X T v).1 = v) :
    esc T v = (X T v).2 ∧ NonTree T v (esc T v) := by
  have : esc T v = (X T v).2 := by simp [esc, he]
  refine ⟨this, ?_⟩
  have hx := (X_mem h).2
  rw [he] at hx
  rw [this]
  exact hx

theorem esc_of_ne {v : V} (h : HasExit T v) (he : (X T v).1 ≠ v) :
    T.parent (esc T v) = v ∧ esc T v ≠ T.root ∧ Desc T (esc T v) (X T v).1 ∧
      T.depth (esc T v) = T.depth v + 1 := by
  have hd := (X_mem h).1
  have h1 := hd.eq_iterate
  have hle := hd.depth_le
  have hk : T.depth (X T v).1 - T.depth v ≠ 0 := by
    intro h0; rw [h0] at h1; exact he h1
  have hesc : esc T v = T.parent^[T.depth (X T v).1 - T.depth v - 1] (X T v).1 := by
    simp [esc, he]
  have hdep : T.depth (esc T v) = T.depth v + 1 := by
    rw [hesc, RootedTree.depth_iterate]; omega
  refine ⟨?_, ?_, ⟨_, hesc.symm⟩, hdep⟩
  · rw [hesc, ← Function.iterate_succ_apply' T.parent, show (T.depth (X T v).1 - T.depth v - 1).succ =
      T.depth (X T v).1 - T.depth v by omega, h1]
  · intro hr; rw [hr, T.depth_root] at hdep; omega

theorem adj_esc {v : V} (h : HasExit T v) : G.Adj v (esc T v) := by
  by_cases he : (X T v).1 = v
  · exact (esc_of_eq h he).2.1
  · obtain ⟨hp, hr, -⟩ := esc_of_ne h he
    have := T.adj_parent _ hr
    rw [hp] at this
    exact this.symm

theorem esc_ne_parent {v : V} (h : HasExit T v) (hv : v ≠ T.root) : esc T v ≠ T.parent v := by
  by_cases he : (X T v).1 = v
  · exact (esc_of_eq h he).2.2.1
  · obtain ⟨hp, -⟩ := esc_of_ne h he
    intro h'
    exact ne_parent_parent hv (by rw [← h', hp])

theorem exits_mono {v c : V} (h : Desc T v c) : exits T c ⊆ exits T v := by
  intro p hp
  simp only [exits, Finset.mem_filter] at hp ⊢
  exact ⟨hp.1, h.trans hp.2.1, hp.2.2⟩

theorem chain_step {v : V} (h : HasExit T v) (he : (X T v).1 ≠ v) :
    HasExit T (esc T v) ∧ low T (esc T v) = low T v := by
  obtain ⟨hp, -, hd, -⟩ := esc_of_ne h he
  have hmem : X T v ∈ exits T (esc T v) := by
    simp only [exits, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hd, (X_mem h).2⟩
  have hc : HasExit T (esc T v) := ⟨_, hmem⟩
  refine ⟨hc, le_antisymm ((X_spec hc).2 _ hmem) ?_⟩
  have hpd : Desc T v (esc T v) := by
    have := desc_parent (T := T) (esc T v); rwa [hp] at this
  exact (X_spec h).2 _ (exits_mono hpd (X_spec hc).1)

/-- The subtree of `u` is closed under the links that survive when the parent link of `u` fails,
unless it has an exit leaving it (value `< depth u`). -/
theorem bridge {F : Set (Sym2 V)} {u : V} (hur : u ≠ T.root) (hu : s(u, T.parent u) ∈ F)
    (hbad : ¬ (HasExit T u ∧ low T u < T.depth u)) {i : V} (hi : Desc T u i) :
    ¬ (G.deleteEdges F).Reachable i T.root := by
  have closed : ∀ z w, Desc T u z → (G.deleteEdges F).Adj z w → Desc T u w := by
    intro z w hz hzw
    rw [deleteEdges_adj] at hzw
    by_cases h1 : w = T.parent z
    · subst h1
      by_cases hzu : z = u
      · subst hzu; exact absurd hu hzw.2
      · exact hz.parent_of_ne hzu
    by_cases h2 : z = T.parent w
    · subst h2; exact hz.trans (desc_parent w)
    by_contra hw
    have hmem : (z, w) ∈ exits T u := by
      simp only [exits, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hz, hzw.1, h1, h2⟩
    have hex : HasExit T u := ⟨_, hmem⟩
    have := (X_spec hex).2 _ hmem
    have hlt : cd T z w < T.depth u := by
      by_contra hc; exact hw ((desc_iff_le_cd hz).2 (by omega))
    exact hbad ⟨hex, by simp only at this; omega⟩
  rintro ⟨p⟩
  have key : ∀ {x y : V} (p : (G.deleteEdges F).Walk x y), Desc T u x → Desc T u y := by
    intro x y p
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun hx => ih (closed _ _ hx h)
  exact hur (eq_root_of_desc_root (key p hi))

/-! ### The forwarding pattern -/

variable (T)

/-- The forwarding function of the pattern built from `T` (see the module docstring). -/
noncomputable def fwd (v : V) (A : Set V) (x : V) : V :=
  if v = T.root then x
  else if x = T.parent v then (if HasExit T v ∧ esc T v ∈ A then esc T v else T.parent v)
  else if T.parent v ∈ A then T.parent v
  else if HasExit T v ∧ low T v < T.depth v then esc T v
  else T.parent v

/-- The forwarding pattern built from the rooted spanning tree `T`. -/
noncomputable def pattern : Pattern G where
  next := fwd T
  adj_next i A u hu := by
    unfold fwd
    by_cases h1 : i = T.root
    · simpa [h1] using hu
    have hp := T.adj_parent i h1
    simp only [h1, ↓reduceIte]
    split_ifs with h2 h3 h4 h5
    exacts [adj_esc h3.1, hp, hp, adj_esc h5.1, hp]

variable {T}

theorem fwd_up {v x : V} (hv : v ≠ T.root) (hx : x ≠ T.parent v) {A : Set V}
    (hA : T.parent v ∈ A) : fwd T v A x = T.parent v := by
  simp [fwd, hv, hx, hA]

theorem fwd_esc {v x : V} (hv : v ≠ T.root) (hx : x ≠ T.parent v) {A : Set V}
    (hA : T.parent v ∉ A) (h : HasExit T v ∧ low T v < T.depth v) : fwd T v A x = esc T v := by
  simp [fwd, hv, hx, hA, h]

theorem fwd_drop {v x : V} (hv : v ≠ T.root) (hx : x ≠ T.parent v) {A : Set V}
    (hA : T.parent v ∉ A) (h : ¬ (HasExit T v ∧ low T v < T.depth v)) :
    fwd T v A x = T.parent v := by
  simp only [fwd, hv, hx, hA, h, ↓reduceIte]

theorem fwd_down {v : V} (hv : v ≠ T.root) {A : Set V} (h : HasExit T v ∧ esc T v ∈ A) :
    fwd T v A (T.parent v) = esc T v := by
  simp only [fwd, hv, h, and_self, ↓reduceIte]

theorem fwd_down' {v : V} (hv : v ≠ T.root) {A : Set V} (h : ¬ (HasExit T v ∧ esc T v ∈ A)) :
    fwd T v A (T.parent v) = T.parent v := by
  simp only [fwd, hv, h, ↓reduceIte]

/-! ### Trajectories -/

section Dynamics

variable {F : Set (Sym2 V)}

theorem nxt_eq (x v : V) : nxt G (pattern T) F (x, v) = (v, fwd T v (view G F v) x) := rfl

theorem deliv_step {x v y : V} (hv : v ≠ T.root) (hn : fwd T v (view G F v) x = y)
    (hl : Live G F v y) (h : Delivers G T.root (pattern T) F (v, y)) :
    Delivers G T.root (pattern T) F (x, v) := by
  refine .step ?_ ?_
  · simp only [Stops, nxt_eq, hn, not_or, not_not]; exact ⟨hv, hl⟩
  · rwa [nxt_eq, hn]

theorem term_step {x v y : V} (hn : fwd T v (view G F v) x = y)
    (h : Terminates G T.root (pattern T) F (v, y)) : Terminates G T.root (pattern T) F (x, v) :=
  .step (by rwa [nxt_eq, hn])

theorem term_stop {x v y : V} (hn : fwd T v (view G F v) x = y) (hl : ¬ Live G F v y) :
    Terminates G T.root (pattern T) F (x, v) :=
  .base (Or.inr (by rwa [nxt_eq, hn]))

/-- Packets in up mode climb the tree while parent links are up. -/
theorem climb (P : V × V → Prop)
    (hstep : ∀ x v y, v ≠ T.root → fwd T v (view G F v) x = y → Live G F v y → P (v, y) →
      P (x, v))
    (hroot : ∀ x, P (x, T.root)) (B : V → Prop)
    (hB : ∀ v, B v → ∀ x, x ≠ T.parent v → P (x, v)) :
    ∀ v, (∀ a, Desc T a v → a ≠ T.root → ¬ B a → s(a, T.parent a) ∉ F) →
      ∀ x, x ≠ T.parent v → P (x, v) := by
  intro v
  induction hd : T.depth v using Nat.strong_induction_on generalizing v with
  | _ n ih =>
    intro hanc x hx
    by_cases hv : v = T.root
    · subst hv; exact hroot x
    by_cases hb : B v
    · exact hB v hb x hx
    have hl : Live G F v (T.parent v) := ⟨T.adj_parent v hv, hanc v (desc_refl v) hv hb⟩
    refine hstep x v _ hv (fwd_up hv hx hl) hl ?_
    exact ih (T.depth (T.parent v)) (hd ▸ RootedTree.depth_parent_lt hv) (T.parent v) rfl
      (fun a ha => hanc a (ha.trans (desc_parent v))) v (ne_parent_parent hv)

variable (T F) in
/-- The parent link of `u` has failed. -/
def Broken (u : V) : Prop := u ≠ T.root ∧ s(u, T.parent u) ∈ F

variable (hF1 : ∀ e ∈ F, ∀ e' ∈ F, e = e')
include hF1

omit [Fintype V] in
theorem broken_unique {u u' : V} (hu : Broken T F u) (hu' : Broken T F u') : u = u' :=
  RootedTree.edge_injective hu.1 hu'.1 (hF1 _ hu.2 _ hu'.2)

omit [Fintype V] in
theorem live_of_broken {u c y : V} (hu : Broken T F u) (hc : c ≠ u) (hc' : c ≠ T.parent u)
    (hadj : G.Adj c y) : Live G F c y := by
  refine ⟨hadj, fun h => ?_⟩
  have := hF1 _ h _ hu.2
  have hm : c ∈ s(u, T.parent u) := this ▸ Sym2.mem_mk_left c y
  rcases Sym2.mem_iff.1 hm with h' | h'
  exacts [hc h', hc' h']

omit hF1 in
/-- Up-mode packets below no failed parent link are delivered. -/
theorem deliver_up {v : V} (h : ∀ a, Desc T a v → ¬ Broken T F a) {x : V}
    (hx : x ≠ T.parent v) : Delivers G T.root (pattern T) F (x, v) :=
  climb (F := F) (Delivers G T.root (pattern T) F) (fun _ _ _ hv hn hl h => deliv_step hv hn hl h)
    (fun _ => .base rfl) (fun _ => False) (fun _ h => h.elim) v
    (fun a ha har _ hF => h a ha ⟨har, hF⟩) x hx

/-- The escape descent from a node whose parent link failed reaches an exit of its subtree. -/
theorem deliver_chain {u : V} (hu : Broken T F u) (hlow : low T u < T.depth u) :
    ∀ v, Desc T u v → HasExit T v → low T v = low T u →
      Delivers G T.root (pattern T) F (v, esc T v) := by
  intro v
  induction hc : (Finset.univ.filter (Desc T v)).card using Nat.strong_induction_on
    generalizing v with
  | _ n ih =>
    intro huv hv hlv
    by_cases he : (X T v).1 = v
    · obtain ⟨hesc, hnt⟩ := esc_of_eq hv he
      refine deliver_up (fun a ha hb => ?_) hnt.2.2
      have hau := broken_unique hF1 hb hu
      subst hau
      have hcd : cd T v (esc T v) = low T v := by simp only [low, hesc, he]
      have := (desc_iff_le_cd huv).1 ha
      omega
    · obtain ⟨hp, hr, -, hdep⟩ := esc_of_ne hv he
      obtain ⟨hcex, hclow⟩ := chain_step hv he
      have hdu := huv.depth_le
      have hcu : esc T v ≠ u := fun h => by rw [h] at hdep; omega
      have hcpu : esc T v ≠ T.parent u := fun h => by
        have := RootedTree.depth_parent_lt hu.1
        rw [h] at hdep; omega
      have hl : Live G F (esc T v) (esc T (esc T v)) := live_of_broken hF1 hu hcu hcpu (adj_esc hcex)
      have hn : fwd T (esc T v) (view G F (esc T v)) v = esc T (esc T v) := by
        have := fwd_down hr (A := view G F (esc T v)) ⟨hcex, hl⟩
        rwa [hp] at this
      have hpd : Desc T v (esc T v) := by
        have := desc_parent (T := T) (esc T v); rwa [hp] at this
      refine deliv_step hr hn hl (ih _ ?_ (esc T v) rfl (huv.trans hpd) hcex (hclow.trans hlv))
      rw [← hc]
      refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun z hz => ?_).2 ⟨v, ?_, ?_⟩)
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
        exact hpd.trans hz
      · simp [desc_refl]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact not_desc_of_depth_lt (by omega)

theorem live_esc_of_broken {u : V} (hu : Broken T F u) (hex : HasExit T u) :
    Live G F u (esc T u) :=
  ⟨adj_esc hex, fun h => esc_ne_parent hex hu.1 (Sym2.congr_right.1 (hF1 _ h _ hu.2))⟩

/-- Up-mode packets at a node whose parent link failed: escape if possible. -/
theorem deliver_broken {u : V} (hu : Broken T F u) (hex : HasExit T u)
    (hlow : low T u < T.depth u) {x : V} (hx : x ≠ T.parent u) :
    Delivers G T.root (pattern T) F (x, u) :=
  deliv_step hu.1 (fwd_esc hu.1 hx (fun h => h.2 hu.2) ⟨hex, hlow⟩)
    (live_esc_of_broken hF1 hu hex) (deliver_chain hF1 hu hlow u (desc_refl u) hex rfl)

/-- All up-mode trajectories terminate. -/
theorem term_up : ∀ v x, x ≠ T.parent v → Terminates G T.root (pattern T) F (x, v) := fun v =>
  climb (F := F) (Terminates G T.root (pattern T) F) (fun _ _ _ _ hn _ h => term_step hn h)
    (fun _ => .base (Or.inl rfl)) (Broken T F)
    (fun u hu x hx => by
      by_cases h : HasExit T u ∧ low T u < T.depth u
      · exact (deliver_broken hF1 hu h.1 h.2 hx).terminates
      · exact term_stop (fwd_drop hu.1 hx (fun h => h.2 hu.2) h) (fun h => h.2 hu.2))
    v (fun a _ har hb hF => hb ⟨har, hF⟩)

/-- All down-mode trajectories terminate. -/
theorem term_down : ∀ v, Terminates G T.root (pattern T) F (T.parent v, v) := by
  intro v
  induction hc : (Finset.univ.filter (Desc T v)).card using Nat.strong_induction_on
    generalizing v with
  | _ n ih =>
    by_cases hv : v = T.root
    · subst hv; exact .base (Or.inl rfl)
    by_cases h : HasExit T v ∧ esc T v ∈ view G F v
    · refine term_step (fwd_down hv h) ?_
      by_cases he : (X T v).1 = v
      · exact term_up hF1 _ _ (esc_of_eq h.1 he).2.2.2
      · obtain ⟨hp, -, -, hdep⟩ := esc_of_ne h.1 he
        have hpd : Desc T v (esc T v) := by
          have := desc_parent (T := T) (esc T v); rwa [hp] at this
        have := ih _ ?_ (esc T v) rfl
        · rwa [hp] at this
        rw [← hc]
        refine Finset.card_lt_card ((Finset.ssubset_iff_of_subset fun z hz => ?_).2 ⟨v, ?_, ?_⟩)
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
          exact hpd.trans hz
        · simp [desc_refl]
        · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact not_desc_of_depth_lt (by omega)
    · exact term_step (fwd_down' hv h) (term_up hF1 _ _ (ne_parent_parent hv))

theorem term_all (δ : V × V) : Terminates G T.root (pattern T) F δ := by
  obtain ⟨x, v⟩ := δ
  by_cases hx : x = T.parent v
  · subst hx; exact term_down hF1 v
  · exact term_up hF1 v x hx

/-- Every node connected to `d` has a first hop whose trajectory is delivered. -/
theorem deliver_first (i : V) (hi : i ≠ T.root) (hr : (G.deleteEdges F).Reachable i T.root) :
    ∃ y, Live G F i y ∧ Delivers G T.root (pattern T) F (i, y) := by
  by_cases hb : ∃ u, Broken T F u
  · obtain ⟨u, hu⟩ := hb
    by_cases hgood : HasExit T u ∧ low T u < T.depth u
    · by_cases hiu : i = u
      · subst hiu
        exact ⟨esc T i, live_esc_of_broken hF1 hu hgood.1,
          deliver_chain hF1 hu hgood.2 i (desc_refl i) hgood.1 rfl⟩
      · have hib : ¬ Broken T F i := fun h => hiu (broken_unique hF1 h hu)
        refine ⟨T.parent i, ⟨T.adj_parent i hi, fun h => hib ⟨hi, h⟩⟩, ?_⟩
        refine climb (F := F) (Delivers G T.root (pattern T) F)
          (fun _ _ _ hv hn hl h => deliv_step hv hn hl h) (fun _ => .base rfl) (Broken T F)
          (fun v hv x hx => ?_) (T.parent i) (fun a _ har hb hF => hb ⟨har, hF⟩) i
          (ne_parent_parent hi)
        have := broken_unique hF1 hv hu
        subst this
        exact deliver_broken hF1 hv hgood.1 hgood.2 hx
    · by_cases hdi : Desc T u i
      · exact absurd hr (bridge hu.1 hu.2 hgood hdi)
      · have hib : ¬ Broken T F i := fun h => hdi (broken_unique hF1 h hu ▸ desc_refl i)
        refine ⟨T.parent i, ⟨T.adj_parent i hi, fun h => hib ⟨hi, h⟩⟩,
          deliver_up (fun a ha hab => ?_) (ne_parent_parent hi)⟩
        have := broken_unique hF1 hab hu
        subst this
        exact hdi (ha.trans (desc_parent i))
  · push Not at hb
    exact ⟨T.parent i, ⟨T.adj_parent i hi, fun h => hb i ⟨hi, h⟩⟩,
      deliver_up (fun a _ => hb a) (ne_parent_parent hi)⟩

end Dynamics

/-- The pattern built from any rooted spanning tree with root `d` is 1-resilient. -/
theorem pattern_isResilient (T : G.RootedTree) : IsResilient G T.root (pattern T) 1 := by
  intro F _ hF
  have hF1 : ∀ e ∈ F, ∀ e' ∈ F, e = e' := fun e he e' he' =>
    Set.encard_le_one_iff.1 hF e e' he he'
  exact good_of (term_all hF1) (deliver_first hF1)

end Podc.ResilientRouting.OneResilient

namespace Podc.ResilientRouting

open SimpleGraph

/-- **Theorem 3.1** (existence part). Every connected network has a 1-resilient forwarding
pattern. -/
theorem theorem_3_1 {V : Type*} [Finite V] {G : SimpleGraph V} (hG : G.Connected) (d : V) :
    ∃ f : Pattern G, IsResilient G d f 1 := by
  have := Fintype.ofFinite V
  exact ⟨OneResilient.pattern (hG.bfsTree d), OneResilient.pattern_isResilient (hG.bfsTree d)⟩

end Podc.ResilientRouting
