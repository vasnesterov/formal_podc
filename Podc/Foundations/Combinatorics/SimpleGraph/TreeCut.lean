import Cslib.Foundations.Combinatorics.SimpleGraph.Shortcut
import Mathlib

-- CSLib candidate: Cslib/Foundations/Combinatorics/SimpleGraph/TreeCut.lean

/-!
# Cutting a rooted tree at congested edges

Fix a rooted spanning tree `T` of `G` and parts `P : ι → Finset V`. Tree edges are identified with
their lower endpoints (`v ↔ s(v, parent v)`, `v ≠ root`), so a set of tree edges is a
`Finset V`. Removing a set `O` of tree edges cuts `T` into a forest `T \ O`.

This is the combinatorial core of the shortcut constructions of Haeupler–Izumi–Zuzic (PODC'16,
`CoreSlow`: an edge is *unusable* if more than `2c` parts can see it) and Ghaffari–Haeupler
(PODC'21, *overcongested* edges): process the tree edges bottom-up and cut an edge if too many
parts meet its subtree in the forest cut so far. (`Papers/PODC2021/LowCongestionShortcuts/
Overcongested.lean` contains an earlier copy of the first half of this file.)

## Main definitions

* `Below T O v w`: `w` is a descendant of `v` in `T \ O` (the path up from `w` to `v` crosses
  no edge of `O`).
* `seenParts T P O v`: the parts meeting the `T \ O`-subtree of `v` (the parts `v`'s parent edge
  *can see*).
* `cutShortcut T P O i`: all edges `s(v, parent v)` with `v ∉ O` that can see part `i`, i.e. all
  ancestor edges of `P i` in `T \ O`.
* `cutTop T O x`: the top of `x`'s tree in the forest `T \ O` (the root, or an edge of `O`).

## Main results

* `exists_cut`, `cut_unique`: for a threshold `θ`, the bottom-up greedy yields the unique set `O`
  with `v ∈ O ↔ v ≠ root ∧ θ < |seenParts O v|`.
* `card_filter_mem_cutShortcut_le`, `restricts_cutShortcut`, `blocksMeetPart_cutShortcut`:
  congestion, tree-restriction and block structure of `cutShortcut`.
* `below_cutTop`, `eq_cutTop`: `cutTop O x` is the unique ancestor `t` of `x` in `T \ O` with
  `t = root ∨ t ∈ O`.
* `climb_cutShortcut_eq_cutTop`: from a vertex of `P i`, climbing along `cutShortcut P O i`
  ends at `cutTop O x`.
-/

set_option linter.unusedSectionVars false

namespace SimpleGraph

namespace RootedTree

open Finset

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  {G : SimpleGraph V} (T : G.RootedTree)

/-- `w` is a descendant of `v` in the forest `T \ O`: going up from `w` reaches `v` without
crossing a tree edge of `O` (tree edges are identified with their lower endpoints). -/
def Below (O : Finset V) (v w : V) : Prop :=
  ∃ n, T.parent^[n] w = v ∧ ∀ i < n, T.parent^[i] w ∉ O

open Classical in
/-- The parts meeting the `T \ O`-subtree of `v`: the parts that `v`'s parent edge can see. -/
noncomputable def seenParts (P : ι → Finset V) (O : Finset V) (v : V) : Finset ι :=
  univ.filter fun i => ∃ w ∈ P i, T.Below O v w

variable {T}

theorem mem_seenParts {P : ι → Finset V} {O : Finset V} {v : V} {i : ι} :
    i ∈ T.seenParts P O v ↔ ∃ w ∈ P i, T.Below O v w := by
  classical
  unfold seenParts; simp

theorem below_refl (O : Finset V) (v : V) : T.Below O v v :=
  ⟨0, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem below_parent {O : Finset V} {v w : V} (h : T.Below O v w) (hv : v ∉ O) :
    T.Below O (T.parent v) w := by
  obtain ⟨n, hn, hi⟩ := h
  refine ⟨n + 1, by rw [Function.iterate_succ_apply', hn], fun i hi' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
  · exact hi i h
  · rw [h, hn]; exact hv

/-- `Below O v ·` only depends on `O` strictly below `v`. -/
theorem below_congr {O O' : Finset V} {v w : V} (hv : v ≠ T.root)
    (h : ∀ u, T.depth v < T.depth u → (u ∈ O ↔ u ∈ O')) : T.Below O v w ↔ T.Below O' v w := by
  constructor
  · rintro ⟨n, hn, hi⟩
    exact ⟨n, hn, fun i hi' => by rw [← h _ (RootedTree.depth_iterate_lt hn hv hi')]; exact hi i hi'⟩
  · rintro ⟨n, hn, hi⟩
    exact ⟨n, hn, fun i hi' => by rw [h _ (RootedTree.depth_iterate_lt hn hv hi')]; exact hi i hi'⟩

theorem seenParts_congr {P : ι → Finset V} {O O' : Finset V} {v : V} (hv : v ≠ T.root)
    (h : ∀ u, T.depth v < T.depth u → (u ∈ O ↔ u ∈ O')) :
    T.seenParts P O v = T.seenParts P O' v := by
  ext i; simp only [mem_seenParts, below_congr hv h]

variable (T) in
/-- The bottom-up greedy (process the tree edges level by level, from the deepest; cut an edge iff
more than `θ` parts meet its subtree in the forest cut so far) yields a set `O` of tree edges
with `v ∈ O ↔ v ≠ root ∧ θ < |seenParts O v|`. -/
theorem exists_cut (P : ι → Finset V) (θ : ℕ) {D : ℕ} (hT : T.DepthLE D) :
    ∃ O : Finset V, ∀ v, v ∈ O ↔ v ≠ T.root ∧ θ < (T.seenParts P O v).card := by
  classical
  suffices ∀ m, ∃ O : Finset V, (∀ u ∈ O, u ≠ T.root ∧ D + 1 ≤ T.depth u + m) ∧
      ∀ v, D + 1 ≤ T.depth v + m → (v ∈ O ↔ v ≠ T.root ∧ θ < (T.seenParts P O v).card) by
    obtain ⟨O, -, hO⟩ := this (D + 1)
    exact ⟨O, fun v => hO v (by omega)⟩
  intro m
  induction m with
  | zero => exact ⟨∅, by simp, fun v hv => absurd hv (by have := hT v; omega)⟩
  | succ m ih =>
    obtain ⟨O, hO1, hO2⟩ := ih
    let N := univ.filter fun v =>
      T.depth v + m = D ∧ v ≠ T.root ∧ θ < (T.seenParts P O v).card
    refine ⟨O ∪ N, ?_, ?_⟩
    · intro u hu
      rcases mem_union.1 hu with h | h
      · have := hO1 u h; exact ⟨this.1, by omega⟩
      · simp only [N, mem_filter] at h; exact ⟨h.2.2.1, by omega⟩
    · intro v hv
      by_cases hroot : v = T.root
      · subst hroot
        simp only [ne_eq, not_true_eq_false, false_and, iff_false, mem_union, not_or]
        exact ⟨fun h => (hO1 _ h).1 rfl, by simp [N]⟩
      have hagree : ∀ u, T.depth v < T.depth u → (u ∈ O ↔ u ∈ O ∪ N) := by
        intro u hu
        simp only [mem_union, N, mem_filter, mem_univ, true_and]
        constructor
        · exact Or.inl
        · rintro (h | h)
          · exact h
          · omega
      rw [← seenParts_congr hroot hagree]
      by_cases hlev : D + 1 ≤ T.depth v + m
      · rw [← hO2 v hlev]
        simp only [mem_union, N, mem_filter, mem_univ, true_and]
        constructor
        · rintro (h | h)
          · exact h
          · omega
        · exact Or.inl
      · have hvO : v ∉ O := fun h => by have := (hO1 v h).2; omega
        simp only [mem_union, hvO, false_or, N, mem_filter, mem_univ, true_and]
        constructor
        · exact fun h => h.2
        · exact fun h => ⟨by omega, h⟩

/-- The set produced by the bottom-up greedy is unique: membership of `v` is determined by the
cut strictly below `v`. -/
theorem cut_unique (P : ι → Finset V) (θ : ℕ) {D : ℕ} (hT : T.DepthLE D) {O O' : Finset V}
    (hO : ∀ v, v ∈ O ↔ v ≠ T.root ∧ θ < (T.seenParts P O v).card)
    (hO' : ∀ v, v ∈ O' ↔ v ≠ T.root ∧ θ < (T.seenParts P O' v).card) : O = O' := by
  suffices h : ∀ m, ∀ v, D < T.depth v + m → (v ∈ O ↔ v ∈ O') by
    ext v; exact h (D + 1) v (by omega)
  intro m
  induction m with
  | zero => intro v hv; have := hT v; omega
  | succ m ih =>
    intro v hv
    by_cases hr : v = T.root
    · rw [hO, hO']; simp [hr]
    rw [hO, hO', seenParts_congr hr fun u hu => ih u (by omega)]

/-! ### The cut shortcut -/

variable (T) in
open Classical in
/-- The shortcut of part `i`: all tree edges `s(v, parent v)` with `v ∉ O` whose
`T \ O`-subtree meets `P i` (all ancestor edges of `P i` in the forest `T \ O`). -/
noncomputable def cutShortcut (P : ι → Finset V) (O : Finset V) (i : ι) : Finset (Sym2 V) :=
  (univ.filter fun v => v ≠ T.root ∧ v ∉ O ∧ i ∈ T.seenParts P O v).image T.edge

theorem mem_cutShortcut {P : ι → Finset V} {O : Finset V} {i : ι} {e : Sym2 V} :
    e ∈ T.cutShortcut P O i ↔
      ∃ v, (v ≠ T.root ∧ v ∉ O ∧ i ∈ T.seenParts P O v) ∧ T.edge v = e := by
  classical
  unfold cutShortcut; simp

theorem edge_mem_cutShortcut_iff {P : ι → Finset V} {O : Finset V} {i : ι} {v : V}
    (hv : v ≠ T.root) : T.edge v ∈ T.cutShortcut P O i ↔ v ∉ O ∧ i ∈ T.seenParts P O v := by
  rw [mem_cutShortcut]
  constructor
  · rintro ⟨u, ⟨hu, h1, h2⟩, he⟩
    rw [RootedTree.edge_injective hu hv he] at h1 h2; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨v, ⟨hv, h1, h2⟩, rfl⟩

theorem restricts_cutShortcut (P : ι → Finset V) (O : Finset V) (i : ι) :
    T.Restricts (T.cutShortcut P O i) := by
  intro e he
  obtain ⟨v, ⟨hv, -, -⟩, rfl⟩ := mem_cutShortcut.1 he
  exact RootedTree.edge_mem_edgeSet hv

/-- Congestion of the cut shortcut: an edge `v ∉ O` is used only by the parts it can see. -/
theorem card_filter_mem_cutShortcut_le {P : ι → Finset V} {O : Finset V} (J : Finset ι) {c : ℕ}
    (hO : ∀ v, v ≠ T.root → v ∉ O → (T.seenParts P O v).card ≤ c) (e : Sym2 V) :
    (J.filter fun i => e ∈ T.cutShortcut P O i).card ≤ c := by
  by_cases h : ∃ i ∈ J, e ∈ T.cutShortcut P O i
  · obtain ⟨i, -, he⟩ := h
    obtain ⟨v, ⟨hv, hvO, -⟩, rfl⟩ := mem_cutShortcut.1 he
    have hsub : J.filter (fun i => T.edge v ∈ T.cutShortcut P O i) ⊆ T.seenParts P O v := by
      intro j hj
      exact ((edge_mem_cutShortcut_iff hv).1 (mem_filter.1 hj).2).2
    exact (card_le_card hsub).trans (hO v hv hvO)
  · push Not at h
    rw [filter_false_of_mem h]; simp

/-- Every vertex of `P i ∪ V(H_i)` lies above some vertex of `P i` in `T \ O`. -/
theorem below_of_mem_partVerts {P : ι → Finset V} {O : Finset V} {i : ι} {x : V}
    (hx : x ∈ partVerts (P i) (T.cutShortcut P O i)) : ∃ w ∈ P i, T.Below O x w := by
  rcases hx with hx | ⟨e, he, hxe⟩
  · exact ⟨x, hx, below_refl O x⟩
  · obtain ⟨v, ⟨hv, hvO, hi⟩, rfl⟩ := mem_cutShortcut.1 he
    obtain ⟨w, hw, hb⟩ := mem_seenParts.1 hi
    rcases Sym2.mem_iff.1 hxe with rfl | rfl
    · exact ⟨w, hw, hb⟩
    · exact ⟨w, hw, below_parent hb hvO⟩

/-- Every block of the cut shortcut contains a vertex of the part. -/
theorem blocksMeetPart_cutShortcut (P : ι → Finset V) (O : Finset V) (i : ι) :
    BlocksMeetPart (P i) (T.cutShortcut P O i) := by
  intro x hx
  obtain ⟨w, hw, n, hn, hi⟩ := below_of_mem_partVerts hx
  refine ⟨w, hw, ?_⟩
  suffices ∀ j ≤ n, (blockGraph (T.cutShortcut P O i)).Reachable w (T.parent^[j] w) by
    rw [← hn]; exact (this n le_rfl).symm
  intro j hj
  induction j with
  | zero => exact Reachable.rfl
  | succ j ih =>
    by_cases hne : T.parent^[j] w = T.root
    · rw [Function.iterate_succ_apply', hne, T.parent_root, ← hne]; exact ih (by omega)
    refine (ih (by omega)).trans (Adj.reachable ?_)
    have hjO : T.parent^[j] w ∉ O := hi j (by omega)
    rw [Function.iterate_succ_apply']
    simp only [blockGraph, fromEdgeSet_adj, Finset.mem_coe]
    refine ⟨?_, (RootedTree.parent_ne_self hne).symm⟩
    exact (edge_mem_cutShortcut_iff hne).2
      ⟨hjO, mem_seenParts.2 ⟨w, hw, j, rfl, fun k hk => hi k (by omega)⟩⟩

/-! ### Tops of the forest `T \ O` -/

variable (T) in
/-- The tree edges not in `O`. -/
noncomputable def cutEdges (O : Finset V) : Finset (Sym2 V) :=
  (univ.filter fun v => v ≠ T.root ∧ v ∉ O).image T.edge

theorem edge_mem_cutEdges_iff {O : Finset V} {v : V} (hv : v ≠ T.root) :
    T.edge v ∈ T.cutEdges O ↔ v ∉ O := by
  unfold cutEdges
  simp only [mem_image, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨u, ⟨hu, huO⟩, he⟩
    rwa [← RootedTree.edge_injective hu hv he]
  · exact fun h => ⟨v, ⟨hv, h⟩, rfl⟩

variable (T) in
/-- The top of `x`'s tree in the forest `T \ O`. -/
noncomputable def cutTop (O : Finset V) (x : V) : V := T.climb (T.cutEdges O) x

theorem below_cutTop (O : Finset V) (x : V) : T.Below O (T.cutTop O x) x := by
  obtain ⟨n, hn, hi⟩ := T.climb_eq_iterate (T.cutEdges O) x
  exact ⟨n, hn.symm, fun i hi' => (edge_mem_cutEdges_iff (hi i hi').1).1 (hi i hi').2⟩

theorem cutTop_root_or_mem (O : Finset V) (x : V) :
    T.cutTop O x = T.root ∨ T.cutTop O x ∈ O := by
  rcases T.climb_top (T.cutEdges O) x with h | h
  · exact Or.inl h
  · by_cases hr : T.cutTop O x = T.root
    · exact Or.inl hr
    · right
      by_contra hO
      exact h ((edge_mem_cutEdges_iff hr).2 hO)

/-- Two ancestors of `x` in `T \ O` that are tops (root or in `O`) coincide. -/
theorem eq_of_below_of_below {O : Finset V} {x t t' : V} (ht : T.Below O t x)
    (htop : t = T.root ∨ t ∈ O) (ht' : T.Below O t' x) (htop' : t' = T.root ∨ t' ∈ O) :
    t = t' := by
  obtain ⟨n, hn, hi⟩ := ht
  obtain ⟨m, hm, hj⟩ := ht'
  have key : ∀ {n m : ℕ} {t t' : V}, T.parent^[n] x = t → (∀ i < m, T.parent^[i] x ∉ O) →
      T.parent^[m] x = t' → (t = T.root ∨ t ∈ O) → n ≤ m → t = t' := by
    intro n m t t' hn hj hm htop hnm
    rcases eq_or_lt_of_le hnm with rfl | hlt
    · rw [← hn, ← hm]
    · rcases htop with hr | hO
      · rw [← hm, show m = (m - n) + n by omega, Function.iterate_add_apply, hn, hr,
          iterate_root]
      · exact absurd (hn ▸ hO) (hj n hlt)
  rcases le_total n m with h | h
  · exact key hn hj hm htop h
  · exact (key hm hi hn htop' h).symm

/-- `cutTop O x` is the unique ancestor of `x` in `T \ O` that is the root or in `O`. -/
theorem eq_cutTop {O : Finset V} {x t : V} (ht : T.Below O t x) (htop : t = T.root ∨ t ∈ O) :
    t = T.cutTop O x :=
  eq_of_below_of_below ht htop (below_cutTop O x) (cutTop_root_or_mem O x)

/-- Climbing from an ancestor `y` (in `T \ O`) of a vertex of `P i` along the cut shortcut of part
`i` ends at the top of `y`'s tree in `T \ O`. -/
theorem climb_cutShortcut_eq_cutTop {P : ι → Finset V} {O : Finset V} {i : ι} {x : V}
    (hx : x ∈ P i) {y : V} (hy : T.Below O y x) :
    T.climb (T.cutShortcut P O i) y = T.cutTop O y := by
  induction hd : T.depth y using Nat.strong_induction_on generalizing y with
  | _ d ih =>
    by_cases h : y ≠ T.root ∧ y ∉ O
    · have he : T.edge y ∈ T.cutShortcut P O i :=
        (edge_mem_cutShortcut_iff h.1).2 ⟨h.2, mem_seenParts.2 ⟨x, hx, hy⟩⟩
      have he' : T.edge y ∈ T.cutEdges O := (edge_mem_cutEdges_iff h.1).2 h.2
      rw [climb_of_mem h.1 he, cutTop, climb_of_mem h.1 he', ← cutTop]
      exact ih _ (hd ▸ depth_parent_lt h.1) (below_parent hy h.2) rfl
    · have h1 : ¬ (y ≠ T.root ∧ T.edge y ∈ T.cutShortcut P O i) := by
        rintro ⟨hr, he⟩; exact h ⟨hr, ((edge_mem_cutShortcut_iff hr).1 he).1⟩
      have h2 : ¬ (y ≠ T.root ∧ T.edge y ∈ T.cutEdges O) := by
        rintro ⟨hr, he⟩; exact h ⟨hr, (edge_mem_cutEdges_iff hr).1 he⟩
      rw [climb_of_not_mem h1, cutTop, climb_of_not_mem h2]

end RootedTree

end SimpleGraph
