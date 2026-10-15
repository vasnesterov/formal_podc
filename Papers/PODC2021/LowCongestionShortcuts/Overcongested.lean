import Cslib.Foundations.Combinatorics.SimpleGraph.Shortcut
import Mathlib

/-!
# Overcongested tree edges (proof of [GH21, Theorem 3.1], first part)

Fix a rooted spanning tree `T` of `G` and a collection of parts `P`. Tree edges are identified with
their lower endpoints (`v ↔ s(v, parent v)`, `v ≠ root`), so a set of tree edges is a `Finset V`.

* `Below T O v w`: `w` is a descendant of `v` in the forest `T \ O` (the path from `w` up to `v`
  uses no edge of `O`).
* `parts T P O v` (`I_e` in the paper): the parts meeting the `T \ O`-subtree of `v`.
* `exists_stable`: the paper's greedy (processing tree edges bottom-up, an edge `e` is
  *overcongested* and added to `O` iff `|I_e| ≥ c`) produces a set `O` with
  `v ∈ O ↔ v ≠ root ∧ c ≤ |I_v(O)|`; this fixed-point property is all the proof uses.
* `exists_rep`: the representative `r_{(e, P_i)}` of a pair `(e, P_i)` of the bipartite graph `B`,
  chosen *topmost* in `P_i` (the paper says "some representative"; topmost is needed).
* `shortcut`: the shortcut `H_i` of case (I) — all ancestor edges of `P_i` in `T \ O` — with its
  congestion (`card_filter_mem_shortcut_le`), block (`numBlocks_shortcut_le`) and
  `BlocksMeetPart` (`blocksMeetPart_shortcut`) properties.
-/

set_option linter.unusedSectionVars false

namespace LowCongestionShortcuts

open SimpleGraph Finset

variable {V ι : Type*} [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]
  {G : SimpleGraph V} (T : G.RootedTree)

/-- `w` is a descendant of `v` in the forest `T \ O`: going up from `w` reaches `v` without
crossing a tree edge of `O` (tree edges are identified with their lower endpoints). -/
def Below (O : Finset V) (v w : V) : Prop :=
  ∃ n, T.parent^[n] w = v ∧ ∀ i < n, T.parent^[i] w ∉ O

open Classical in
/-- `I_v` in the paper: the parts meeting the `T \ O`-subtree of `v`. -/
noncomputable def parts (P : ι → Finset V) (O : Finset V) (v : V) : Finset ι :=
  univ.filter fun i => ∃ w ∈ P i, Below T O v w

variable {T}

theorem mem_parts {P : ι → Finset V} {O : Finset V} {v : V} {i : ι} :
    i ∈ parts T P O v ↔ ∃ w ∈ P i, Below T O v w := by
  classical
  unfold parts; simp

theorem below_refl (O : Finset V) (v : V) : Below T O v v :=
  ⟨0, rfl, fun _ h => absurd h (Nat.not_lt_zero _)⟩

theorem below_parent {O : Finset V} {v w : V} (h : Below T O v w) (hv : v ∉ O) :
    Below T O (T.parent v) w := by
  obtain ⟨n, hn, hi⟩ := h
  refine ⟨n + 1, by rw [Function.iterate_succ_apply', hn], fun i hi' => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hi' with h | h
  · exact hi i h
  · rw [h, hn]; exact hv

/-- `Below O v ·` only depends on `O` strictly below `v`. -/
theorem below_congr {O O' : Finset V} {v w : V} (hv : v ≠ T.root)
    (h : ∀ u, T.depth v < T.depth u → (u ∈ O ↔ u ∈ O')) : Below T O v w ↔ Below T O' v w := by
  constructor
  · rintro ⟨n, hn, hi⟩
    exact ⟨n, hn, fun i hi' => by rw [← h _ (RootedTree.depth_iterate_lt hn hv hi')]; exact hi i hi'⟩
  · rintro ⟨n, hn, hi⟩
    exact ⟨n, hn, fun i hi' => by rw [h _ (RootedTree.depth_iterate_lt hn hv hi')]; exact hi i hi'⟩

theorem parts_congr {P : ι → Finset V} {O O' : Finset V} {v : V} (hv : v ≠ T.root)
    (h : ∀ u, T.depth v < T.depth u → (u ∈ O ↔ u ∈ O')) : parts T P O v = parts T P O' v := by
  ext i; simp only [mem_parts, below_congr hv h]

variable (T) in
/-- The greedy selection of overcongested edges (processing the tree level by level, bottom-up)
yields a set `O` of tree edges such that an edge is in `O` iff at least `c` parts meet its subtree
in `T \ O`. -/
theorem exists_stable (P : ι → Finset V) (c : ℝ) {D : ℕ} (hT : T.DepthLE D) :
    ∃ O : Finset V, ∀ v, v ∈ O ↔ v ≠ T.root ∧ c ≤ (parts T P O v).card := by
  classical
  suffices ∀ m, ∃ O : Finset V, (∀ u ∈ O, u ≠ T.root ∧ D + 1 ≤ T.depth u + m) ∧
      ∀ v, D + 1 ≤ T.depth v + m → (v ∈ O ↔ v ≠ T.root ∧ c ≤ (parts T P O v).card) by
    obtain ⟨O, -, hO⟩ := this (D + 1)
    exact ⟨O, fun v => hO v (by omega)⟩
  intro m
  induction m with
  | zero => exact ⟨∅, by simp, fun v hv => absurd hv (by have := hT v; omega)⟩
  | succ m ih =>
    obtain ⟨O, hO1, hO2⟩ := ih
    let N := univ.filter fun v => T.depth v + m = D ∧ v ≠ T.root ∧ c ≤ (parts T P O v).card
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
      rw [← parts_congr hroot hagree]
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

/-- Representatives: for `i ∈ I_v` there is a topmost vertex `r ∈ P i` below `v` in `T \ O`; the
path from `r` (exclusive) up to `v` (inclusive) avoids `P i`. -/
theorem exists_rep {P : ι → Finset V} {O : Finset V} {v : V} {i : ι}
    (h : i ∈ parts T P O v) : ∃ r ∈ P i, ∃ n, T.parent^[n] r = v ∧
      (∀ j < n, T.parent^[j] r ∉ O) ∧ ∀ j, 1 ≤ j → j ≤ n → T.parent^[j] r ∉ P i := by
  classical
  have hex : ∃ n, ∃ r ∈ P i, T.parent^[n] r = v ∧ ∀ j < n, T.parent^[j] r ∉ O := by
    obtain ⟨w, hw, n, hn, hi⟩ := mem_parts.1 h
    exact ⟨n, w, hw, hn, hi⟩
  obtain ⟨r, hr, hn, hi⟩ := Nat.find_spec hex
  refine ⟨r, hr, Nat.find hex, hn, hi, fun j hj1 hj2 hjP => ?_⟩
  have : Nat.find hex ≤ Nat.find hex - j := by
    apply Nat.find_min'
    refine ⟨T.parent^[j] r, hjP, ?_, fun j' hj' => ?_⟩
    · rw [← Function.iterate_add_apply]; convert hn using 2; omega
    · rw [← Function.iterate_add_apply]; exact hi _ (by omega)
  omega

/-! ### Case (I): the shortcut of a part -/

variable (T) in
open Classical in
/-- The shortcut `H_i` of case (I): all tree edges `s(v, parent v)` with `v ∉ O` whose
`T \ O`-subtree meets `P i` ("all ancestor edges of `P_i` in the forest `T \ O`"). -/
noncomputable def shortcut (P : ι → Finset V) (O : Finset V) (i : ι) : Finset (Sym2 V) :=
  (univ.filter fun v => v ≠ T.root ∧ v ∉ O ∧ i ∈ parts T P O v).image T.edge

theorem mem_shortcut {P : ι → Finset V} {O : Finset V} {i : ι} {e : Sym2 V} :
    e ∈ shortcut T P O i ↔ ∃ v, (v ≠ T.root ∧ v ∉ O ∧ i ∈ parts T P O v) ∧ T.edge v = e := by
  classical
  unfold shortcut; simp

theorem edge_mem_shortcut_iff {P : ι → Finset V} {O : Finset V} {i : ι} {v : V}
    (hv : v ≠ T.root) : T.edge v ∈ shortcut T P O i ↔ v ∉ O ∧ i ∈ parts T P O v := by
  rw [mem_shortcut]
  constructor
  · rintro ⟨u, ⟨hu, h1, h2⟩, he⟩
    rw [RootedTree.edge_injective hu hv he] at h1 h2; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨v, ⟨hv, h1, h2⟩, rfl⟩

theorem restricts_shortcut (P : ι → Finset V) (O : Finset V) (i : ι) :
    T.Restricts (shortcut T P O i) := by
  intro e he
  obtain ⟨v, ⟨hv, -, -⟩, rfl⟩ := mem_shortcut.1 he
  exact RootedTree.edge_mem_edgeSet hv

/-- Congestion of case (I): an edge outside `O` is used only by parts in `I_v`. -/
theorem card_filter_mem_shortcut_le {P : ι → Finset V} {O : Finset V} (J : Finset ι)
    {c : ℝ} (hc : 0 ≤ c) (hO : ∀ v, v ≠ T.root → v ∉ O → ((parts T P O v).card : ℝ) < c)
    (e : Sym2 V) : ((J.filter fun i => e ∈ shortcut T P O i).card : ℝ) ≤ c := by
  by_cases h : ∃ i ∈ J, e ∈ shortcut T P O i
  · obtain ⟨i, -, he⟩ := h
    obtain ⟨v, ⟨hv, hvO, -⟩, rfl⟩ := mem_shortcut.1 he
    have hsub : J.filter (fun i => T.edge v ∈ shortcut T P O i) ⊆ parts T P O v := by
      intro j hj
      exact ((edge_mem_shortcut_iff hv).1 (mem_filter.1 hj).2).2
    exact le_trans (by exact_mod_cast card_le_card hsub) (hO v hv hvO).le
  · push Not at h
    rw [filter_false_of_mem h]; simpa using hc

/-- Every vertex of `P i ∪ V(H_i)` lies above some vertex of `P i` in `T \ O`. -/
theorem below_of_mem_partVerts {P : ι → Finset V} {O : Finset V} {i : ι} {x : V}
    (hx : x ∈ partVerts (P i) (shortcut T P O i)) : ∃ w ∈ P i, Below T O x w := by
  rcases hx with hx | ⟨e, he, hxe⟩
  · exact ⟨x, hx, below_refl O x⟩
  · obtain ⟨v, ⟨hv, hvO, hi⟩, rfl⟩ := mem_shortcut.1 he
    obtain ⟨w, hw, hb⟩ := mem_parts.1 hi
    rcases Sym2.mem_iff.1 hxe with rfl | rfl
    · exact ⟨w, hw, hb⟩
    · exact ⟨w, hw, below_parent hb hvO⟩

/-- Every block of `H_i` contains a vertex of `P i`. -/
theorem blocksMeetPart_shortcut (P : ι → Finset V) (O : Finset V) (i : ι) :
    BlocksMeetPart (P i) (shortcut T P O i) := by
  intro x hx
  obtain ⟨w, hw, n, hn, hi⟩ := below_of_mem_partVerts hx
  refine ⟨w, hw, ?_⟩
  -- walk from `w` up to `x` along edges of the shortcut
  suffices ∀ j ≤ n, (blockGraph (shortcut T P O i)).Reachable w (T.parent^[j] w) by
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
    exact (edge_mem_shortcut_iff hne).2 ⟨hjO, mem_parts.2 ⟨w, hw, j, rfl, fun k hk => hi k (by omega)⟩⟩

/-- The tops of the blocks of `H_i`: the climb from any vertex of `P i ∪ V(H_i)` ends at the root or
at an overcongested edge `v ∈ O` with `i ∈ I_v` (an edge of `B`). -/
theorem climb_shortcut_mem {P : ι → Finset V} {O : Finset V} {i : ι} {x : V}
    (hx : x ∈ partVerts (P i) (shortcut T P O i)) :
    T.climb (shortcut T P O i) x = T.root ∨
      (T.climb (shortcut T P O i) x ∈ O ∧ i ∈ parts T P O (T.climb (shortcut T P O i) x)) := by
  have hp : ∃ w ∈ P i, Below T O (T.climb (shortcut T P O i) x) w := by
    refine RootedTree.climb_induction _ (fun y => ∃ w ∈ P i, Below T O y w) ?_ x
      (below_of_mem_partVerts hx)
    rintro y hy he ⟨w, hw, hb⟩
    exact ⟨w, hw, below_parent hb ((edge_mem_shortcut_iff hy).1 he).1⟩
  have hi : i ∈ parts T P O (T.climb (shortcut T P O i) x) := mem_parts.2 hp
  rcases RootedTree.climb_top (shortcut T P O i) x with h | h
  · exact Or.inl h
  · by_cases hr : T.climb (shortcut T P O i) x = T.root
    · exact Or.inl hr
    · refine Or.inr ⟨?_, hi⟩
      by_contra hO
      exact h ((edge_mem_shortcut_iff hr).2 ⟨hO, hi⟩)

/-- Blocks of case (I): a part has at most `1 + deg_B(P_i)` blocks (one per edge of `B` at `P_i`,
plus possibly the block containing the root). -/
theorem numBlocks_shortcut_le (P : ι → Finset V) (O : Finset V) (i : ι) :
    numBlocks (P i) (shortcut T P O i) ≤ 1 + (O.filter fun v => i ∈ parts T P O v).card := by
  classical
  set H := shortcut T P O i
  have hcc : ∀ x, (blockGraph H).connectedComponentMk x =
      (blockGraph H).connectedComponentMk (T.climb H x) :=
    fun x => ConnectedComponent.sound (RootedTree.reachable_climb H x)
  have himg : (blockGraph H).connectedComponentMk '' partVerts (P i) H =
      (blockGraph H).connectedComponentMk '' (T.climb H '' partVerts (P i) H) := by
    rw [Set.image_image]; exact Set.image_congr fun x _ => hcc x
  have hsub : T.climb H '' partVerts (P i) H ⊆
      ↑(insert T.root (O.filter fun v => i ∈ parts T P O v)) := by
    rintro _ ⟨x, hx, rfl⟩
    rcases climb_shortcut_mem hx with h | h
    · rw [h]; simp
    · simp only [coe_insert, coe_filter, Set.mem_insert_iff, Set.mem_ofPred_eq]; exact Or.inr h
  unfold numBlocks
  rw [himg]
  calc _ ≤ (T.climb H '' partVerts (P i) H).ncard := Set.ncard_image_le (Set.toFinite _)
    _ ≤ (↑(insert T.root (O.filter fun v => i ∈ parts T P O v)) : Set V).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ 1 + (O.filter fun v => i ∈ parts T P O v).card := by
        rw [Set.ncard_coe_finset]; rw [add_comm]; exact card_insert_le _ _

end LowCongestionShortcuts
