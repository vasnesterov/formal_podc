import Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree
import Mathlib

/-!
# Synchronous primitives on a supergraph

The routing algorithms of [HIZ16, Theorem 2, Lemma 3] run synchronous algorithms on the
*supergraph* of a part, whose nodes are the block components (one *superstep* = one exchange over
`G`-edges between blocks, followed by a convergecast and a broadcast inside every block). Here we
verify the supergraph-level algorithms on an abstract finite graph `S`:

* `floodMin x k B`: min-flooding (every node keeps the minimum of its own value and its
  neighbours' values). `floodMin_spec`: after `k` supersteps, `B` holds the minimum over all nodes
  within distance `k`; `floodMin_eq_inf`: in a connected graph with `n` nodes, after `n - 1`
  supersteps every node holds the global minimum (leader election).
* `floodDist L k B`: BFS distance labelling from `L` by flooding. `floodDist_spec`: after `k`
  supersteps, `B` holds `dist L B` if it is `≤ k`, and `⊤` otherwise. (A BFS parent is then any
  neighbour with a smaller label, e.g. CSLib's `bfsParent`; `Connected.bfsTree`.)
* `treeAgg T f k B`: convergecast of a commutative-monoid aggregate along a rooted spanning tree
  `T` of `S` (each node repeatedly sends its current partial sum to its parent).
  `treeAgg_root`: if `T` has depth `≤ h`, after `h` supersteps the root holds `∑ B, f B`.
-/

set_option linter.unusedSectionVars false

namespace ShortcutsNoEmbedding

open SimpleGraph Finset

variable {β : Type*} [Fintype β] [DecidableEq β] (S : SimpleGraph β) [DecidableRel S.Adj]

/-- `u` and `v` are joined by a walk of length at most `k`. -/
def WalkLE (u v : β) (k : ℕ) : Prop := ∃ p : S.Walk u v, p.length ≤ k

variable {S}

theorem walkLE_succ_iff {u v : β} {k : ℕ} :
    WalkLE S u v (k + 1) ↔ WalkLE S u v k ∨ ∃ w, S.Adj u w ∧ WalkLE S w v k := by
  constructor
  · rintro ⟨p, hp⟩
    cases p with
    | nil => exact Or.inl ⟨Walk.nil, by simp⟩
    | cons h q => exact Or.inr ⟨_, h, q, by simp at hp; omega⟩
  · rintro (⟨p, hp⟩ | ⟨w, h, p, hp⟩)
    · exact ⟨p, by omega⟩
    · exact ⟨Walk.cons h p, by simp; omega⟩

theorem walkLE_refl (u : β) (k : ℕ) : WalkLE S u u k := ⟨Walk.nil, by simp⟩

theorem WalkLE.mono {u v : β} {k l : ℕ} (h : WalkLE S u v k) (hkl : k ≤ l) : WalkLE S u v l :=
  let ⟨p, hp⟩ := h; ⟨p, hp.trans hkl⟩

/-- In a connected graph on `n` nodes any two nodes are joined by a walk of length `≤ n - 1`. -/
theorem Connected.walkLE_card (hS : S.Connected) (u v : β) :
    WalkLE S u v (Fintype.card β - 1) := by
  obtain ⟨p⟩ := hS.preconnected u v
  have := p.bypass_isPath.length_lt
  exact ⟨p.bypass, by omega⟩

/-! ### Min-flooding (leader election) -/

variable (S) in
/-- The nodes within distance `k` of `B`. -/
noncomputable def superBall (B : β) (k : ℕ) : Finset β :=
  open Classical in univ.filter fun B' => WalkLE S B B' k

theorem mem_ball {B B' : β} {k : ℕ} : B' ∈ superBall S B k ↔ WalkLE S B B' k := by
  classical
  unfold superBall; simp

theorem ball_nonempty (B : β) (k : ℕ) : (superBall S B k).Nonempty :=
  ⟨B, mem_ball.2 (walkLE_refl B k)⟩

variable (S) in
/-- Min-flooding: in each superstep every node takes the minimum of its value and its neighbours'
values. -/
noncomputable def floodMin {α : Type*} [LinearOrder α] (x : β → α) : ℕ → β → α
  | 0 => x
  | k + 1 => fun B =>
    (insert B (univ.filter (S.Adj B))).inf' (insert_nonempty _ _) (floodMin x k)

/-- After `k` supersteps of min-flooding, `B` holds the minimum over the ball of radius `k`. -/
theorem floodMin_spec {α : Type*} [LinearOrder α] (x : β → α) (k : ℕ) (B : β) :
    floodMin S x k B = (superBall S B k).inf' (ball_nonempty B k) x := by
  induction k generalizing B with
  | zero =>
    have : superBall S B 0 = {B} := by
      ext B'
      rw [mem_ball, mem_singleton]
      constructor
      · rintro ⟨p, hp⟩
        cases p with
        | nil => rfl
        | cons _ _ => simp at hp
      · rintro rfl; exact walkLE_refl _ _
    simp only [floodMin, this, inf'_singleton]
  | succ k ih =>
    simp only [floodMin, ih]
    apply le_antisymm
    · rw [le_inf'_iff]
      intro B' hB'
      rcases walkLE_succ_iff.1 (mem_ball.1 hB') with h | ⟨w, hw, h⟩
      · exact (inf'_le _ (mem_insert_self B _)).trans (inf'_le _ (mem_ball.2 h))
      · exact (inf'_le _ (mem_insert_of_mem (by simpa using hw))).trans
          (inf'_le _ (mem_ball.2 h))
    · rw [le_inf'_iff]
      intro w hw
      rw [le_inf'_iff]
      intro B' hB'
      apply inf'_le
      rcases mem_insert.1 hw with rfl | hw
      · exact mem_ball.2 ((mem_ball.1 hB').mono (by omega))
      · simp only [mem_filter, mem_univ, true_and] at hw
        exact mem_ball.2 (walkLE_succ_iff.2 (Or.inr ⟨w, hw, mem_ball.1 hB'⟩))

/-- **Leader election by min-flooding.** In a connected graph with at most `b` nodes, after
`b - 1` supersteps every node holds the global minimum. -/
theorem floodMin_eq_inf {α : Type*} [LinearOrder α] (hS : S.Connected) (x : β → α) {b : ℕ}
    (hb : Fintype.card β ≤ b) (B : β) :
    floodMin S x (b - 1) B = univ.inf' (Finset.univ_nonempty_iff.mpr ⟨B⟩) x := by
  rw [floodMin_spec]
  congr 1
  ext B'
  simp only [mem_univ, iff_true]
  exact mem_ball.2 ((Connected.walkLE_card hS B B').mono (by omega))

/-! ### BFS distances by flooding -/

variable (S) in
/-- BFS labelling from `L` by flooding: initially `0` at `L` and `⊤` elsewhere; in each
superstep every node takes the minimum of its label and its neighbours' labels plus one. -/
noncomputable def floodDist (L : β) : ℕ → β → ℕ∞
  | 0 => fun B => if B = L then 0 else ⊤
  | k + 1 => fun B => min (floodDist L k B) ((univ.filter (S.Adj B)).inf fun N => floodDist L k N + 1)

/-- After `k` supersteps, `B` holds `dist L B` if it is at most `k`, and `⊤` otherwise. -/
theorem floodDist_spec (hS : S.Connected) (L : β) (k : ℕ) (B : β) :
    floodDist S L k B = if S.dist L B ≤ k then (S.dist L B : ℕ∞) else ⊤ := by
  induction k generalizing B with
  | zero =>
    simp only [floodDist, nonpos_iff_eq_zero]
    by_cases h : B = L
    · subst h; simp
    · have : S.dist L B ≠ 0 := by
        rw [Ne, (hS.preconnected L B).dist_eq_zero_iff]; exact fun h' => h h'.symm
      simp [h, this]
  | succ k ih =>
    simp only [floodDist, ih]
    have hadj : ∀ N, S.Adj B N → S.dist L B ≤ S.dist L N + 1 ∧ S.dist L N ≤ S.dist L B + 1 := by
      intro N hN
      have h1 : S.dist L B ≤ S.dist L N + S.dist N B := hS.dist_triangle
      have h2 : S.dist L N ≤ S.dist L B + S.dist B N := hS.dist_triangle
      rw [dist_eq_one_iff_adj.2 hN.symm] at h1
      rw [dist_eq_one_iff_adj.2 hN] at h2
      exact ⟨h1, h2⟩
    set δ := S.dist L B
    -- lower bound on the neighbour terms
    have hlow : ∀ N ∈ univ.filter (S.Adj B),
        (if δ ≤ k + 1 then (δ : ℕ∞) else ⊤) ≤
          (if S.dist L N ≤ k then (S.dist L N : ℕ∞) else ⊤) + 1 := by
      intro N hN
      simp only [mem_filter, mem_univ, true_and] at hN
      have := (hadj N hN).1
      split_ifs with h1 h2 h2
      · exact_mod_cast this
      · simp
      · omega
      · simp
    have hge := Finset.le_inf hlow
    rcases lt_trichotomy δ (k + 1) with hlt | heq | hgt
    · rw [ite_eq_left (by omega : δ ≤ k), ite_eq_left hlt.le]
      refine min_eq_left ?_
      exact (ite_eq_left hlt.le ▸ hge :)
    · rw [ite_eq_right (by omega : ¬ δ ≤ k), ite_eq_left heq.le]
      rw [min_eq_right le_top]
      refine le_antisymm ?_ (ite_eq_left heq.le ▸ hge :)
      have hBL : B ≠ L := by
        rintro rfl; simp [δ] at heq
      obtain ⟨N, hN, hd⟩ := hS.exists_adj_dist_succ L hBL
      refine (inf_le (mem_filter.2 ⟨mem_univ _, hN⟩)).trans ?_
      rw [ite_eq_left (by omega : S.dist L N ≤ k)]
      have : δ = S.dist L N + 1 := hd.symm
      rw [this]; push_cast; exact le_rfl
    · rw [ite_eq_right (by omega : ¬ δ ≤ k), ite_eq_right (by omega : ¬ δ ≤ k + 1)]
      simp only [min_eq_left_iff, top_le_iff]
      rw [Finset.inf_eq_top_iff]
      intro N hN
      simp only [mem_filter, mem_univ, true_and] at hN
      have := (hadj N hN).1
      rw [ite_eq_right (by omega)]
      simp

/-! ### Convergecast along a rooted tree -/

variable (T : S.RootedTree)

/-- The children of `B` in the rooted tree `T`. -/
noncomputable def children (B : β) : Finset β :=
  open Classical in univ.filter fun u => u ≠ T.root ∧ T.parent u = B

/-- Convergecast of a commutative-monoid aggregate along `T`: in each superstep every node sends
its current partial aggregate to its parent and recomputes its own from its children's. -/
noncomputable def treeAgg {M : Type*} [AddCommMonoid M] (f : β → M) : ℕ → β → M
  | 0 => f
  | k + 1 => fun B => f B + ∑ u ∈ children T B, treeAgg f k u

/-- The descendants of `B` at most `k` levels below `B`. -/
noncomputable def descK (k : ℕ) (B : β) : Finset β :=
  open Classical in univ.filter fun w => T.depth B ≤ T.depth w ∧ T.depth w ≤ T.depth B + k ∧
    T.parent^[T.depth w - T.depth B] w = B

variable {T}

theorem mem_descK {k : ℕ} {B w : β} : w ∈ descK T k B ↔
    T.depth B ≤ T.depth w ∧ T.depth w ≤ T.depth B + k ∧ T.parent^[T.depth w - T.depth B] w = B := by
  classical
  unfold descK; simp

theorem mem_children {B u : β} : u ∈ children T B ↔ u ≠ T.root ∧ T.parent u = B := by
  classical
  unfold children; simp

theorem descK_zero (B : β) : descK T 0 B = {B} := by
  ext w
  rw [mem_descK, mem_singleton]
  constructor
  · rintro ⟨h1, h2, h3⟩
    rwa [show T.depth w - T.depth B = 0 by omega] at h3
  · rintro rfl; simp

theorem depth_child {B u : β} (hu : u ∈ children T B) : T.depth u = T.depth B + 1 := by
  obtain ⟨hr, hp⟩ := mem_children.1 hu
  have := T.depth_parent u hr; rw [hp] at this; omega

theorem descK_succ (k : ℕ) (B : β) :
    descK T (k + 1) B = insert B ((children T B).biUnion (descK T k)) := by
  ext w
  simp only [mem_insert, mem_biUnion, mem_descK]
  constructor
  · rintro ⟨h1, h2, h3⟩
    by_cases hd : T.depth w = T.depth B
    · left; rw [hd, Nat.sub_self] at h3; exact h3
    · right
      set u := T.parent^[T.depth w - T.depth B - 1] w
      have hdu : T.depth u = T.depth B + 1 := by
        rw [T.depth_iterate]; omega
      have hur : u ≠ T.root := fun h => by
        rw [h, T.depth_root] at hdu; omega
      have hpu : T.parent u = B := by
        rw [← h3, show T.depth w - T.depth B = (T.depth w - T.depth B - 1) + 1 by omega,
          Function.iterate_succ_apply']
      refine ⟨u, mem_children.2 ⟨hur, hpu⟩, by omega, by omega, ?_⟩
      rw [hdu, show T.depth w - (T.depth B + 1) = T.depth w - T.depth B - 1 by omega]
  · rintro (rfl | ⟨u, hu, h1, h2, h3⟩)
    · simp
    · have hdu := depth_child hu
      obtain ⟨-, hpu⟩ := mem_children.1 hu
      refine ⟨by omega, by omega, ?_⟩
      rw [show T.depth w - T.depth B = (T.depth w - T.depth u) + 1 by omega,
        Function.iterate_succ_apply', h3, hpu]

theorem notMem_biUnion_descK (k : ℕ) (B : β) : B ∉ (children T B).biUnion (descK T k) := by
  simp only [mem_biUnion, not_exists, not_and]
  intro u hu h
  have := (mem_descK.1 h).1
  have := depth_child hu
  omega

theorem pairwiseDisjoint_descK (k : ℕ) (B : β) :
    ((children T B : Set β)).PairwiseDisjoint (descK T k) := by
  intro u hu u' hu' hne
  rw [Function.onFun, Finset.disjoint_left]
  intro w hw hw'
  apply hne
  have h1 := mem_descK.1 hw
  have h2 := mem_descK.1 hw'
  have e1 := depth_child (mem_coe.1 hu)
  have e2 := depth_child (mem_coe.1 hu')
  rw [← h1.2.2, ← h2.2.2, e1, e2]

/-- After `k` supersteps, `B` holds the aggregate over its descendants at most `k` levels below. -/
theorem treeAgg_spec {M : Type*} [AddCommMonoid M] (f : β → M) (k : ℕ) (B : β) :
    treeAgg T f k B = ∑ w ∈ descK T k B, f w := by
  induction k generalizing B with
  | zero => simp [treeAgg, descK_zero]
  | succ k ih =>
    rw [descK_succ, sum_insert (notMem_biUnion_descK k B), sum_biUnion (pairwiseDisjoint_descK k B)]
    simp only [treeAgg, ih]

/-- **Convergecast along a tree.** If `T` has depth `≤ h`, after `h` supersteps the root holds the
aggregate of all values. -/
theorem treeAgg_root {M : Type*} [AddCommMonoid M] (f : β → M) {h : ℕ} (hT : T.DepthLE h) :
    treeAgg T f h T.root = ∑ B, f B := by
  rw [treeAgg_spec]
  congr 1
  ext w
  simp only [mem_descK, mem_univ, iff_true, T.depth_root, Nat.sub_zero, zero_add]
  exact ⟨Nat.zero_le _, hT w, T.iterate_depth w⟩

end ShortcutsNoEmbedding
