import Papers.PODC2020.ActivelyDynamicNetworks.PointerJumping
import Cslib.Foundations.Combinatorics.SimpleGraph.RootedTree
import Mathlib.Combinatorics.SimpleGraph.Hasse

/-!
# TreeToStar (Proposition 2.1 / A.1)

Michail–Skretas–Spirakis, PODC 2020, §2.3: starting from a rooted tree `T` (nodes know their
parent), in every round each node whose parent is not the root activates the edge to its
grandparent and deactivates the edge to its parent. This is synchronous pointer jumping: after `t`
rounds the parent of `v` is `parent^[2^t] v` (`ptr T t`).

* `exec T t`: the snapshot after `t` rounds; `exec_zero` (it starts from `T`), `exec_succ` (one
  round = the activations/deactivations of the rule), `isExec` (valid execution of the model),
  `isTree` (every snapshot is a spanning tree).
* `star_iff`: the snapshot after `t` rounds is the spanning star centred at the root **iff**
  `⌈log₂ d⌉ ≤ t`, where `d` is the depth of `T`. So TreeToStar takes exactly `⌈log₂ d⌉` rounds.
* `activeEdges_le`: at most `(n-1) + (n-2) = 2n-3` edges are active during a round (the tree
  edges plus the activated ones); every snapshot has exactly `n - 1` edges (`ncard_edgeSet`).
* `numActivated_le`, `totalActivations_le`: at most `n - 2` activations per round and
  `(n-2)⌈log₂ d⌉ = O(n log n)` in total.
* `ceil_log_depth_le_log_false`: the paper's `⌈log d⌉ ≤ log n` fails for the line on `6` nodes
  (`⌈log₂ 5⌉ = 3 > log₂ 6`), where TreeToStar indeed needs 3 rounds (`line6_not_star_two`).
-/

namespace Podc.ActivelyDynamicNetworks

open SimpleGraph Cslib.DynNet.Active

namespace TreeToStar

variable {V : Type*} {G : SimpleGraph V} (T : G.RootedTree)

/-- The parent pointers after `t` rounds of TreeToStar: `parent^[2^t]`. -/
def ptr (t : ℕ) : V → V := T.parent^[2 ^ t]

/-- The nodes that move in round `t`: those whose parent is not the root. -/
def movers (t : ℕ) (u : V) : Prop := ptr T t u ≠ T.root

instance [DecidableEq V] (t : ℕ) : DecidablePred (movers T t) := fun _ => by
  unfold movers; infer_instance

/-- The snapshot after `t` rounds. -/
def exec (t : ℕ) : SimpleGraph V := parentGraph (ptr T t)

theorem isRootedMap_parent : IsRootedMap T.parent T.root T.depth :=
  ⟨T.parent_root, fun _ hv => RootedTree.depth_parent_lt hv⟩

theorem isRootedMap_ptr (t : ℕ) : IsRootedMap (ptr T t) T.root T.depth where
  map_root := RootedTree.iterate_root _
  rk_lt v hv := by
    unfold ptr
    rw [RootedTree.depth_iterate]
    have := RootedTree.depth_pos hv
    have : 0 < 2 ^ t := Nat.two_pow_pos t
    omega

variable [DecidableEq V]

theorem jump_ptr (t : ℕ) : jump (ptr T t) (movers T t) = ptr T (t + 1) := by
  funext u
  have e : ptr T (t + 1) u = ptr T t (ptr T t u) := by
    simp only [ptr, pow_succ, mul_two, Function.iterate_add_apply]
  rw [e]
  unfold jump
  split_ifs with h
  · rfl
  · unfold movers at h; push Not at h
    rw [h, (isRootedMap_ptr T t).map_root]

theorem movers_ne_root (t : ℕ) : ∀ u, movers T t u → ptr T t u ≠ T.root := fun _ h => h

theorem exec_zero : exec T 0 = parentGraph T.parent := by
  simp [exec, ptr]

/-- One round of TreeToStar: the snapshot after round `t` is obtained from the one before by
activating the grandparent edges and deactivating the parent edges of the moving nodes. -/
theorem exec_succ (t : ℕ) : exec T (t + 1) =
    (exec T t ⊔ jumpAct (ptr T t) (movers T t)) \ jumpDeact (ptr T t) (movers T t) := by
  rw [exec, ← jump_ptr]
  exact parentGraph_jump (isRootedMap_ptr T t) (movers_ne_root T t)

/-- TreeToStar is a valid execution of the actively dynamic model. -/
theorem isExec : IsExec (exec T) := fun t => by
  rw [exec, exec, ← jump_ptr]
  exact validRound_jump (isRootedMap_ptr T t) (movers_ne_root T t)

theorem isTree [Finite V] (t : ℕ) : (exec T t).IsTree := (isRootedMap_ptr T t).isTree

theorem ncard_edgeSet [Finite V] (t : ℕ) : (exec T t).edgeSet.ncard + 1 = Nat.card V :=
  (isRootedMap_ptr T t).ncard_edgeSet

variable [Fintype V]

/-- The depth `d` of the tree. -/
def height : ℕ := Finset.univ.sup T.depth

theorem depth_le_height (v : V) : T.depth v ≤ height T :=
  Finset.le_sup (f := T.depth) (Finset.mem_univ v)

theorem ptr_eq_root_iff (t : ℕ) (v : V) : ptr T t v = T.root ↔ T.depth v ≤ 2 ^ t := by
  constructor
  · intro h
    have := RootedTree.depth_iterate (T := T) v (2 ^ t)
    rw [← ptr, h, T.depth_root] at this
    omega
  · exact RootedTree.iterate_eq_root_of_le

theorem all_ptr_eq_root_iff (t : ℕ) : (∀ v, ptr T t v = T.root) ↔ Nat.clog 2 (height T) ≤ t := by
  rw [Nat.clog_le_iff_le_pow (by norm_num)]
  simp only [ptr_eq_root_iff]
  constructor
  · intro h; exact Finset.sup_le fun v _ => h v
  · intro h v; exact (depth_le_height T v).trans h

/-- **Proposition 2.1 (time, exact).** After `t` rounds TreeToStar has turned `T` into the spanning
star centred at the root iff `⌈log₂ d⌉ ≤ t`, `d` the depth of `T`. -/
theorem star_iff (t : ℕ) :
    (∀ v, v ≠ T.root → (exec T t).Adj v T.root) ↔ Nat.clog 2 (height T) ≤ t := by
  rw [← all_ptr_eq_root_iff]
  simp only [exec, (isRootedMap_ptr T t).adj_root_iff]
  constructor
  · intro h v
    by_cases hv : v = T.root
    · rw [hv]; exact (isRootedMap_ptr T t).map_root
    · exact (h v hv).2
  · intro h v hv; exact ⟨hv, h v⟩

theorem exec_eq_star {t : ℕ} (ht : Nat.clog 2 (height T) ≤ t) :
    exec T t = parentGraph (fun _ => T.root) := by
  rw [exec]; congr 1; funext v; exact (all_ptr_eq_root_iff T t).2 ht v

/-- Besides the root, some child of the root never moves. -/
theorem ncard_movers_le (t : ℕ) (hn : 2 ≤ Fintype.card V) :
    {u | movers T t u}.ncard ≤ Fintype.card V - 2 := by
  classical
  obtain ⟨v, hv⟩ := Fintype.exists_ne_of_one_lt_card (by omega) T.root
  obtain ⟨c, hc, hcr⟩ := (isRootedMap_parent T).exists_child_root hv
  have hc' : ptr T t c = T.root := by
    rw [ptr_eq_root_iff]
    have := T.depth_parent c hc
    rw [hcr, T.depth_root] at this
    have : 1 ≤ 2 ^ t := Nat.one_le_two_pow
    omega
  have hsub : {u | movers T t u} ⊆ (Set.univ \ {T.root, c}) := by
    intro u hu
    simp only [Set.mem_ofPred_eq, movers] at hu
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_and]
    rintro (rfl | rfl)
    · exact hu (isRootedMap_ptr T t).map_root
    · exact hu hc'
  calc {u | movers T t u}.ncard ≤ (Set.univ \ {T.root, c} : Set V).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = Fintype.card V - 2 := by
        rw [Set.ncard_sdiff (by simp) (Set.toFinite _), Set.ncard_univ, Set.ncard_pair hc.symm,
          Nat.card_eq_fintype_card]

/-- **Proposition 2.1 (active edges).** During a round at most `(n-1) + (n-2) = 2n - 3` edges are
active (the current tree edges and the newly activated ones). -/
theorem activeEdges_le (t : ℕ) (hn : 2 ≤ Fintype.card V) :
    (exec T t ⊔ jumpAct (ptr T t) (movers T t)).edgeSet.ncard ≤ 2 * Fintype.card V - 3 := by
  rw [edgeSet_sup]
  have h1 := ncard_edgeSet T t
  have h2 : (jumpAct (ptr T t) (movers T t)).edgeSet.ncard ≤ Fintype.card V - 2 :=
    ncard_jumpAct_le.trans (ncard_movers_le T t hn)
  rw [Nat.card_eq_fintype_card] at h1
  have := Set.ncard_union_le (exec T t).edgeSet (jumpAct (ptr T t) (movers T t)).edgeSet
  omega

/-- At most `n - 2` edges are activated per round. -/
theorem numActivated_le (t : ℕ) (hn : 2 ≤ Fintype.card V) :
    numActivated (exec T) t ≤ Fintype.card V - 2 := by
  unfold numActivated
  rw [exec, exec, ← jump_ptr]
  exact (numActivated_jump_le (isRootedMap_ptr T t) (movers_ne_root T t)).trans
    (ncard_movers_le T t hn)

/-- No activations once the star is formed. -/
theorem numActivated_eq_zero {t : ℕ} (ht : Nat.clog 2 (height T) ≤ t) :
    numActivated (exec T) t = 0 := by
  unfold numActivated
  rw [exec_eq_star T ht, exec_eq_star T (ht.trans (Nat.le_succ t)), sdiff_self]
  simp

/-- **Proposition 2.1 (total activations).** TreeToStar activates at most `(n-2)⌈log₂ d⌉`
edges in total, over any horizon. -/
theorem totalActivations_le (R : ℕ) (hn : 2 ≤ Fintype.card V) :
    totalActivations (exec T) R ≤ (Fintype.card V - 2) * Nat.clog 2 (height T) := by
  suffices h : totalActivations (exec T) R ≤ (Fintype.card V - 2) * min R (Nat.clog 2 (height T)) from
    h.trans (Nat.mul_le_mul_left _ (min_le_right _ _))
  induction R with
  | zero => simp [totalActivations]
  | succ R ih =>
    have e : totalActivations (exec T) (R + 1) = totalActivations (exec T) R + numActivated (exec T) R := by
      simp [totalActivations, Finset.sum_range_succ]
    rw [e]
    by_cases hR : R < Nat.clog 2 (height T)
    · have : min (R + 1) (Nat.clog 2 (height T)) = min R (Nat.clog 2 (height T)) + 1 := by omega
      rw [this, Nat.mul_succ]
      exact add_le_add ih (numActivated_le T R hn)
    · rw [numActivated_eq_zero T (by omega)]
      have : min (R + 1) (Nat.clog 2 (height T)) = min R (Nat.clog 2 (height T)) := by omega
      rw [this]; simpa using ih

/-- **Proposition 2.1** (summary). TreeToStar is a valid execution, every snapshot is a spanning
tree, it reaches the spanning star centred at the root after exactly `⌈log₂ d⌉` rounds, with at
most `2n - 3` active edges during each round and at most `(n-2)⌈log₂ d⌉` activations in total. -/
theorem proposition_2_1 (hn : 2 ≤ Fintype.card V) :
    IsExec (exec T) ∧ exec T 0 = parentGraph T.parent ∧ (∀ t, (exec T t).IsTree) ∧
    (∀ t, (∀ v, v ≠ T.root → (exec T t).Adj v T.root) ↔ Nat.clog 2 (height T) ≤ t) ∧
    (∀ t, (exec T t ⊔ jumpAct (ptr T t) (movers T t)).edgeSet.ncard ≤ 2 * Fintype.card V - 3) ∧
    (∀ R, totalActivations (exec T) R ≤ (Fintype.card V - 2) * Nat.clog 2 (height T)) :=
  ⟨isExec T, exec_zero T, isTree T, star_iff T, fun t => activeEdges_le T t hn,
    fun R => totalActivations_le T R hn⟩

end TreeToStar

/-! ### The line rooted at an endpoint -/

/-- The line `0 - 1 - ⋯ - n` rooted at `0` (parent of `i` is `i - 1`), as a rooted tree whose
graph is `pathGraph (n + 1)`. -/
def lineTree (n : ℕ) : (pathGraph (n + 1)).RootedTree where
  root := 0
  parent i := ⟨i.val - 1, by omega⟩
  depth i := i.val
  parent_root := by ext; simp
  depth_root := rfl
  depth_parent v hv := by
    have : v.val ≠ 0 := fun h => hv (Fin.ext h)
    simp only; omega
  adj_parent v hv := by
    have : v.val ≠ 0 := fun h => hv (Fin.ext h)
    rw [pathGraph_adj]; simp only; omega

theorem parentGraph_lineTree (n : ℕ) : parentGraph (lineTree n).parent = pathGraph (n + 1) := by
  ext i j
  rw [parentGraph_adj, pathGraph_adj]
  simp only [lineTree, Fin.ext_iff, ne_eq]
  omega

theorem height_lineTree (n : ℕ) : TreeToStar.height (lineTree n) = n := by
  apply le_antisymm
  · exact Finset.sup_le fun i _ => by simp only [lineTree]; omega
  · exact TreeToStar.depth_le_height (lineTree n) (Fin.last n)

/-- On the line with 6 nodes (depth 5) TreeToStar has not produced a star after 2 rounds. -/
theorem line6_not_star_two :
    ¬ ∀ v, v ≠ (lineTree 5).root → (TreeToStar.exec (lineTree 5) 2).Adj v (lineTree 5).root := by
  rw [TreeToStar.star_iff, height_lineTree]
  decide

/-- **Proposition 2.1, the bound `⌈log d⌉ ≤ log n` is false**: for the line with `n = 6` nodes,
`d = 5`, TreeToStar needs `⌈log₂ 5⌉ = 3` rounds (`line6_not_star_two`), but `2^3 > 6`, i.e.
`3 > log₂ 6`. (True instead: `⌈log₂ d⌉ ≤ ⌈log₂ n⌉`.) -/
theorem ceil_log_depth_le_log_false :
    Nat.clog 2 (TreeToStar.height (lineTree 5)) = 3 ∧ 6 < 2 ^ Nat.clog 2 (TreeToStar.height (lineTree 5)) := by
  rw [height_lineTree]; decide

end Podc.ActivelyDynamicNetworks
