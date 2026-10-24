import Papers.PODC2020.ActivelyDynamicNetworks.TreeToStar
import Papers.PODC2020.ActivelyDynamicNetworks.LineArith
import Papers.PODC2020.ActivelyDynamicNetworks.LowerBounds

/-!
# LineToCompleteBinaryTree (Proposition 2.2 / A.2)

Michail–Skretas–Spirakis, PODC 2020, §2.3. The initial network is the line `0 - 1 - ⋯ - n`
(`n + 1` nodes, diameter `d = n`) rooted at the endpoint `0`, each node knowing its parent. In
every round, each node whose parent is not the root and whose grandparent has fewer than two
children activates the edge to its grandparent and deactivates the edge to its parent; otherwise
it does nothing. (The paper says a node repeats this "until" its grandparent has two children or it
is attached to the root; the closed form below shows that a node that stops never satisfies the
condition again, so the stateless rule used here has the same executions.)

* `exec n r`: the snapshot after `r` rounds; `exec_zero` (the line), `isExec` (valid execution),
  `exec_eq` (closed form: the parent of `i` after `r` rounds is `i - 2^min(r, kk i)`).
* `exec_stable`, `exec_succ_ne`: the algorithm stops changing the network exactly after
  `kk n ≤ ⌈log₂ d⌉` rounds (`kk_le_clog`).
* `final_isDepthTree`, `final_edist`: the final network is the complete binary tree in level order:
  node `i` has depth `⌊log₂ (i+1)⌋`, the depth is `⌊log₂ (n+1)⌋`.
* `childCount_le_two`, `degree_le_three`: in every snapshot every node has at most two children,
  hence degree at most `3`.
* `activeEdges_le`, `numActivated_le`, `totalActivations_le`: at most `2(n+1) - 3` active edges
  during a round, at most `n - 1` activations per round, at most `(n-1)⌈log₂ d⌉` in total.
-/

namespace Podc.ActivelyDynamicNetworks.LineToBinaryTree

open SimpleGraph Cslib.DynNet.Active LineArith

variable (n : ℕ)

/-- The closed form: parent pointers after `r` rounds. -/
def QF (r : ℕ) (i : Fin (n + 1)) : Fin (n + 1) := ⟨Q r i, (Nat.sub_le _ _).trans_lt i.2⟩

/-- Number of children of `g` under the parent map `P`. -/
def childCount (P : Fin (n + 1) → Fin (n + 1)) (g : Fin (n + 1)) : ℕ :=
  (Finset.univ.filter fun j => j ≠ g ∧ P j = g).card

/-- The nodes that move in a round: parent not the root, grandparent with fewer than two
children. -/
def movers (P : Fin (n + 1) → Fin (n + 1)) (u : Fin (n + 1)) : Prop :=
  P u ≠ 0 ∧ childCount n P (P (P u)) < 2

instance (P : Fin (n + 1) → Fin (n + 1)) : DecidablePred (movers n P) := fun _ => by
  unfold movers; infer_instance

/-- One round of LineToCompleteBinaryTree on parent maps. -/
def step (P : Fin (n + 1) → Fin (n + 1)) : Fin (n + 1) → Fin (n + 1) := jump P (movers n P)

/-- The snapshot after `r` rounds. -/
def exec (r : ℕ) : SimpleGraph (Fin (n + 1)) := parentGraph ((step n)^[r] (lineTree n).parent)

variable {n}

theorem QF_val (r : ℕ) (i : Fin (n + 1)) : (QF n r i).val = Q r i.val := rfl

theorem QF_zero : QF n 0 = (lineTree n).parent := by
  funext i; ext; simp [QF_val, Q_zero_left, lineTree]

theorem isRootedMap_QF (r : ℕ) : IsRootedMap (QF n r) 0 Fin.val where
  map_root := by ext; simp [QF_val, Q_zero_right]
  rk_lt v hv := by
    rw [QF_val]
    exact Q_lt (Nat.one_le_iff_ne_zero.2 fun h => hv (Fin.ext h))

theorem movers_iff (r : ℕ) (i : Fin (n + 1)) : movers n (QF n r) i ↔ r < kk i := by
  constructor
  · rintro ⟨h1, h2⟩
    by_contra h
    push Not at h
    have hq : Q r i ≠ 0 := fun h' => h1 (Fin.ext h')
    obtain ⟨a, b, hab, ha, hb, hai, hbi, hqa, hqb⟩ := frozen_two_children h hq
    let a' : Fin (n + 1) := ⟨a, hai.trans i.2⟩
    let b' : Fin (n + 1) := ⟨b, hbi.trans i.2⟩
    have hsub : ({a', b'} : Finset (Fin (n + 1))) ⊆
        Finset.univ.filter fun j => j ≠ QF n r (QF n r i) ∧ QF n r j = QF n r (QF n r i) := by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, QF_val]
      rcases hj with rfl | rfl
      · exact ⟨ha, hqa⟩
      · exact ⟨hb, hqb⟩
    have := Finset.card_le_card hsub
    rw [Finset.card_pair (fun h => hab (congrArg Fin.val h))] at this
    unfold childCount at h2
    omega
  · intro h
    obtain ⟨h1, -, h3⟩ := active_step h
    refine ⟨fun h' => h1 (congrArg Fin.val h'), ?_⟩
    have hsub : (Finset.univ.filter fun j => j ≠ QF n r (QF n r i) ∧
        QF n r j = QF n r (QF n r i)) ⊆ {QF n r i} := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, QF_val] at hj
      simp only [Finset.mem_singleton, Fin.ext_iff, QF_val]
      exact h3 j hj.1 hj.2
    have := Finset.card_le_card hsub
    unfold childCount
    simp only [Finset.card_singleton] at this
    omega

theorem step_QF (r : ℕ) : step n (QF n r) = QF n (r + 1) := by
  funext i
  unfold step jump
  split_ifs with h
  · rw [movers_iff] at h
    ext; rw [QF_val, QF_val, QF_val]; exact (active_step h).2.1
  · rw [movers_iff] at h
    push Not at h
    ext; rw [QF_val, QF_val]; exact (Q_succ_of_le h).symm

theorem iterate_step (r : ℕ) : (step n)^[r] (lineTree n).parent = QF n r := by
  induction r with
  | zero => exact QF_zero.symm
  | succ r ih => rw [Function.iterate_succ_apply', ih, step_QF]

theorem exec_eq (r : ℕ) : exec n r = parentGraph (QF n r) := by
  rw [exec, iterate_step]

theorem exec_zero : exec n 0 = pathGraph (n + 1) := by
  rw [exec]; exact parentGraph_lineTree n

theorem movers_ne_root (r : ℕ) : ∀ u, movers n (QF n r) u → QF n r u ≠ 0 := fun _ h => h.1

/-- LineToCompleteBinaryTree is a valid execution of the actively dynamic model. -/
theorem isExec : IsExec (exec n) := fun r => by
  rw [exec_eq, exec_eq, ← step_QF]
  exact validRound_jump (isRootedMap_QF r) (movers_ne_root r)

theorem isTree (r : ℕ) : (exec n r).IsTree := by
  rw [exec_eq]; exact (isRootedMap_QF r).isTree

/-! ### Termination -/

theorem QF_stable {r : ℕ} (hr : kk n ≤ r) : QF n r = QF n (kk n) := by
  funext i; ext
  rw [QF_val, QF_val, Q_of_le (le_trans (kk_mono (Nat.le_of_lt_succ i.2)) hr),
    Q_of_le (kk_mono (Nat.le_of_lt_succ i.2))]

/-- After `kk n` rounds the network no longer changes. -/
theorem exec_stable {r : ℕ} (hr : kk n ≤ r) : exec n r = exec n (kk n) := by
  rw [exec_eq, exec_eq, QF_stable hr]

/-- Before round `kk n` the network still changes (node `n` moves). -/
theorem exec_succ_ne {r : ℕ} (hr : r < kk n) : exec n (r + 1) ≠ exec n r := by
  intro h
  rw [exec_eq, exec_eq] at h
  have hn : (Fin.last n : Fin (n + 1)) ≠ 0 := by
    intro h'; have := congrArg Fin.val h'; simp at this
    have := (le_kk_iff 0 n).1 (by omega); omega
  have h1 : (parentGraph (QF n r)).Adj (Fin.last n) (QF n r (Fin.last n)) :=
    parentGraph_adj.2 ⟨((isRootedMap_QF r).map_ne_self hn).symm, Or.inl rfl⟩
  rw [← h, parentGraph_adj] at h1
  have hp := pow_kk_le (i := n) (by omega)
  have h2 : 2 ^ (r + 1) ≤ 2 ^ kk n := Nat.pow_le_pow_right (by norm_num) hr
  have hq1 : Q (r + 1) n = n - 2 ^ (r + 1) := by unfold Q; rw [min_eq_left hr]
  have hq0 : Q r n = n - 2 ^ r := Q_of_lt (by omega)
  rw [pow_succ] at h2 hq1
  have hpos : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rcases h1 with ⟨-, h1 | h1⟩
  · have := congrArg Fin.val h1
    simp only [QF_val, Fin.val_last] at this
    omega
  · have := congrArg Fin.val h1
    simp only [QF_val, Fin.val_last] at this
    have h3 := Q_lt (r := r + 1) (i := Q r n) (by omega)
    omega

/-- The number of rounds is at most `⌈log₂ d⌉`, `d = n` the diameter of the line (in fact at most
`⌊log₂ n⌋`). -/
theorem kk_le_clog (n : ℕ) : kk n ≤ Nat.clog 2 n := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp [kk]
  · have := pow_kk_le h
    exact ((Nat.le_log_iff_pow_le (by norm_num) (by omega)).2 this).trans (Nat.log_le_clog 2 n)

/-! ### The final tree -/

theorem QF_final_val (i : Fin (n + 1)) : (QF n (kk n) i).val = F i :=
  Q_of_le (kk_mono (Nat.le_of_lt_succ i.2))

theorem isRootedMap_final : IsRootedMap (QF n (kk n)) 0 fun i => lev i where
  map_root := (isRootedMap_QF _).map_root
  rk_lt v hv := by
    have hv1 : 1 ≤ v.val := Nat.one_le_iff_ne_zero.2 fun h => hv (Fin.ext h)
    simp only [QF_final_val]
    have := lev_F hv1; omega

/-- **Proposition 2.2 (shape).** In the final network node `i` has depth `⌊log₂ (i+1)⌋`: the
complete binary tree in level order. -/
theorem final_edist (i : Fin (n + 1)) : (exec n (kk n)).edist 0 i = lev i := by
  rw [exec_eq]
  refine isRootedMap_final.edist_root_eq (by simp [lev]) (fun v hv => ?_) i
  have hv1 : 1 ≤ v.val := Nat.one_le_iff_ne_zero.2 fun h => hv (Fin.ext h)
  simp only [QF_final_val]; exact lev_F hv1

/-- **Proposition 2.2 (target).** The final network is a rooted tree of depth `⌊log₂ (n+1)⌋`
(attained by node `n`), the minimum possible for a binary tree on `n + 1` nodes. -/
theorem final_isDepthTree : IsDepthTree (exec n (kk n)) 0 (Nat.log 2 (n + 1)) := by
  refine ⟨isTree _, fun v => ?_⟩
  rw [final_edist]
  exact_mod_cast Nat.log_mono_right (by omega)

theorem final_edist_last : (exec n (kk n)).edist 0 (Fin.last n) = Nat.log 2 (n + 1) := by
  rw [final_edist]; rfl

/-! ### Degrees -/

/-- **Proposition 2.2 (binary).** In every snapshot every node has at most two children. -/
theorem childCount_le_two (r : ℕ) (g : Fin (n + 1)) : childCount n (QF n r) g ≤ 2 := by
  by_contra hc
  push Not at hc
  obtain ⟨a, ha, b, hb, c, hc', hab, hac, hbc⟩ := Finset.two_lt_card.1 hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, Fin.ext_iff, QF_val] at ha hb hc'
  have uniq : ∀ x : Fin (n + 1), x.val ≠ g.val → Q r x = g → ∀ y : Fin (n + 1), y.val ≠ g.val →
      Q r y = g → (∀ j', j' ≠ g.val → Q r j' = g.val → j' = x.val) → x = y := by
    intro x _ _ y hy hy' hu; exact Fin.ext (hu _ hy hy').symm
  rcases child_cases ha.1 ha.2 with h1 | h1
  · exact hab (uniq a ha.1 ha.2 b hb.1 hb.2 h1)
  rcases child_cases hb.1 hb.2 with h2 | h2
  · exact hab (uniq b hb.1 hb.2 a ha.1 ha.2 h2).symm
  rcases child_cases hc'.1 hc'.2 with h3 | h3
  · exact hac (uniq c hc'.1 hc'.2 a ha.1 ha.2 h3).symm
  have := c1_lt_c2 g.val
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;>
    first
    | exact hab (Fin.ext (h1.trans h2.symm))
    | exact hac (Fin.ext (h1.trans h3.symm))
    | exact hbc (Fin.ext (h2.trans h3.symm))

/-- **Proposition 2.2 (degree).** In every snapshot every node has degree at most `3`. -/
theorem degree_le_three (r : ℕ) (v : Fin (n + 1)) : ((exec n r).neighborSet v).ncard ≤ 3 := by
  rw [exec_eq]
  have hsub := IsRootedMap.neighborSet_subset (P := QF n r) v
  have h1 : ({j | j ≠ v ∧ QF n r j = v} : Set (Fin (n + 1))).ncard ≤ 2 := by
    have := childCount_le_two r v
    unfold childCount at this
    rw [← Set.ncard_coe_finset] at this
    convert this using 2
    ext j; simp
  calc ((parentGraph (QF n r)).neighborSet v).ncard
      ≤ (insert (QF n r v) {j | j ≠ v ∧ QF n r j = v}).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ {j | j ≠ v ∧ QF n r j = v}.ncard + 1 := Set.ncard_insert_le _ _
    _ ≤ 3 := by omega

/-! ### Edge complexity -/

theorem QF_one (r : ℕ) (h : 1 ≤ n) : QF n r ⟨1, by omega⟩ = 0 := by
  ext; simp [QF_val, Q, kk]

theorem ncard_movers_le (r : ℕ) (hn : 1 ≤ n) : {u | movers n (QF n r) u}.ncard ≤ n - 1 := by
  have hsub : {u | movers n (QF n r) u} ⊆ (Set.univ \ {0, ⟨1, by omega⟩}) := by
    intro u hu
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_insert_iff, Set.mem_singleton_iff, true_and]
    rintro (rfl | rfl)
    · exact hu.1 (isRootedMap_QF r).map_root
    · exact hu.1 (QF_one r hn)
  have hne : (0 : Fin (n + 1)) ≠ ⟨1, by omega⟩ := by
    intro h; have := congrArg Fin.val h; simp at this
  calc {u | movers n (QF n r) u}.ncard ≤ (Set.univ \ {0, ⟨1, by omega⟩} : Set (Fin (n + 1))).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = n - 1 := by
        rw [Set.ncard_sdiff (by simp) (Set.toFinite _), Set.ncard_univ, Set.ncard_pair hne,
          Nat.card_eq_fintype_card, Fintype.card_fin]
        omega

/-- **Proposition 2.2 (active edges).** During a round at most `(N-1) + (N-2) = 2N - 3` edges are
active, `N = n + 1` the number of nodes. -/
theorem activeEdges_le (r : ℕ) (hn : 1 ≤ n) :
    (exec n r ⊔ jumpAct (QF n r) (movers n (QF n r))).edgeSet.ncard ≤ 2 * (n + 1) - 3 := by
  rw [exec_eq, edgeSet_sup]
  have h1 := (isRootedMap_QF (n := n) r).ncard_edgeSet
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  have h2 := (ncard_jumpAct_le (P := QF n r) (S := movers n (QF n r))).trans (ncard_movers_le r hn)
  have := Set.ncard_union_le (parentGraph (QF n r)).edgeSet
    (jumpAct (QF n r) (movers n (QF n r))).edgeSet
  omega

theorem numActivated_le (r : ℕ) (hn : 1 ≤ n) : numActivated (exec n) r ≤ n - 1 := by
  unfold numActivated
  rw [exec_eq, exec_eq, ← step_QF]
  exact (numActivated_jump_le (isRootedMap_QF r) (movers_ne_root r)).trans (ncard_movers_le r hn)

theorem numActivated_eq_zero {r : ℕ} (hr : kk n ≤ r) : numActivated (exec n) r = 0 := by
  unfold numActivated
  rw [exec_stable hr, exec_stable (hr.trans (Nat.le_succ r)), sdiff_self]
  simp

/-- **Proposition 2.2 (total activations).** At most `(n-1)⌈log₂ d⌉ ≤ N log₂ N` activations. -/
theorem totalActivations_le (R : ℕ) (hn : 1 ≤ n) :
    totalActivations (exec n) R ≤ (n - 1) * Nat.clog 2 n :=
  (totalActivations_le_of (fun r => numActivated_le r hn) (fun _ h => numActivated_eq_zero h) R).trans
    (Nat.mul_le_mul_left _ (kk_le_clog n))

/-- **Proposition 2.2** (summary). On the line with `n + 1 ≥ 2` nodes rooted at an endpoint,
LineToCompleteBinaryTree is a valid execution; after `kk n ≤ ⌈log₂ d⌉` rounds (`d = n`) it stops
changing the network, which is then the complete binary tree of depth `⌊log₂ (n+1)⌋` rooted at
the endpoint; all snapshots are trees of maximum degree `≤ 3`; at most `2N - 3` edges are active
during a round and at most `(n-1)⌈log₂ d⌉` edges are activated in total. -/
theorem proposition_2_2 (hn : 1 ≤ n) :
    IsExec (exec n) ∧ exec n 0 = pathGraph (n + 1) ∧ kk n ≤ Nat.clog 2 n ∧
    (∀ r, kk n ≤ r → exec n r = exec n (kk n)) ∧
    IsDepthTree (exec n (kk n)) 0 (Nat.log 2 (n + 1)) ∧
    (∀ r, (exec n r).IsTree ∧ ∀ v, ((exec n r).neighborSet v).ncard ≤ 3) ∧
    (∀ r, (exec n r ⊔ jumpAct (QF n r) (movers n (QF n r))).edgeSet.ncard ≤ 2 * (n + 1) - 3) ∧
    (∀ R, totalActivations (exec n) R ≤ (n - 1) * Nat.clog 2 n) :=
  ⟨isExec, exec_zero, kk_le_clog n, fun _ h => exec_stable h, final_isDepthTree,
    fun r => ⟨isTree r, degree_le_three r⟩, fun r => activeEdges_le r hn,
    fun R => totalActivations_le R hn⟩

end Podc.ActivelyDynamicNetworks.LineToBinaryTree
