import Papers.PODC2023.TreeExplorationBFDN.Sync
import Papers.PODC2023.TreeExplorationBFDN.Accounting
import Papers.PODC2023.TreeExplorationBFDN.Idle

/-!
# Theorem 2.1: BFDN explores any tree in `2n/k + D² (min(log Δ, log k) + 2)` rounds

Cosson, Massoulié, Viennot, PODC 2023, Theorem 2.1 (full version arXiv:2301.13307, Theorem 1),
together with Lemma 2 of the full version (the per-depth bound on anchor assignments, the
statement behind Corollary 3.2 of the brief announcement).

* `n = Fintype.card V` is the number of nodes, `D = maxDepth T` the depth of the tree and
  `Δ = G.maxDegree` the maximum degree of the graph `G` whose rooted spanning tree `T` is explored
  (when `G` is a tree, `T` has exactly the edges of `G`).
* `log` is the natural logarithm.
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ} [Fintype V] [DecidableEq V]

variable (T) in
/-- The depth `D` of the tree. -/
def maxDepth : ℕ := univ.sup T.depth

omit [DecidableEq V] in
theorem depth_le_maxDepth (v : V) : T.depth v ≤ maxDepth T :=
  le_sup (f := T.depth) (mem_univ v)

/-- A non-root node has at most `Δ − 1` children. -/
theorem nChildren_add_one_le [DecidableRel G.Adj] {w : V} (hw : w ≠ T.root) :
    nChildren T w + 1 ≤ G.maxDegree := by
  classical
  refine le_trans ?_ (G.degree_le_maxDegree w)
  rw [← card_neighborFinset_eq_degree]
  have hsub : insert (T.parent w) (univ.filter fun x => x ≠ T.root ∧ T.parent x = w) ⊆
      G.neighborFinset w := by
    intro x hx
    rw [mem_insert] at hx
    rw [mem_neighborFinset]
    rcases hx with rfl | hx
    · exact (T.adj_parent w hw)
    · simp only [mem_filter, mem_univ, true_and] at hx
      rw [← hx.2]; exact (T.adj_parent x hx.1).symm
  have hnot : T.parent w ∉ (univ.filter fun x => x ≠ T.root ∧ T.parent x = w) := by
    simp only [mem_filter, mem_univ, true_and, not_and]
    intro hpr hpp
    have h1 := T.depth_parent w hw
    have h2 := T.depth_parent _ hpr
    rw [hpp] at h2; omega
  have := card_le_card hsub
  rw [card_insert_of_notMem hnot] at this
  unfold nChildren; convert this

section Exec

variable {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e)
include he

omit he in
theorem assignCount_eq_filter (d t : ℕ) :
    assignCount T act e d t = ((univ.filter fun i => i ∈ act t ∧ (e t).pos i = T.root).filter
      fun i => T.depth ((e (t + 1)).anchor i) = d).card := by
  classical
  unfold assignCount; rw [filter_filter]; congr 1; ext i; simp [and_assoc]

/-- Anchors assigned at depth `d ≥ 1` are open nodes, hence `d < D`. -/
theorem assignCount_eq_zero_of_le {d t : ℕ} (hd : 1 ≤ d) (hD : maxDepth T ≤ d) :
    assignCount T act e d t = 0 := by
  classical
  unfold assignCount
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro i - ⟨hi, hp, hdi⟩
  obtain ⟨⟨_, w, hw, hpw, _⟩, _⟩ := he.cand_of_assign hd hi hp hdi
  have := T.depth_parent w hw
  have := depth_le_maxDepth (T := T) w
  rw [hpw] at *
  omega

theorem assignDepth_le (t : ℕ) :
    assignDepth T act e t ≤ ∑ d ∈ range (maxDepth T), d * assignCount T act e d t := by
  classical
  unfold assignDepth
  rw [← sum_fiberwise_of_maps_to (s := univ.filter fun i => i ∈ act t ∧ (e t).pos i = T.root)
    (t := range (maxDepth T + 1)) (g := fun i => T.depth ((e (t + 1)).anchor i))
    (fun i _ => mem_range.2 (Nat.lt_succ_of_le (depth_le_maxDepth _)))]
  rw [sum_range_succ]
  have hlast : ∑ i ∈ (univ.filter fun i => i ∈ act t ∧ (e t).pos i = T.root).filter
      (fun i => T.depth ((e (t + 1)).anchor i) = maxDepth T), T.depth ((e (t + 1)).anchor i) = 0 := by
    rw [sum_congr rfl (fun i hi => (mem_filter.1 hi).2), sum_const, smul_eq_mul]
    rcases Nat.eq_zero_or_pos (maxDepth T) with h0 | hpos
    · rw [h0]; simp
    · rw [← assignCount_eq_filter (act := act) (e := e), assignCount_eq_zero_of_le he hpos le_rfl]; simp
  rw [hlast, add_zero]
  apply sum_le_sum
  intro d _
  rw [sum_congr rfl (fun i hi => (mem_filter.1 hi).2), sum_const, smul_eq_mul,
    ← assignCount_eq_filter (act := act) (e := e), mul_comm]

end Exec

/-- **Lemma 2** of the full version (synchronous model): for every depth `d ≥ 1`, the number of
calls to `Reanchor` returning a node of depth `d` is at most `S_k(Δ) = ∑_{u=1}^{k} min(Δ, ⌈k/u⌉)`. -/
theorem lemma_2_urnSum [DecidableRel G.Adj] {e : ℕ → Config V k} (he : IsSyncExec T e) {d : ℕ}
    (hd : 1 ≤ d) (t₁ : ℕ) :
    ∑ t ∈ range t₁, assignCount T (fun _ => univ) e d t ≤ urnSum k G.maxDegree := by
  by_cases hΔ : 1 ≤ G.maxDegree
  · exact sum_assignCount_le_of_window he hd hΔ
      (sync_window he hd fun w hw => nChildren_add_one_le hw) t₁
  · have hall : ∀ w : V, w = T.root := by
      intro w; by_contra hw; have := nChildren_add_one_le (T := T) hw; omega
    have : ∀ t, assignCount T (fun _ => univ) e d t = 0 := by
      intro t
      apply assignCount_eq_zero_of_le he hd
      have : maxDepth T = 0 := by
        apply Nat.eq_zero_of_le_zero; apply Finset.sup_le; intro v _; rw [hall v, T.depth_root]
      omega
    simp [this]

/-- **Lemma 2** of the full version (arXiv:2301.13307): in an execution of BFDN, for every depth
`d ≥ 1`, the total number of re-assignments of anchors to nodes of depth `d` is at most
`k (min(log k, log Δ) + 2)`. -/
theorem lemma_2 [DecidableRel G.Adj] {e : ℕ → Config V k} (he : IsSyncExec T e) {d : ℕ}
    (hd : 1 ≤ d) (t₁ : ℕ) :
    (∑ t ∈ range t₁, assignCount T (fun _ => univ) e d t : ℝ) ≤
      k * (min (Real.log k) (Real.log G.maxDegree) + 2) := by
  rw [min_comm]
  exact_mod_cast (Nat.cast_le.2 (lemma_2_urnSum he hd t₁)).trans (urnSum_le k G.maxDegree)

/-- **Theorem 2.1** of [CMV23]: in the synchronous model with complete communication, BFDN
explores any tree with `k ≥ 1` robots and brings all robots back to the root in at most
`2n/k + D² (min(log Δ, log k) + 2)` rounds, whatever the tie-breaking choices. -/
theorem theorem_2_1 [DecidableRel G.Adj] (hk : 0 < k) {e : ℕ → Config V k} (he : IsSyncExec T e) :
    ∃ t : ℕ, Terminal T (e t) ∧
      (t : ℝ) ≤ 2 * (Fintype.card V : ℝ) / k +
        (maxDepth T : ℝ) ^ 2 * (min (Real.log G.maxDegree) (Real.log k) + 2) := by
  classical
  set D := maxDepth T
  set m := min (Real.log G.maxDegree) (Real.log k)
  set B : ℝ := 2 * (Fintype.card V : ℝ) / k + (D : ℝ) ^ 2 * (m + 2)
  have hm : 0 ≤ m := le_min (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)
  have hL : (urnSum k G.maxDegree : ℝ) ≤ k * (m + 2) := urnSum_le k G.maxDegree
  -- key estimate: if no terminal configuration before `t₁` then `t₁ ≤ B`
  have key : ∀ t₁, (∀ t < t₁, ¬ Terminal T (e t)) → (t₁ : ℝ) ≤ B := by
    intro t₁ hnt
    have hidle := card_idleRounds_le he D (depth_le_maxDepth) t₁ hnt
    have hmoved := sum_moved_le he t₁
    -- k t₁ = idle + moves
    have hk1 : k * t₁ ≤ k * (2 * D) + ∑ t ∈ range t₁, (movedSet e t).card := by
      have : ∀ t ∈ range t₁, k ≤ k * (if ∃ i, (e (t + 1)).pos i = (e t).pos i then 1 else 0) +
          (movedSet e t).card := by
        intro t _
        split_ifs with h
        · omega
        · push Not at h
          have : movedSet e t = univ := by
            ext i; simp [movedSet, h i]
          rw [this, card_univ, Fintype.card_fin]; omega
      have h2 := sum_le_sum this
      rw [sum_const, card_range, smul_eq_mul, sum_add_distrib, ← mul_sum, ← card_filter] at h2
      have := Nat.mul_le_mul_left k hidle
      nlinarith
    have hvis : (e t₁).vis.card ≤ Fintype.card V := card_le_univ _
    have hvis1 : 1 ≤ (e t₁).vis.card := card_pos.2 ⟨_, (he.inv t₁).root_vis⟩
    have hAD : ∑ t ∈ range t₁, assignDepth T (fun _ => univ) e t ≤
        ∑ d ∈ range D, d * urnSum k G.maxDegree := by
      calc ∑ t ∈ range t₁, assignDepth T (fun _ => univ) e t
          ≤ ∑ t ∈ range t₁, ∑ d ∈ range D, d * assignCount T (fun _ => univ) e d t :=
            sum_le_sum fun t _ => assignDepth_le he t
        _ = ∑ d ∈ range D, d * ∑ t ∈ range t₁, assignCount T (fun _ => univ) e d t := by
            rw [sum_comm]; simp_rw [mul_sum]
        _ ≤ ∑ d ∈ range D, d * urnSum k G.maxDegree := by
            apply sum_le_sum; intro d _
            rcases Nat.eq_zero_or_pos d with rfl | hd
            · simp
            · exact Nat.mul_le_mul_left d (lemma_2_urnSum he hd t₁)
    rw [← sum_mul] at hAD
    have hsum := sum_range_id_mul_two D
    -- move to the reals
    have hkR : (0 : ℝ) < k := Nat.cast_pos.2 hk
    have e1 : (k : ℝ) * t₁ ≤ k * (2 * D) + 2 * ((Fintype.card V : ℝ) - 1) +
        (D : ℝ) * (D - 1) * urnSum k G.maxDegree := by
      have h1 : ((k * t₁ : ℕ) : ℝ) ≤ ((k * (2 * D) + (2 * ((e t₁).vis.card - 1) +
          2 * ((∑ d ∈ range D, d) * urnSum k G.maxDegree)) : ℕ) : ℝ) := by
        exact_mod_cast le_trans hk1 (by omega)
      push_cast [Nat.cast_sub hvis1] at h1
      have hs : ((∑ d ∈ range D, d : ℕ) : ℝ) * 2 = (D : ℝ) * (D - 1) := by
        rcases Nat.eq_zero_or_pos D with h0 | hpos
        · rw [h0]; simp
        · have := congrArg (fun x : ℕ => (x : ℝ)) hsum
          push_cast [Nat.cast_sub hpos] at this ⊢
          linarith
      have hv : ((e t₁).vis.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hvis
      push_cast at hs
      nlinarith
    have hU : (D : ℝ) * (D - 1) * urnSum k G.maxDegree ≤ (D : ℝ) * (D - 1) * (k * (m + 2)) := by
      rcases Nat.eq_zero_or_pos D with h0 | hpos
      · rw [h0]; simp
      · have : (0 : ℝ) ≤ (D : ℝ) * (D - 1) := by
          have : (1 : ℝ) ≤ D := by exact_mod_cast hpos
          nlinarith
        exact mul_le_mul_of_nonneg_left hL this
    have e2 : (t₁ : ℝ) ≤ 2 * D + 2 * ((Fintype.card V : ℝ) - 1) / k + (D : ℝ) * (D - 1) * (m + 2) := by
      rw [← mul_le_mul_iff_of_pos_left hkR]
      have : (k : ℝ) * (2 * D + 2 * ((Fintype.card V : ℝ) - 1) / k + (D : ℝ) * (D - 1) * (m + 2)) =
          k * (2 * D) + 2 * ((Fintype.card V : ℝ) - 1) + (D : ℝ) * (D - 1) * (k * (m + 2)) := by
        field_simp
      rw [this]; linarith
    have e3 : 2 * (D : ℝ) ≤ (D : ℝ) * (m + 2) + 2 / k := by
      have : (0 : ℝ) ≤ 2 / k := by positivity
      have : (0 : ℝ) ≤ (D : ℝ) * m := mul_nonneg (Nat.cast_nonneg _) hm
      nlinarith
    have : 2 * ((Fintype.card V : ℝ) - 1) / k = 2 * (Fintype.card V : ℝ) / k - 2 / k := by ring
    simp only [B]
    nlinarith
  -- conclude
  by_contra hcon
  push Not at hcon
  set N := ⌊B⌋₊ + 1
  have := key N (fun t ht h => by
    have := hcon t h
    have : (t : ℝ) ≤ ⌊B⌋₊ := by exact_mod_cast Nat.lt_succ_iff.1 ht
    have hB : (⌊B⌋₊ : ℝ) ≤ B := Nat.floor_le (by positivity)
    linarith)
  have := Nat.lt_floor_add_one B
  simp only [N] at *
  push_cast at *
  linarith

end Podc.TreeExplorationBFDN
