import Papers.PODC2023.TreeExplorationBFDN.Main

/-!
# Proposition 4.2: adversarial break-downs

Cosson, Massoulié, Viennot, PODC 2023, Section 4.2, Proposition 4.2 (full version
arXiv:2301.13307, Section 4.2, Proposition 6).

At every round `t` an adversary chooses the set `act t` of robots allowed to move
(`M^i_t = 1` iff `i ∈ act t`); blocked robots neither take part in the decisions of the round nor
move. `A(M) = (1/k) ∑_t ∑_i M^i_t ∈ ℕ ∪ {∞}` is the average number of allowed moves. If
`A(M) ≥ 2n/k + D² (log k + 2)`, all edges are visited (equivalently, since edges are identified
with their lower endpoints, all nodes are visited).
-/

set_option linter.unusedSectionVars false

namespace Podc.TreeExplorationBFDN

open Finset SimpleGraph
open scoped ENNReal

variable {V : Type*} {G : SimpleGraph V} {T : G.RootedTree} {k : ℕ} [Fintype V] [DecidableEq V]

/-- Before the tree is explored, each round contributes at most its moves, except one round
(the round in which the last dangling edges at the root are taken) where up to `k` allowed
robots may stay idle. -/
theorem sum_card_act_le {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k} (he : IsExec T act e)
    (t₁ : ℕ) (hnv : ∀ t < t₁, (e t).vis ≠ univ) :
    ∑ t ∈ range t₁, (act t).card ≤ k + ∑ t ∈ range t₁, (movedSet e t).card := by
  classical
  set SB := (range t₁).filter fun t => IsOpen T (e t) T.root ∧ ¬ IsOpen T (e (t + 1)) T.root
  have hSB : SB.card ≤ 1 := by
    rw [card_le_one]
    intro a ha b hb
    simp only [SB, mem_filter, mem_range] at ha hb
    by_contra hab
    rcases lt_or_gt_of_ne hab with h | h
    · exact he.not_open_mono h (he.inv _).root_vis ha.2.2 hb.2.1
    · exact he.not_open_mono h (he.inv _).root_vis hb.2.2 ha.2.1
  have hround : ∀ t ∈ range t₁, (act t).card ≤ k * (if t ∈ SB then 1 else 0) + (movedSet e t).card := by
    intro t ht
    split_ifs with hs
    · rw [mul_one]; exact (card_le_univ _).trans (by simp)
    · rw [mul_zero, zero_add]
      apply card_le_card
      intro i hi
      simp only [movedSet, mem_filter, mem_univ, true_and]
      intro hst
      rcases he.idle_cases hi hst with h | h
      · exact hnv t (mem_range.1 ht) (vis_eq_univ_of_no_open (he.inv t) h)
      · exact hs (mem_filter.2 ⟨ht, h⟩)
  calc ∑ t ∈ range t₁, (act t).card
      ≤ ∑ t ∈ range t₁, (k * (if t ∈ SB then 1 else 0) + (movedSet e t).card) := sum_le_sum hround
    _ = k * SB.card + ∑ t ∈ range t₁, (movedSet e t).card := by
        rw [sum_add_distrib, ← mul_sum, sum_boole]
        have : (range t₁).filter (fun x => x ∈ SB) = SB := by
          ext t; simp only [SB, mem_filter]; tauto
        rw [this]; simp
    _ ≤ k + ∑ t ∈ range t₁, (movedSet e t).card := by
        have := Nat.mul_le_mul_left k hSB; omega

/-- **Proposition 4.2** of [CMV23]: for any pattern of break-downs `M` (here `act t`, the robots
allowed to move in round `t`) with `A(M) ≥ 2n/k + D² (log k + 2)`, BFDN (where only the robots
allowed to move take part in each round) visits all edges of the tree. -/
theorem proposition_4_2 (hk : 0 < k) {act : ℕ → Finset (Fin k)} {e : ℕ → Config V k}
    (he : IsExec T act e)
    (hA : ENNReal.ofReal (2 * (Fintype.card V : ℝ) / k +
        (maxDepth T : ℝ) ^ 2 * (Real.log k + 2)) ≤ (∑' t, ((act t).card : ℝ≥0∞)) / k) :
    ∃ t, (e t).vis = univ := by
  classical
  by_contra hcon
  push Not at hcon
  set D := maxDepth T
  set n := Fintype.card V
  set L := urnSum k (k + 1)
  have hL : (L : ℝ) ≤ k * (Real.log k + 2) := by
    have := urnSum_le k (k + 1)
    have hmin : min (Real.log ((k + 1 : ℕ) : ℝ)) (Real.log k) = Real.log k :=
      min_eq_right (Real.log_le_log (by exact_mod_cast hk) (by push_cast; linarith))
    rw [hmin] at this; exact this
  -- the depth is positive (otherwise the tree is a single node, visited at time 0)
  have hD : 1 ≤ D := by
    by_contra h0
    apply hcon 0
    rw [he.1, eq_univ_iff_forall]; intro x
    have : x = T.root := RootedTree.depth_eq_zero_iff.1 (by have := depth_le_maxDepth (T := T) x; omega)
    simp [init, this]
  set C : ℕ := k + (2 * (n - 1) + D * (D - 1) * L)
  have hbound : ∀ t₁, ∑ t ∈ range t₁, (act t).card ≤ C := by
    intro t₁
    have h1 := sum_card_act_le he t₁ (fun t _ => hcon t)
    have h2 := sum_moved_le he t₁
    have hvis : (e t₁).vis.card ≤ n := card_le_univ _
    have hAD : ∑ t ∈ range t₁, assignDepth T act e t ≤ (∑ d ∈ range D, d) * L := by
      calc ∑ t ∈ range t₁, assignDepth T act e t
          ≤ ∑ t ∈ range t₁, ∑ d ∈ range D, d * assignCount T act e d t :=
            sum_le_sum fun t _ => assignDepth_le he t
        _ = ∑ d ∈ range D, d * ∑ t ∈ range t₁, assignCount T act e d t := by
            rw [sum_comm]; simp_rw [mul_sum]
        _ ≤ ∑ d ∈ range D, d * L := by
            apply sum_le_sum; intro d _
            rcases Nat.eq_zero_or_pos d with rfl | hd
            · simp
            · exact Nat.mul_le_mul_left d (sum_assignCount_le_k he hd t₁)
        _ = (∑ d ∈ range D, d) * L := by rw [sum_mul]
    have hsum := sum_range_id_mul_two D
    have : 2 * ((∑ d ∈ range D, d) * L) = D * (D - 1) * L := by rw [← hsum]; ring
    omega
  have htsum : (∑' t, ((act t).card : ℝ≥0∞)) ≤ C := by
    apply ENNReal.tsum_le_of_sum_range_le
    intro t₁; exact_mod_cast hbound t₁
  have hkR : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have h2 : ENNReal.ofReal (2 * (n : ℝ) / k + (D : ℝ) ^ 2 * (Real.log k + 2)) ≤
      ENNReal.ofReal ((C : ℝ) / k) := by
    refine hA.trans ?_
    rw [ENNReal.ofReal_div_of_pos hkR, ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
    exact ENNReal.div_le_div_right htsum _
  rw [ENNReal.ofReal_le_ofReal_iff (by positivity)] at h2
  rw [le_div_iff₀ hkR] at h2
  have hn1 : 1 ≤ n := Fintype.card_pos_iff.2 ⟨T.root⟩
  have hCR : (C : ℝ) = k + 2 * ((n : ℝ) - 1) + (D : ℝ) * (D - 1) * L := by
    simp only [C]; push_cast [Nat.cast_sub hn1, Nat.cast_sub hD]; ring
  rw [hCR] at h2
  have hDR : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hlog : 0 ≤ Real.log k := Real.log_natCast_nonneg k
  have hDD : (0 : ℝ) ≤ (D : ℝ) * (D - 1) := by nlinarith
  have := mul_le_mul_of_nonneg_left hL hDD
  have hexp : (2 * (n : ℝ) / k + (D : ℝ) ^ 2 * (Real.log k + 2)) * k =
      2 * n + (D : ℝ) ^ 2 * (k * (Real.log k + 2)) := by field_simp
  rw [hexp] at h2
  nlinarith [mul_pos hkR (by linarith : (0:ℝ) < Real.log k + 2)]

end Podc.TreeExplorationBFDN
