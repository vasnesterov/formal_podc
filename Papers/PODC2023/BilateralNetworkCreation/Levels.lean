import Papers.PODC2023.BilateralNetworkCreation.Model
import Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree

/-!
# Distance cost in graphs of maximum degree two

In a connected graph of maximum degree `≤ 2`, a vertex `w` of degree `c` has at most `c` vertices
at each distance `i ≥ 1`, hence `dist(w) ≥ ∑_{i<n} (n - 1 - c·i)`. For `c = 2` this is `⌊n²/4⌋`
(the distance cost in the cycle `C_n`), for `c = 1` it is `n(n-1)/2` (the end of a path).
-/

-- CSLib candidate (the whole file is general graph theory)
namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {H : SimpleGraph V}

/-- Number of vertices at distance exactly `i` from `w`, in a connected graph of maximum degree
`≤ 2`, is at most `deg w` (for `i ≥ 1`). -/
lemma card_level_le [DecidableEq V] (hH : H.Connected) (hdeg : ∀ x, deg H x ≤ 2) (w : V) :
    ∀ i, 1 ≤ i → (univ.filter fun v => H.dist w v = i).card ≤ deg H w := by
  classical
  intro i hi
  induction i, hi using Nat.le_induction with
  | base =>
    have : (univ.filter fun v => H.dist w v = 1) = (H.neighborSet w).toFinset := by
      ext v; simp [dist_eq_one_iff_adj]
    rw [this, deg, Set.ncard_eq_toFinset_card']
  | succ i hi ih =>
    refine le_trans ?_ ih
    -- predecessor map
    have hpred : ∀ v, v ≠ w → ∃ y, H.Adj v y ∧ H.dist w y + 1 = H.dist w v :=
      fun v hv => hH.exists_adj_dist_succ w hv
    classical
    let pred : V → V := fun v => if hv : v ≠ w then (hpred v hv).choose else v
    have hpred_spec : ∀ v, v ≠ w → H.Adj v (pred v) ∧ H.dist w (pred v) + 1 = H.dist w v := by
      intro v hv; simp only [pred, dif_pos hv]; exact (hpred v hv).choose_spec
    refine Finset.card_le_card_of_injOn pred ?_ ?_
    · intro v hv
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hv ⊢
      have hvw : v ≠ w := by rintro rfl; simp at hv
      have := (hpred_spec v hvw).2; omega
    · intro v hv v' hv' heq
      simp only [coe_filter, Set.mem_setOf_eq, mem_univ, true_and] at hv hv'
      by_contra hne
      have hvw : v ≠ w := by rintro rfl; simp at hv
      have hv'w : v' ≠ w := by rintro rfl; simp at hv'
      have hz : H.dist w (pred v) = i := by have := (hpred_spec v hvw).2; omega
      have hzw : pred v ≠ w := by intro h; rw [h] at hz; simp at hz; omega
      obtain ⟨hzz, hz'⟩ := hpred_spec (pred v) hzw
      have h1 : H.Adj (pred v) v := (hpred_spec v hvw).1.symm
      have h2 : H.Adj (pred v) v' := by rw [heq]; exact (hpred_spec v' hv'w).1.symm
      -- three distinct neighbours of `z`
      have hsub : ({v, v', pred (pred v)} : Set V) ⊆ H.neighborSet (pred v) := by
        intro x hx
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
        rcases hx with rfl | rfl | rfl
        · exact h1
        · exact h2
        · exact hzz
      have hc : ({v, v', pred (pred v)} : Set V).ncard = 3 := by
        rw [Set.ncard_eq_three]
        refine ⟨v, v', pred (pred v), hne, ?_, ?_, rfl⟩
        · intro h; rw [← h] at hz'; omega
        · intro h; rw [← h] at hz'; omega
      have := Set.ncard_le_ncard hsub (Set.toFinite _)
      have := hdeg (pred v)
      unfold deg at this
      omega

/-- Balls: at most `1 + deg(w)·i` vertices at distance `≤ i`. -/
lemma card_ball_le [DecidableEq V] (hH : H.Connected) (hdeg : ∀ x, deg H x ≤ 2) (w : V) (i : ℕ) :
    (univ.filter fun v => H.dist w v ≤ i).card ≤ 1 + deg H w * i := by
  induction i with
  | zero =>
    have : (univ.filter fun v => H.dist w v ≤ 0) ⊆ {w} := by
      intro v hv
      simp only [mem_filter, mem_univ, true_and, Nat.le_zero] at hv
      rw [mem_singleton]
      exact ((hH.preconnected w v).dist_eq_zero_iff.1 hv).symm
    simpa using card_le_card this
  | succ i ih =>
    have : (univ.filter fun v => H.dist w v ≤ i + 1) =
        (univ.filter fun v => H.dist w v ≤ i) ∪ (univ.filter fun v => H.dist w v = i + 1) := by
      ext v; simp only [mem_filter, mem_univ, true_and, mem_union]; omega
    rw [this]
    refine (card_union_le _ _).trans ?_
    have := card_level_le hH hdeg w (i + 1) (by omega)
    rw [mul_add, mul_one]; omega

/-- Layer-cake lower bound: `dist(w) ≥ ∑_{i<n} (n - 1 - deg(w)·i)`. -/
theorem distCost_ge_levels {M : ℕ} (hH : H.Connected) (hdeg : ∀ x, deg H x ≤ 2) (w : V) :
    ∑ i ∈ range (Fintype.card V), (Fintype.card V - 1 - deg H w * i) ≤ distCost M H w := by
  classical
  set n := Fintype.card V
  have hd : ∀ v, d M H w v = ((range n).filter fun i => i < H.dist w v).card := by
    intro v
    rw [d_of_reachable (hH w v)]
    have : (range n).filter (fun i => i < H.dist w v) = range (H.dist w v) := by
      ext i; simp only [mem_filter, mem_range]
      have := dist_lt_card (hH w v); omega
    rw [this, card_range]
  unfold distCost
  simp_rw [hd, card_eq_sum_ones, sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← sum_filter, ← card_eq_sum_ones]
  have hc : (univ.filter fun v => i < H.dist w v).card =
      n - (univ.filter fun v => H.dist w v ≤ i).card := by
    rw [← card_compl]; congr 1; ext v; simp
  rw [hc]
  have := card_ball_le hH hdeg w i
  omega

/-! ### The two sums -/

lemma sum_range_sub_one_sub (n : ℕ) : ∑ i ∈ range n, (n - 1 - i) = n * (n - 1) / 2 := by
  rw [Finset.sum_range_reflect (fun i => i) n, Finset.sum_range_id]

lemma sum_range_sub_one_sub_two (n : ℕ) : ∑ i ∈ range n, (n - 1 - 2 * i) = n ^ 2 / 4 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simp
    | 1 => simp
    | m + 2 =>
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      have h : ∀ j ∈ range m, (m + 2 - 1 - 2 * (j + 1)) = (m - 1 - 2 * j) := by
        intro j _; omega
      rw [Finset.sum_congr rfl h, ih m (by omega)]
      have : (m + 2) ^ 2 = m ^ 2 + 4 * (m + 1) := by ring
      rw [this]
      omega

lemma sum_range_sub_one (n : ℕ) : ∑ i ∈ range n, (n - 1 - 0 * i) = n * (n - 1) := by
  simp [mul_comm]

/-- Max degree `≤ 2`, connected, `deg w = 2`: `dist(w) ≥ ⌊n²/4⌋`. -/
theorem distCost_ge_deg_two {M : ℕ} (hH : H.Connected) (hdeg : ∀ x, deg H x ≤ 2) (w : V)
    (hw : deg H w = 2) : Fintype.card V ^ 2 / 4 ≤ distCost M H w := by
  have := distCost_ge_levels (M := M) hH hdeg w
  rwa [hw, sum_range_sub_one_sub_two] at this

/-- Max degree `≤ 2`, connected, `deg w ≤ 1`: `dist(w) ≥ n(n-1)/2`. -/
theorem distCost_ge_deg_le_one {M : ℕ} (hH : H.Connected) (hdeg : ∀ x, deg H x ≤ 2) (w : V)
    (hw : deg H w ≤ 1) : Fintype.card V * (Fintype.card V - 1) / 2 ≤ distCost M H w := by
  have := distCost_ge_levels (M := M) hH hdeg w
  rw [← sum_range_sub_one_sub]
  refine le_trans (Finset.sum_le_sum fun i _ => ?_) this
  have : deg H w * i ≤ i := by
    calc deg H w * i ≤ 1 * i := Nat.mul_le_mul_right _ hw
      _ = i := one_mul i
  omega

end Podc.BilateralNetworkCreation
