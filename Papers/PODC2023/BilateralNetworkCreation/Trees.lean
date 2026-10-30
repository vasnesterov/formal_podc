import Papers.PODC2023.BilateralNetworkCreation.TreeMetric
import Papers.PODC2023.BilateralNetworkCreation.Removal

/-!
# Trees in Bilateral Swap Equilibrium (Section 3.2.1)

Throughout, `G` is a tree rooted at a 1-median `r` (a vertex of minimum distance cost, `IsMedian`);
`ℓ(x) = dist(r, x)` and `T_u = sub G r u`.

* `lemma_3_3`: every `T_u` has a `T_u`-1-median `v` with `ℓ(v) ≤ ℓ(u) + 2α/n`;
* `lemma_3_4`: `depth(T_u) ≤ (1 + 2α/n) log |T_u|`;
* `lemma_3_5`: `|T_u| ≤ α / (ℓ(u) - 1)` for `ℓ(u) ≥ 2`;
* `theorem_3_6`: `ρ(G) ≤ 2 + 2 log α` for every tree in BSwE (`α ≥ 1`).
-/

namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {α : ℝ} {M : ℕ}

/-! ### Swaps -/

section Swap

variable {u v w : V}

lemma neighborSet_swap_self (huv : G.Adj u v) (huw : u ≠ w) :
    (swap G u v w).neighborSet u = insert w (G.neighborSet u \ {v}) := by
  ext x
  simp only [swap, mem_neighborSet, sup_adj, deleteEdges_adj, Set.mem_singleton_iff, edge_adj,
    Set.mem_insert_iff, Set.mem_diff]
  constructor
  · rintro (⟨h, hne⟩ | ⟨h1, h2⟩)
    · right; exact ⟨h, fun hx => hne (by rw [hx])⟩
    · rcases h1 with ⟨-, rfl⟩ | ⟨rfl, -⟩
      · left; rfl
      · exact absurd rfl huw
  · rintro (rfl | ⟨h, hx⟩)
    · right; exact ⟨Or.inl ⟨trivial, rfl⟩, huw⟩
    · left; refine ⟨h, fun he => hx ?_⟩
      rcases Sym2.eq_iff.1 he with ⟨-, h'⟩ | ⟨h1, h2⟩
      · exact h'
      · exact h2.trans h1

lemma deg_swap_self (huv : G.Adj u v) (huw : u ≠ w) (hnuw : ¬ G.Adj u w) :
    deg (swap G u v w) u = deg G u := by
  unfold deg
  rw [neighborSet_swap_self huv huw, Set.ncard_insert_of_notMem (by simp [hnuw])
    ((Set.toFinite _).diff)]
  exact Set.ncard_diff_singleton_add_one (s := G.neighborSet u) huv

lemma neighborSet_swap_other (huv : G.Adj u v) (huw : u ≠ w) (hnuw : ¬ G.Adj u w) :
    (swap G u v w).neighborSet w = insert u (G.neighborSet w) := by
  have hwv : w ≠ v := fun h => hnuw (h ▸ huv)
  ext x
  simp only [swap, mem_neighborSet, sup_adj, deleteEdges_adj, Set.mem_singleton_iff, edge_adj,
    Set.mem_insert_iff]
  constructor
  · rintro (⟨h, -⟩ | ⟨h1, -⟩)
    · right; exact h
    · rcases h1 with ⟨rfl, -⟩ | ⟨-, rfl⟩
      · exact absurd rfl huw
      · left; rfl
  · rintro (rfl | h)
    · right; exact ⟨Or.inr ⟨trivial, rfl⟩, huw.symm⟩
    · left; refine ⟨h, fun he => ?_⟩
      rcases Sym2.eq_iff.1 he with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact huw h1.symm
      · exact hwv h1

lemma deg_swap_other (huv : G.Adj u v) (huw : u ≠ w) (hnuw : ¬ G.Adj u w) :
    deg (swap G u v w) w = deg G w + 1 := by
  unfold deg
  rw [neighborSet_swap_other huv huw hnuw, Set.ncard_insert_of_notMem
    (by simpa [mem_neighborSet, adj_comm] using hnuw) (Set.toFinite _)]

lemma deleteEdges_le_swap : G.deleteEdges {s(u, v)} ≤ swap G u v w := le_sup_left

lemma swap_adj_new (huw : u ≠ w) : (swap G u v w).Adj u w := by
  right; simp [edge_adj, huw]

end Swap

/-! ### Sums over a subtree and its complement -/

lemma sum_ite_mem (S : Finset V) (f g : V → ℕ) :
    ∑ x, (if x ∈ S then f x else g x) = ∑ x ∈ S, f x + ∑ x ∈ Sᶜ, g x := by
  rw [Finset.sum_ite]
  congr 1
  · congr 1; ext; simp
  · congr 1; ext; simp

lemma distCost_eq_sum_dist (hG : G.Connected) (u : V) : distCost M G u = ∑ x, G.dist u x :=
  Finset.sum_congr rfl fun x _ => d_of_reachable (hG u x)

/-- `r` is a 1-median: a vertex of minimum distance cost. -/
def IsMedian (G : SimpleGraph V) (r : V) : Prop := ∀ y, ∑ x, G.dist r x ≤ ∑ x, G.dist y x

/-- `v` is a `T_u`-1-median: a vertex of `T_u` minimizing the distance cost within `T_u`. -/
def IsSubMedian (G : SimpleGraph V) (r u v : V) : Prop :=
  v ∈ sub G r u ∧ ∀ y ∈ sub G r u, ∑ x ∈ sub G r u, G.dist v x ≤ ∑ x ∈ sub G r u, G.dist y x

lemma exists_median (G : SimpleGraph V) [Nonempty V] : ∃ r, IsMedian G r := by
  obtain ⟨r, -, hr⟩ := Finset.exists_min_image univ (fun y => ∑ x, G.dist y x) univ_nonempty
  exact ⟨r, fun y => hr y (mem_univ y)⟩

variable (hT : G.IsTree) {r : V}
include hT

/-- The child subtrees of a 1-median have at most `n/2` vertices. -/
lemma two_mul_card_sub_le (hr : IsMedian G r) {u : V} (hu : u ≠ r) :
    2 * (sub G r u).card ≤ Fintype.card V := by
  have hG := hT.connected
  have hl : 1 ≤ G.dist r u := Nat.one_le_iff_ne_zero.2 fun h =>
    hu ((hG.preconnected r u).dist_eq_zero_iff.1 h).symm
  obtain ⟨a, -, hla, hua⟩ := exists_anc hG (u := r) (x := u) (by rw [sub_root]; exact mem_univ _) 1
    (by simp) hl
  have hadj : G.Adj a r := by
    rw [← dist_eq_one_iff_adj, dist_comm]; exact hla
  have hm := sum_move (r := r) hT hadj (by simp [hla]) univ
  have h1 := hr a
  have h2 := Finset.card_filter_add_card_filter_not (s := univ) (· ∈ sub G r a)
  have h3 : (univ.filter (· ∈ sub G r a)) = sub G r a := by ext; simp
  rw [h3] at hm h2
  have h4 := card_le_card (sub_subset hG hua)
  rw [card_univ] at h2
  omega

/-- Lemma 3.3: in a tree in BSwE rooted at a 1-median `r`, every subtree `T_u` has a
`T_u`-1-median `v` with `ℓ(v) ≤ ℓ(u) + 2α/n`. -/
theorem lemma_3_3 (hα : 0 ≤ α) (hM : Fintype.card V ≤ M) (hr : IsMedian G r)
    (hB : BSwE α M G) (u : V) :
    ∃ v, IsSubMedian G r u v ∧
      (G.dist r v : ℝ) ≤ G.dist r u + 2 * α / Fintype.card V := by
  have hG := hT.connected
  set S := sub G r u with hS
  set f : V → ℕ := fun y => ∑ x ∈ S, G.dist y x
  obtain ⟨v, hvS, hv⟩ := Finset.exists_min_image S f ⟨u, self_mem_sub⟩
  have hn0 : (0 : ℝ) ≤ 2 * α / Fintype.card V := by positivity
  by_cases hfu : f u ≤ f v
  · exact ⟨u, ⟨self_mem_sub, fun y hy => hfu.trans (hv y hy)⟩, by linarith⟩
  push Not at hfu
  refine ⟨v, ⟨hvS, hv⟩, ?_⟩
  -- `u` is not the root, since the root is a 1-median of the whole tree
  have hur : u ≠ r := by
    rintro rfl
    have := hr v
    simp only [f, hS, sub_root] at hfu
    omega
  have hvu : v ≠ u := by rintro rfl; exact lt_irrefl _ hfu
  obtain ⟨p, hadj, hp⟩ := hG.exists_adj_dist_succ r hur
  have hpS : p ∉ S := parent_not_mem_sub hp
  have hpv : p ≠ v := fun h => hpS (h ▸ hvS)
  have hnpv : ¬ G.Adj p v := fun h => hvu (eq_of_adj_cross hT hadj hp h.symm hvS hpS).1
  set G' := swap G p u v
  have hHG' : G.deleteEdges {s(u, p)} ≤ G' := by
    rw [Sym2.eq_swap]; exact deleteEdges_le_swap
  have hHG : G.deleteEdges {s(u, p)} ≤ G := deleteEdges_le _
  have hreachS : ∀ x ∈ S, ∀ y ∈ S, (G.deleteEdges {s(u, p)}).Reachable x y := fun x hx y hy =>
    (reachable_of_mem_sub hT hadj hp hx).symm.trans (reachable_of_mem_sub hT hadj hp hy)
  have hreachN : ∀ x ∉ S, ∀ y ∉ S, (G.deleteEdges {s(u, p)}).Reachable x y := fun x hx y hy =>
    (reachable_parent_of_not_mem_sub hT hadj hp hx).symm.trans
      (reachable_parent_of_not_mem_sub hT hadj hp hy)
  have hpv' : d M G' p v = 1 := d_eq_one_of_adj (swap_adj_new hpv)
  -- agent `p` strictly improves
  have hp_imp : cost α M G' p < cost α M G p := by
    have hle : distCost M G' p ≤ ∑ x, (if x ∈ S then 1 + G.dist v x else G.dist p x) := by
      unfold distCost
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs with hx
      · have := d_triangle (G := G') (u := p) (v := v) (w := x) hM
        have := d_le_dist_of_reachable hT (M := M) hHG hHG' (hreachS v hvS x hx)
        omega
      · exact d_le_dist_of_reachable hT hHG hHG' (hreachN p hpS x hx)
    have heq : distCost M G p = ∑ x, (if x ∈ S then 1 + G.dist u x else G.dist p x) := by
      rw [distCost_eq_sum_dist hG]
      refine Finset.sum_congr rfl fun x _ => ?_
      split_ifs with hx
      · rw [dist_parent_of_mem hT hadj hp hx]; ring
      · rfl
    rw [sum_ite_mem] at hle heq
    rw [Finset.sum_add_distrib] at hle heq
    have : distCost M G' p < distCost M G p := by
      rw [heq]; simp only [f] at hfu; omega
    unfold cost
    rw [deg_swap_self hadj.symm hpv hnpv]
    have : (distCost M G' p : ℝ) < distCost M G p := by exact_mod_cast this
    linarith
  -- hence `v` does not improve
  have hv_no := hB p u v hadj.symm hpv hnpv hp_imp
  unfold cost at hv_no
  rw [deg_swap_other hadj.symm hpv hnpv] at hv_no
  push_cast at hv_no
  have hle : distCost M G' v ≤ ∑ x, (if x ∈ S then G.dist v x else 1 + G.dist p x) := by
    unfold distCost
    refine Finset.sum_le_sum fun x _ => ?_
    split_ifs with hx
    · exact d_le_dist_of_reachable hT hHG hHG' (hreachS v hvS x hx)
    · have := d_triangle (G := G') (u := v) (v := p) (w := x) hM
      rw [d_comm] at hpv'
      have := d_le_dist_of_reachable hT (M := M) hHG hHG' (hreachN p hpS x hx)
      omega
  have heq : distCost M G v =
      ∑ x, (if x ∈ S then G.dist v x else G.dist v u + (1 + G.dist p x)) := by
    rw [distCost_eq_sum_dist hG]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rfl
    · rw [dist_cross hT hadj hp hvS hx]; ring
  rw [sum_ite_mem, Finset.sum_add_distrib] at heq
  rw [sum_ite_mem] at hle
  rw [Finset.sum_const, smul_eq_mul, card_compl] at heq
  -- `(n - |T_u|) · dist(u,v) ≤ α`
  have key : ((Fintype.card V - S.card : ℕ) : ℝ) * G.dist v u ≤ α := by
    have h1 : (distCost M G v : ℝ) ≤ (∑ x ∈ S, G.dist v x : ℕ) + (∑ x ∈ Sᶜ, (1 + G.dist p x) : ℕ)
        + (Fintype.card V - S.card : ℕ) * G.dist v u := by
      rw [heq]; push_cast; ring_nf; rfl
    have h2 : (distCost M G' v : ℝ) ≤ (∑ x ∈ S, G.dist v x : ℕ) +
        (∑ x ∈ Sᶜ, (1 + G.dist p x) : ℕ) := by exact_mod_cast hle
    have h3 : (distCost M G v : ℝ) = (∑ x ∈ S, G.dist v x : ℕ) +
        (∑ x ∈ Sᶜ, (1 + G.dist p x) : ℕ) + (Fintype.card V - S.card : ℕ) * G.dist v u := by
      rw [heq]; push_cast; ring
    linarith
  have hhalf := two_mul_card_sub_le hT hr hur
  have hdl : (G.dist r v : ℝ) = G.dist r u + G.dist v u := by
    have := (mem_sub.1 hvS); rw [dist_comm (u := v)]; exact_mod_cast this
  have hn : (Fintype.card V : ℝ) ≤ 2 * ((Fintype.card V - S.card : ℕ) : ℝ) := by
    rw [Nat.cast_sub (Finset.card_le_univ S)]
    have : (2 * S.card : ℝ) ≤ Fintype.card V := by exact_mod_cast hhalf
    linarith
  have hnpos : (0 : ℝ) < Fintype.card V := by
    have : 0 < Fintype.card V := Fintype.card_pos_iff.2 ⟨u⟩
    exact_mod_cast this
  rw [hdl, add_le_add_iff_left, le_div_iff₀ hnpos]
  have : (0 : ℝ) ≤ G.dist v u := by positivity
  nlinarith

/-- The key step of Lemma 3.4: below the layer of a `T_u`-1-median `v`, all subtrees of `T_u`
have at most `|T_u|/2` vertices. -/
lemma two_mul_card_sub_le_of_subMedian {u v w : V} (hv : IsSubMedian G r u v)
    (hw : w ∈ sub G r u) (hlw : G.dist r v < G.dist r w) :
    2 * (sub G r w).card ≤ (sub G r u).card := by
  have hG := hT.connected
  obtain ⟨hvS, hmin⟩ := hv
  by_contra hbig
  push Not at hbig
  by_cases hwv : w ∈ sub G r v
  · -- move from `v` down to its child `c` towards `w`
    obtain ⟨c, hcv, hlc, hwc⟩ := exists_anc hG hwv (G.dist r v + 1) (by omega) (by omega)
    have hcS : c ∈ (sub G r u) := sub_trans hG hvS hcv
    have hadj : G.Adj c v := by
      have := mem_sub.1 hcv
      rw [← dist_eq_one_iff_adj, SimpleGraph.dist_comm]; omega
    have hm := sum_move (r := r) hT hadj (by omega) (sub G r u)
    have h2 := Finset.card_filter_add_card_filter_not (s := (sub G r u)) (· ∈ sub G r c)
    have h3 : (sub G r u).filter (· ∈ sub G r c) = sub G r c := by
      ext y; simp only [mem_filter, and_iff_right_iff_imp]; exact fun hy => sub_trans hG hcS hy
    rw [h3] at hm h2
    have h4 := card_le_card (sub_subset hG hwc)
    have := hmin c hcS
    omega
  · -- `w` lies outside `T_v`: move from `v` up to its parent `p'`
    have hvu : v ≠ u := by rintro rfl; exact hwv hw
    have hlv : G.dist r u < G.dist r v := by
      have := mem_sub.1 hvS
      have : G.dist u v ≠ 0 := fun h =>
        hvu (((hG.preconnected u v).dist_eq_zero_iff.1 h).symm)
      omega
    obtain ⟨p', hp'S, hlp', hvp'⟩ := exists_anc hG hvS (G.dist r v - 1) (by omega) (by omega)
    have hadj : G.Adj v p' := by
      have := mem_sub.1 hvp'
      rw [← dist_eq_one_iff_adj, SimpleGraph.dist_comm]; omega
    have hm := sum_move (r := r) hT hadj (by omega) (sub G r u)
    have h2 := Finset.card_filter_add_card_filter_not (s := (sub G r u)) (· ∈ sub G r v)
    have h5 : sub G r w ⊆ (sub G r u).filter (· ∉ sub G r v) := by
      intro y hy
      simp only [mem_filter]
      refine ⟨sub_trans hG hw hy, fun hyv => hwv ?_⟩
      exact mem_sub_of_mem_sub_of_le hT hyv hy hlw.le
    have h4 := card_le_card h5
    have := hmin p' hp'S
    omega

/-- Lemma 3.4: in a tree in BSwE rooted at a 1-median `r`, for every `u`,
`depth(T_u) ≤ (1 + 2α/n) · log₂ |T_u|`. -/
theorem lemma_3_4 (hα : 0 ≤ α) (hM : Fintype.card V ≤ M) (hr : IsMedian G r)
    (hB : BSwE α M G) (u : V) :
    ∀ x ∈ sub G r u, (G.dist r x : ℝ) - G.dist r u ≤
      (1 + 2 * α / Fintype.card V) * Real.logb 2 (sub G r u).card := by
  have hG := hT.connected
  set c : ℝ := 1 + 2 * α / Fintype.card V with hc
  have hc0 : 2 * α / Fintype.card V ≤ c - 1 := by rw [hc]; ring_nf; rfl
  have hc1 : 0 ≤ 2 * α / Fintype.card V := by positivity
  induction h : (sub G r u).card using Nat.strong_induction_on generalizing u with
  | _ k ih =>
    intro x hx
    obtain ⟨v, hv, hlv⟩ := lemma_3_3 hT hα hM hr hB u
    have hvS := hv.1
    have hk1 : 1 ≤ k := h ▸ Finset.card_pos.2 ⟨u, self_mem_sub⟩
    by_cases hxv : G.dist r x ≤ G.dist r v
    · -- shallow nodes
      by_cases hk : k = 1
      · have : x = u := by
          rw [hk, Finset.card_eq_one] at h
          obtain ⟨a, ha⟩ := h
          have h1 := ha ▸ hx; have h2 := ha ▸ (self_mem_sub : u ∈ sub G r u)
          simp only [mem_singleton] at h1 h2; rw [h1, h2]
        subst this; rw [hk]; simp
      · have hlog : 1 ≤ Real.logb 2 k := by
          rw [Real.le_logb_iff_rpow_le (by norm_num) (by positivity)]
          have : (2 : ℝ) ≤ k := by exact_mod_cast (show 2 ≤ k by omega)
          simpa using this
        have : (G.dist r x : ℝ) ≤ G.dist r v := by exact_mod_cast hxv
        nlinarith
    · push Not at hxv
      have hvu : G.dist r u ≤ G.dist r v := layer_le_of_mem_sub hvS
      obtain ⟨w, hwS, hlw, hxw⟩ := exists_anc hG hx (G.dist r v + 1) (by omega) (by omega)
      have hw2 := two_mul_card_sub_le_of_subMedian hT hv hwS (by omega)
      have hw1 : 1 ≤ (sub G r w).card := Finset.card_pos.2 ⟨w, self_mem_sub⟩
      have ihw := ih (sub G r w).card (by omega) w rfl x hxw
      -- `log |T_w| ≤ log |T_u| - 1`
      have hlog : Real.logb 2 (sub G r w).card ≤ Real.logb 2 k - 1 := by
        have h1 : ((sub G r w).card : ℝ) ≤ k / 2 := by
          have : (2 * (sub G r w).card : ℝ) ≤ k := by exact_mod_cast h ▸ hw2
          linarith
        have h2 : (0 : ℝ) < (sub G r w).card := by exact_mod_cast hw1
        calc Real.logb 2 (sub G r w).card ≤ Real.logb 2 (k / 2) :=
              Real.logb_le_logb_of_le (by norm_num) h2 h1
          _ = Real.logb 2 k - 1 := by
              rw [Real.logb_div (by positivity) (by norm_num), Real.logb_self_eq_one (by norm_num)]
      have hlw' : (G.dist r w : ℝ) = G.dist r v + 1 := by exact_mod_cast hlw
      have hcpos : 0 ≤ c := by linarith
      have := mul_le_mul_of_nonneg_left hlog hcpos
      push_cast at hlv
      nlinarith

/-- Lemma 3.5: in a tree in BSwE rooted at a 1-median `r`, `|T_u| ≤ α / (ℓ(u) - 1)` whenever
`ℓ(u) ≥ 2`. -/
theorem lemma_3_5 (hM : Fintype.card V ≤ M) (hr : IsMedian G r) (hB : BSwE α M G) {u : V}
    (hu : 2 ≤ G.dist r u) : ((sub G r u).card : ℝ) ≤ α / ((G.dist r u : ℝ) - 1) := by
  have hG := hT.connected
  have hL : (0 : ℝ) < (G.dist r u : ℝ) - 1 := by
    have : (2 : ℝ) ≤ G.dist r u := by exact_mod_cast hu
    linarith
  rw [le_div_iff₀ hL]
  by_contra hcon
  push Not at hcon
  set S := sub G r u
  have hur : u ≠ r := by rintro rfl; simp at hu
  obtain ⟨p, hadj, hp⟩ := hG.exists_adj_dist_succ r hur
  obtain ⟨a, -, hla, hua⟩ := exists_anc hG (u := r) (x := u) (by rw [sub_root]; exact mem_univ _) 1
    (by simp) (by omega)
  have hadja : G.Adj a r := by rw [← dist_eq_one_iff_adj, dist_comm]; exact hla
  have hpa : G.dist r r + 1 = G.dist r a := by simp [hla]
  have har : a ≠ r := by rintro rfl; simp at hla
  have hhalf := two_mul_card_sub_le hT hr har
  have hSa : S ⊆ sub G r a := sub_subset hG hua
  have hrS : r ∉ S := by rw [mem_sub]; simp; omega
  have hnadj : ¬ G.Adj u r := by
    intro h; have := dist_eq_one_iff_adj.2 h.symm; omega
  set G' := swap G u p r
  have hHG' : G.deleteEdges {s(u, p)} ≤ G' := deleteEdges_le_swap
  have hHG : G.deleteEdges {s(u, p)} ≤ G := deleteEdges_le _
  have hreachS : ∀ x ∈ S, (G.deleteEdges {s(u, p)}).Reachable u x := fun x hx =>
    reachable_of_mem_sub hT hadj hp hx
  have hreachN : ∀ x ∉ S, ∀ y ∉ S, (G.deleteEdges {s(u, p)}).Reachable x y := fun x hx y hy =>
    (reachable_parent_of_not_mem_sub hT hadj hp hx).symm.trans
      (reachable_parent_of_not_mem_sub hT hadj hp hy)
  have hur' : d M G' u r = 1 := d_eq_one_of_adj (swap_adj_new hur)
  set L : ℕ := G.dist r u - 1
  -- agent `u` strictly improves
  have hu_imp : cost α M G' u < cost α M G u := by
    have hle : distCost M G' u ≤ ∑ x, (if x ∈ S then G.dist u x else 1 + G.dist r x) := by
      unfold distCost
      refine Finset.sum_le_sum fun x _ => ?_
      split_ifs with hx
      · exact d_le_dist_of_reachable hT hHG hHG' (hreachS x hx)
      · have := d_triangle (G := G') (u := u) (v := r) (w := x) hM
        have := d_le_dist_of_reachable hT (M := M) hHG hHG' (hreachN r hrS x hx)
        omega
    -- pointwise comparison with the old distances
    have hpt : ∀ x, (if x ∈ S then G.dist u x else 1 + G.dist r x) + L *
        (if x ∉ sub G r a then 1 else 0) ≤ G.dist u x + L * (if x ∈ sub G r a ∧ x ∉ S then 1 else 0)
        := by
      intro x
      by_cases hxS : x ∈ S
      · have := hSa hxS; simp [hxS, this]
      · by_cases hxa : x ∈ sub G r a
        · simp only [hxS, hxa, if_false, not_false_eq_true, and_self, if_true, not_true_eq_false,
            mul_one, mul_zero, add_zero]
          have h1 := dist_cross hT hadj hp self_mem_sub hxS
          have h2 := hG.dist_triangle (u := r) (v := p) (w := x)
          rw [SimpleGraph.dist_self] at h1
          omega
        · simp only [hxS, hxa, if_false, false_and, not_false_eq_true, if_true, mul_zero, mul_one,
            add_zero]
          have h1 := dist_cross hT hadja hpa hua hxa
          have h2 := mem_sub.1 hua
          rw [SimpleGraph.dist_comm (G := G) (u := a) (v := u)] at h2
          omega
    have hsum := Finset.sum_le_sum fun x (_ : x ∈ univ) => hpt x
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
    simp only [Finset.sum_boole, Nat.cast_id] at hsum
    have hc1 : (univ.filter fun x => x ∈ sub G r a ∧ x ∉ S).card + S.card = (sub G r a).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1; ext x; simp only [mem_union, mem_filter, mem_univ, true_and]
        constructor
        · rintro (⟨h, -⟩ | h); exact h; exact hSa h
        · intro h; by_cases hx : x ∈ S; exact Or.inr hx; exact Or.inl ⟨h, hx⟩
      · rw [Finset.disjoint_left]; intro x hx hx'; simp at hx; exact hx.2 hx'
    have hc2 : (univ.filter fun x => x ∉ sub G r a).card + (sub G r a).card = Fintype.card V := by
      have := Finset.card_filter_add_card_filter_not (s := univ) (· ∉ sub G r a)
      rw [card_univ] at this; rw [← this]; congr 2; ext; simp
    have hS1 : 1 ≤ S.card := Finset.card_pos.2 ⟨u, self_mem_sub⟩
    have hL1 : 1 ≤ L := by omega
    have : distCost M G' u < distCost M G u := by
      rw [distCost_eq_sum_dist hG]
      have : L * (univ.filter fun x => x ∈ sub G r a ∧ x ∉ S).card + L * S.card ≤
          L * (univ.filter fun x => x ∉ sub G r a).card := by
        rw [← mul_add, hc1]; exact Nat.mul_le_mul_left _ (by omega)
      have : L * S.card ≥ 1 := Nat.mul_pos (by omega) hS1
      omega
    unfold cost
    rw [deg_swap_self hadj hur hnadj]
    have : (distCost M G' u : ℝ) < distCost M G u := by exact_mod_cast this
    linarith
  -- hence `r` does not improve, but it gains `L · |T_u| > α`
  have hr_no := hB u p r hadj hur hnadj hu_imp
  unfold cost at hr_no
  rw [deg_swap_other hadj hur hnadj] at hr_no
  push_cast at hr_no
  have hle : distCost M G' r ≤ ∑ x, (if x ∈ S then 1 + G.dist u x else G.dist r x) := by
    unfold distCost
    refine Finset.sum_le_sum fun x _ => ?_
    split_ifs with hx
    · have := d_triangle (G := G') (u := r) (v := u) (w := x) hM
      rw [d_comm] at hur'
      have := d_le_dist_of_reachable hT (M := M) hHG hHG' (hreachS x hx)
      omega
    · exact d_le_dist_of_reachable hT hHG hHG' (hreachN r hrS x hx)
  have heq : distCost M G r = ∑ x, (if x ∈ S then G.dist r u + G.dist u x else G.dist r x) := by
    rw [distCost_eq_sum_dist hG]
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · exact mem_sub.1 hx
    · rfl
  rw [sum_ite_mem, Finset.sum_add_distrib] at hle heq
  rw [Finset.sum_const, smul_eq_mul] at heq
  rw [Finset.sum_const, smul_eq_mul, mul_one] at hle
  have : (distCost M G r : ℝ) ≥ (distCost M G' r : ℝ) + L * S.card := by
    have h1 : (distCost M G r : ℕ) ≥ distCost M G' r + L * S.card := by
      rw [heq]
      have : S.card * G.dist r u = S.card * 1 + L * S.card := by
        rw [mul_comm L]; rw [← mul_add]; congr 1; omega
      omega
    exact_mod_cast h1
  have hLc : ((L : ℕ) : ℝ) = (G.dist r u : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  rw [hLc] at this
  nlinarith

/-- Trees are in Remove Equilibrium (removing an edge disconnects; needs `M ≥ α + 1`). -/
theorem tree_RE (hα : 0 ≤ α) (hM : Fintype.card V ≤ M) (hM' : α + 1 ≤ M) : RE α M G := by
  intro u v huv
  have hnr : ¬ (G.deleteEdges {s(u, v)}).Reachable u v :=
    isBridge_iff.1 (isAcyclic_iff_forall_isBridge.1 hT.isAcyclic ((mem_edgeSet G).2 huv))
  have h1 : distCost M G u + M ≤ distCost M (G.deleteEdges {s(u, v)}) u + 1 := by
    unfold distCost
    rw [← Finset.add_sum_erase _ _ (mem_univ v), ← Finset.add_sum_erase _ _ (mem_univ v),
      d_eq_one_of_adj huv, d_of_not_reachable hnr]
    have := Finset.sum_le_sum fun x (_ : x ∈ univ.erase v) =>
      d_anti (M := M) (u := u) (v := x) (deleteEdges_le (G := G) {s(u, v)}) hM
    omega
  unfold cost
  rw [deg_deleteEdges_single huv]
  have : (distCost M G u : ℝ) + M ≤ distCost M (G.deleteEdges {s(u, v)}) u + 1 := by
    exact_mod_cast h1
  nlinarith

/-- Theorem 3.6: every tree in BSwE has `ρ(G) ≤ 2 + 2 log₂ α` (for `α ≥ 1`, `n ≥ 2`, `M > α n³`). -/
theorem theorem_3_6 (hα : 1 ≤ α) (hM : α * (Fintype.card V) ^ 3 < M)
    (hn : 2 ≤ Fintype.card V) (hB : BSwE α M G) :
    rho α M G ≤ 2 + 2 * Real.logb 2 α := by
  have hG := hT.connected
  have hcM := card_le_M hα hM
  have hn' : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hM' : α + 1 ≤ M := by
    have h8 : (2 : ℝ) ^ 3 ≤ (Fintype.card V : ℝ) ^ 3 := pow_le_pow_left₀ (by norm_num) hn' 3
    have h0 : (0 : ℝ) ≤ α := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h8 h0]
  have hRE := tree_RE hT (by linarith) hcM hM'
  haveI : Nonempty V := hG.nonempty
  obtain ⟨r, hr⟩ := exists_median G
  set n := Fintype.card V
  set Lg := Real.logb 2 α
  have hLg : 0 ≤ Lg := Real.logb_nonneg (by norm_num) hα
  set B : ℝ := 2 + (1 + 2 * α / n) * Lg
  have hc0 : 0 ≤ 2 * α / n := by positivity
  -- every layer is at most `B`
  have hlayer : ∀ x, (G.dist r x : ℝ) ≤ B := by
    intro x
    by_cases hx : G.dist r x ≤ 1
    · have : (G.dist r x : ℝ) ≤ 1 := by exact_mod_cast hx
      have : 0 ≤ (1 + 2 * α / n) * Lg := by positivity
      linarith
    · push Not at hx
      obtain ⟨w, -, hlw, hxw⟩ := exists_anc hG (u := r) (x := x)
        (by rw [sub_root]; exact mem_univ _) 2 (by simp) (by omega)
      have h4 := lemma_3_4 hT (by linarith) hcM hr hB w x hxw
      have h5 := lemma_3_5 hT hcM hr hB (u := w) (by omega)
      rw [hlw] at h5 h4
      norm_num at h5
      have hw1 : (0 : ℝ) < (sub G r w).card := by
        have := Finset.card_pos.2 ⟨w, (self_mem_sub : w ∈ sub G r w)⟩; exact_mod_cast this
      have := Real.logb_le_logb_of_le (b := 2) (by norm_num) hw1 h5
      have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ 1 + 2 * α / n)
      push_cast at h4
      linarith
  -- the distance cost of the root
  have hD : (distCost M G r : ℝ) ≤ (n - 1) * B := by
    rw [distCost_eq_sum_dist hG]
    push_cast
    rw [← Finset.add_sum_erase _ _ (mem_univ r), SimpleGraph.dist_self]
    calc ((0 : ℕ) : ℝ) + ∑ x ∈ univ.erase r, (G.dist r x : ℝ) ≤ ∑ x ∈ univ.erase r, B := by
          simp only [Nat.cast_zero, zero_add]
          exact Finset.sum_le_sum fun x _ => hlayer x
      _ = (n - 1) * B := by
          rw [Finset.sum_const, card_erase_of_mem (mem_univ _), card_univ, nsmul_eq_mul,
            Nat.cast_sub (show 1 ≤ Fintype.card V by omega)]; simp [n]
  refine (prop_3_1 hα hM hn hG hRE r).trans ?_
  rw [div_le_iff₀ (by linarith)]
  have h1 : (n - 1 : ℝ) * (2 * α / n) * Lg ≤ 2 * α * Lg := by
    have : (n - 1 : ℝ) * (2 * α / n) ≤ 2 * α := by
      rw [mul_div_assoc', div_le_iff₀ (by linarith)]; nlinarith
    exact mul_le_mul_of_nonneg_right this hLg
  have : (distCost M G r : ℝ) ≤ (n - 1) * (2 + Lg) + 2 * α * Lg := by
    have : (n - 1 : ℝ) * B = (n - 1) * (2 + Lg) + (n - 1) * (2 * α / n) * Lg := by ring
    linarith
  nlinarith

end Podc.BilateralNetworkCreation
