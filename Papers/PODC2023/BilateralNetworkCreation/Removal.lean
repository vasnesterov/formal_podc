import Papers.PODC2023.BilateralNetworkCreation.Model
import Cslib.Foundations.Combinatorics.SimpleGraph.BFSTree

/-!
# Remove Equilibria: Lemma B.1, Proposition 3.1 and Corollary 3.2

* `RE.cost_le_delAt`: in a Remove Equilibrium no agent improves by removing *any set* of incident
  edges (the paper uses this via Proposition A.2, "RE = NE in the BNCG"). The reason is that
  a shortest path from `v` uses only one edge at `v`, so removal costs are superadditive.
* `lemma_B1`: `cost(G) ≤ 2(n-1)(α + dist(u))` for connected `G` in RE (BFS-tree argument).
* `prop_3_1`, `cor_3_2`: `ρ(G) ≤ (α + dist(u))/(α + n - 1) ≤ 1 + n²/α`.
-/

namespace Podc.BilateralNetworkCreation

open SimpleGraph Finset

variable {V : Type*} [Fintype V] {α : ℝ} {M : ℕ} {G : SimpleGraph V}

/-- `G` without the edges between `v` and the agents of `R`. -/
def delAt (G : SimpleGraph V) (v : V) (R : Finset V) : SimpleGraph V :=
  G.deleteEdges {e | ∃ x ∈ R, e = s(v, x)}

lemma delAt_le (v : V) (R : Finset V) : delAt G v R ≤ G := deleteEdges_le _

lemma delAt_le_deleteEdges {v x : V} {R : Finset V} (hx : x ∈ R) :
    delAt G v R ≤ G.deleteEdges {s(v, x)} := by
  intro a b h
  simp only [delAt, deleteEdges_adj, Set.mem_setOf_eq, Set.mem_singleton_iff] at h ⊢
  exact ⟨h.1, fun he => h.2 ⟨x, hx, he⟩⟩

/-- A path starting at `v` contains at most one edge at `v`. -/
lemma isPath_eq_of_mem_edges_start {v w x y : V} {p : G.Walk v w} (hp : p.IsPath)
    (hx : s(v, x) ∈ p.edges) (hy : s(v, y) ∈ p.edges) : x = y := by
  cases p with
  | nil => simp at hx
  | @cons _ a _ h q =>
    rw [Walk.cons_isPath_iff] at hp
    have key : ∀ z, s(v, z) ∈ (Walk.cons h q).edges → z = a := by
      intro z hz
      rw [Walk.edges_cons, List.mem_cons] at hz
      rcases hz with hz | hz
      · rcases Sym2.eq_iff.1 hz with ⟨-, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact h2.trans h1
      · exact absurd (Walk.fst_mem_support_of_mem_edges q hz) hp.2
    rw [key x hx, key y hy]

/-- Superadditivity of the distance increase when removing edges at `v` (for one target `w`). -/
lemma sum_d_delete_le (hM : Fintype.card V ≤ M) (v w : V) (R : Finset V) :
    ∑ x ∈ R, ((d M (G.deleteEdges {s(v, x)}) v w : ℤ) - d M G v w) ≤
      (d M (delAt G v R) v w : ℤ) - d M G v w := by
  classical
  have hR0 : (0 : ℤ) ≤ (d M (delAt G v R) v w : ℤ) - d M G v w := by
    have := d_anti (u := v) (v := w) (delAt_le (G := G) v R) hM; omega
  by_cases hr : G.Reachable v w
  · obtain ⟨p, hp, hl⟩ := hr.exists_path_of_dist
    -- terms with `s(v,x) ∉ p.edges` are `≤ 0`
    have hneg : ∀ x ∈ R, s(v, x) ∉ p.edges →
        ((d M (G.deleteEdges {s(v, x)}) v w : ℤ) - d M G v w) ≤ 0 := by
      intro x _ hx
      have := d_le_of_walk (M := M) (p.toDeleteEdge _ hx)
      rw [Walk.length_transfer, hl, ← d_of_reachable (M := M) hr] at this
      omega
    by_cases hex : ∃ x0 ∈ R, s(v, x0) ∈ p.edges
    · obtain ⟨x0, hx0R, hx0⟩ := hex
      rw [← Finset.add_sum_erase R _ hx0R]
      have hrest : ∑ x ∈ R.erase x0, ((d M (G.deleteEdges {s(v, x)}) v w : ℤ) - d M G v w) ≤ 0 :=
        Finset.sum_nonpos fun x hx => by
          rw [Finset.mem_erase] at hx
          exact hneg x hx.2 fun h => hx.1 (isPath_eq_of_mem_edges_start hp h hx0)
      have h0 := d_anti (u := v) (v := w) (delAt_le_deleteEdges (G := G) (v := v) hx0R) hM
      omega
    · push Not at hex
      exact (Finset.sum_nonpos fun x hx => hneg x hx (hex x hx)).trans hR0
  · -- unreachable: all distances are `M`
    have hz : ∀ x ∈ R, ((d M (G.deleteEdges {s(v, x)}) v w : ℤ) - d M G v w) = 0 := by
      intro x _
      rw [d_of_not_reachable hr,
        d_of_not_reachable fun h => hr (h.mono (deleteEdges_le _))]; simp
    rw [Finset.sum_eq_zero hz]; exact hR0

lemma neighborSet_delAt (v : V) (R : Finset V) :
    (delAt G v R).neighborSet v = G.neighborSet v \ (R : Set V) := by
  ext x
  simp only [mem_neighborSet, delAt, deleteEdges_adj, Set.mem_setOf_eq, Set.mem_diff,
    Finset.mem_coe]
  constructor
  · rintro ⟨h, hn⟩; exact ⟨h, fun hx => hn ⟨x, hx, rfl⟩⟩
  · rintro ⟨h, hn⟩
    refine ⟨h, ?_⟩
    rintro ⟨y, hy, he⟩
    have : x = y := by
      rcases Sym2.eq_iff.1 he with ⟨-, h2⟩ | ⟨h1, h2⟩
      · exact h2
      · exact h2.trans h1
    exact hn (this ▸ hy)

lemma deg_delAt {v : V} {R : Finset V} (hR : ∀ x ∈ R, G.Adj v x) :
    (deg (delAt G v R) v : ℝ) = deg G v - R.card := by
  unfold deg
  have hsub : (R : Set V) ⊆ G.neighborSet v := fun x hx => hR x hx
  rw [neighborSet_delAt, Set.ncard_diff hsub (Set.toFinite _)]
  rw [Nat.cast_sub (Set.ncard_le_ncard hsub (Set.toFinite _))]
  simp

lemma deg_deleteEdges_single {v x : V} (h : G.Adj v x) :
    (deg (G.deleteEdges {s(v, x)}) v : ℝ) = deg G v - 1 := by
  have : G.deleteEdges {s(v, x)} = delAt G v {x} := by
    unfold delAt; congr 1; ext e; simp
  rw [this, deg_delAt (by simpa using h)]; simp

/-- In a Remove Equilibrium no agent improves by removing any set of incident edges. -/
theorem RE.cost_le_delAt (hRE : RE α M G) (hM : Fintype.card V ≤ M) {v : V} {R : Finset V}
    (hR : ∀ x ∈ R, G.Adj v x) : cost α M G v ≤ cost α M (delAt G v R) v := by
  have hsum : ∑ x ∈ R, ((distCost M (G.deleteEdges {s(v, x)}) v : ℤ) - distCost M G v) ≤
      (distCost M (delAt G v R) v : ℤ) - distCost M G v := by
    unfold distCost; push_cast
    simp_rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_comm]
    exact Finset.sum_le_sum fun w _ => sum_d_delete_le hM v w R
  have hsumR : ∑ x ∈ R, ((distCost M (G.deleteEdges {s(v, x)}) v : ℝ) - distCost M G v) ≤
      (distCost M (delAt G v R) v : ℝ) - distCost M G v := by exact_mod_cast hsum
  have hsingle : ∀ x ∈ R, α ≤ (distCost M (G.deleteEdges {s(v, x)}) v : ℝ) - distCost M G v := by
    intro x hx
    have := hRE v x (hR x hx)
    unfold cost at this
    rw [deg_deleteEdges_single (hR x hx)] at this
    linarith
  have := Finset.sum_le_sum hsingle
  rw [Finset.sum_const, nsmul_eq_mul] at this
  unfold cost
  rw [deg_delAt hR]
  linarith

/-! ### Lemma B.1 -/

/-- Walking up the BFS tree towards the root `u`, inside any graph containing the tree edges. -/
lemma exists_walk_up (hG : G.Connected) (u : V) (H : SimpleGraph V)
    (hH : ∀ y, y ≠ u → H.Adj y (G.bfsParent u y)) :
    ∀ y, ∃ q : H.Walk y u, q.length = G.dist u y := by
  intro y
  induction h : G.dist u y using Nat.strong_induction_on generalizing y with
  | _ k ih =>
    by_cases hy : y = u
    · subst hy; refine ⟨Walk.nil, ?_⟩; simp at h ⊢; omega
    · have hr : G.Reachable u y := hG u y
      have h1 := hr.dist_bfsParent_add_one hy
      obtain ⟨q, hq⟩ := ih (G.dist u (G.bfsParent u y)) (by omega) _ rfl
      exact ⟨Walk.cons (hH y hy) q, by simp [hq]; omega⟩

/-- Lemma B.1: for connected `G` in RE and any agent `u`, `cost(G) ≤ 2(n-1)(α + dist(u))`. -/
theorem lemma_B1 (hα : 0 ≤ α) (hM : Fintype.card V ≤ M) (hG : G.Connected) (hRE : RE α M G)
    (u : V) :
    socialCost α M G ≤ 2 * ((Fintype.card V : ℝ) - 1) * (α + distCost M G u) := by
  classical
  set n := Fintype.card V
  set p := G.bfsParent u
  set ℓ : V → ℕ := fun y => G.dist u y with hℓ
  -- kept neighbours of `v`: its parent and its children
  let K : V → Finset V := fun v =>
    (if v = u then ∅ else {p v}) ∪ Finset.univ.filter (fun x => x ≠ u ∧ p x = v)
  let R : V → Finset V := fun v => (G.neighborFinset v).filter (fun x => x ∉ K v)
  have hRadj : ∀ v, ∀ x ∈ R v, G.Adj v x := fun v x hx => by
    simp only [R, Finset.mem_filter, mem_neighborFinset] at hx; exact hx.1
  -- tree edges survive in `delAt G v (R v)`
  have htree : ∀ v y, y ≠ u → (delAt G v (R v)).Adj y (p y) := by
    intro v y hy
    simp only [delAt, deleteEdges_adj, Set.mem_setOf_eq]
    refine ⟨(hG u y).adj_bfsParent hy, ?_⟩
    rintro ⟨x, hx, he⟩
    simp only [R, Finset.mem_filter] at hx
    apply hx.2
    rcases Sym2.eq_iff.1 he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2
      simp [K, hy]
    · subst h1; subst h2
      simp [K, hy]
  -- per-agent bound
  have hper : ∀ v, cost α M G v ≤
      α * (K v).card + ∑ w, (if w = v then 0 else ((ℓ v : ℝ) + ℓ w)) := by
    intro v
    refine (hRE.cost_le_delAt hM (hRadj v)).trans ?_
    unfold cost
    gcongr
    · -- degree
      unfold deg
      rw [neighborSet_delAt]
      calc (G.neighborSet v \ ↑(R v)).ncard ≤ ((K v : Set V)).ncard := by
            refine Set.ncard_le_ncard ?_ (Set.toFinite _)
            intro x ⟨hx, hxR⟩
            by_contra hK
            apply hxR
            simp only [R, Finset.coe_filter, Set.mem_setOf_eq, mem_neighborFinset]
            exact ⟨hx, fun h => hK (Finset.mem_coe.2 h)⟩
        _ = (K v).card := by rw [Set.ncard_coe_finset]
    · -- distances
      unfold distCost; push_cast
      gcongr with w
      by_cases hw : w = v
      · subst hw; simp
      · rw [if_neg hw]
        obtain ⟨q1, hq1⟩ := exists_walk_up hG u _ (htree v) v
        obtain ⟨q2, hq2⟩ := exists_walk_up hG u _ (htree v) w
        have := d_le_of_walk (M := M) (q1.append q2.reverse)
        rw [Walk.length_append, Walk.length_reverse, hq1, hq2] at this
        exact_mod_cast this
  -- summing up
  have hK : ∑ v, ((K v).card : ℝ) ≤ 2 * ((n : ℝ) - 1) := by
    have h1 : ∀ v, ((K v).card : ℝ) ≤ (if v = u then 0 else 1) +
        (Finset.univ.filter (fun x => x ≠ u ∧ p x = v)).card := by
      intro v
      have := Finset.card_union_le (if v = u then ∅ else {p v})
        (Finset.univ.filter (fun x => x ≠ u ∧ p x = v))
      have h' : (((if v = u then (∅ : Finset V) else {p v}).card : ℕ) : ℝ) =
          if v = u then 0 else 1 := by split_ifs <;> simp
      calc ((K v).card : ℝ) ≤ (((if v = u then (∅ : Finset V) else {p v}).card : ℕ) : ℝ) +
            (Finset.univ.filter (fun x => x ≠ u ∧ p x = v)).card := by exact_mod_cast this
        _ = _ := by rw [h']
    refine (Finset.sum_le_sum fun v _ => h1 v).trans ?_
    rw [Finset.sum_add_distrib]
    have h2 : ∑ v, ((if v = u then 0 else 1 : ℝ)) = n - 1 := by
      rw [Finset.sum_ite, Finset.sum_const_zero, Finset.sum_const, zero_add, nsmul_eq_mul,
        mul_one, Finset.filter_ne' Finset.univ u, Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ]
      have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨u⟩
      rw [Nat.cast_sub this, Nat.cast_one]
    have h3 : ∑ v, ((Finset.univ.filter (fun x => x ≠ u ∧ p x = v)).card : ℝ) = n - 1 := by
      have : ∑ v, (Finset.univ.filter (fun x => x ≠ u ∧ p x = v)).card =
          (Finset.univ.filter (fun x => x ≠ u)).card := by
        rw [Finset.card_eq_sum_card_fiberwise (f := p) (t := Finset.univ) (by simp)]
        congr 1; ext v; congr 1; ext x; simp [and_comm]
      rw [← Nat.cast_sum, this, Finset.filter_ne' Finset.univ u,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
      have : 1 ≤ Fintype.card V := Fintype.card_pos_iff.2 ⟨u⟩
      rw [Nat.cast_sub this, Nat.cast_one]
    rw [h2, h3]; linarith
  have hD : (distCost M G u : ℝ) = ∑ w, (ℓ w : ℝ) := by
    unfold distCost; push_cast
    exact Finset.sum_congr rfl fun w _ => by rw [d_of_reachable (hG u w)]
  have hdist : ∀ v, ∑ w, (if w = v then 0 else ((ℓ v : ℝ) + ℓ w)) =
      n * ℓ v + (distCost M G u : ℝ) - 2 * ℓ v := by
    intro v
    rw [hD, ← Finset.add_sum_erase _ _ (Finset.mem_univ v), if_pos rfl, zero_add]
    have : ∑ w, ((ℓ v : ℝ) + ℓ w) = (ℓ v + ℓ v) + ∑ w ∈ Finset.univ.erase v, ((ℓ v : ℝ) + ℓ w) :=
      (Finset.add_sum_erase _ _ (Finset.mem_univ v)).symm
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    rw [Finset.sum_congr rfl fun w hw => if_neg (Finset.ne_of_mem_erase hw)]
    linarith
  unfold socialCost
  refine (Finset.sum_le_sum fun v _ => hper v).trans ?_
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  simp_rw [hdist]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hD]
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Fintype.card_pos_iff.2 ⟨u⟩
  nlinarith [mul_le_mul_of_nonneg_left hK hα]

/-- Proposition 3.1: for connected `G` in RE and any agent `u`,
`ρ(G) ≤ (α + dist(u)) / (α + n - 1)` (for `α ≥ 1`, `n ≥ 2`, `M > α n³`). -/
theorem prop_3_1 (hα : 1 ≤ α) (hM : α * (Fintype.card V) ^ 3 < M) (hn : 2 ≤ Fintype.card V)
    (hG : G.Connected) (hRE : RE α M G) (u : V) :
    rho α M G ≤ (α + distCost M G u) / (α + Fintype.card V - 1) := by
  have hcM := card_le_M hα hM
  have hB := lemma_B1 (zero_le_one.trans hα) hcM hG hRE u
  have hO := optCost_ge (V := V) hα hM
  have hn' : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hpos : 0 < 2 * ((Fintype.card V : ℝ) - 1) * (α + Fintype.card V - 1) := by
    have : 0 < (Fintype.card V : ℝ) - 1 := by linarith
    have : 0 < α + Fintype.card V - 1 := by linarith
    positivity
  unfold rho
  rw [div_le_div_iff₀ (hpos.trans_le hO) (by linarith)]
  have h1 : 0 ≤ α + (distCost M G u : ℝ) := by positivity
  calc socialCost α M G * (α + Fintype.card V - 1)
      ≤ 2 * ((Fintype.card V : ℝ) - 1) * (α + distCost M G u) * (α + Fintype.card V - 1) := by
        gcongr; linarith
    _ = (α + distCost M G u) * (2 * ((Fintype.card V : ℝ) - 1) * (α + Fintype.card V - 1)) := by
        ring
    _ ≤ (α + distCost M G u) * optCost α M := by gcongr

/-- Corollary 3.2: for connected `G` in RE, `ρ(G) ≤ 1 + n²/α`. -/
theorem cor_3_2 (hα : 1 ≤ α) (hM : α * (Fintype.card V) ^ 3 < M) (hn : 2 ≤ Fintype.card V)
    (hG : G.Connected) (hRE : RE α M G) :
    rho α M G ≤ 1 + (Fintype.card V : ℝ) ^ 2 / α := by
  have u : V := Classical.choice hG.nonempty
  refine (prop_3_1 hα hM hn hG hRE u).trans ?_
  have hd : (distCost M G u : ℝ) ≤ (Fintype.card V : ℝ) ^ 2 := by
    have : distCost M G u ≤ Fintype.card V * Fintype.card V := by
      unfold distCost
      calc ∑ v, d M G u v ≤ ∑ _v : V, Fintype.card V :=
            Finset.sum_le_sum fun v _ => (d_lt_card_of_reachable (hG u v)).le
        _ = _ := by simp
    rw [sq]; exact_mod_cast this
  have hn' : (2 : ℝ) ≤ Fintype.card V := by exact_mod_cast hn
  have hα0 : 0 < α := by linarith
  calc (α + distCost M G u) / (α + Fintype.card V - 1)
      ≤ (α + (Fintype.card V : ℝ) ^ 2) / (α + Fintype.card V - 1) := by
        gcongr; linarith
    _ ≤ (α + (Fintype.card V : ℝ) ^ 2) / α := by
        gcongr; linarith
    _ = _ := by rw [add_div, div_self hα0.ne']

end Podc.BilateralNetworkCreation
